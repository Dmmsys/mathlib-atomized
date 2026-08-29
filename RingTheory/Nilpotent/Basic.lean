/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.FiniteSupport.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Order.Lattice.Nat
public import Mathlib.RingTheory.Nilpotent.Defs

/-!
# Nilpotent elements

This file develops the basic theory of nilpotent elements. In particular it shows that the
nilpotent elements are closed under many operations.

For the definition of `nilradical`, see `Mathlib/RingTheory/Nilpotent/Lemmas.lean`.


## Main definitions

  * `isNilpotent_neg_iff`
  * `Commute.isNilpotent_add`
  * `Commute.isNilpotent_sub`

-/

public section

universe u v

open Function Set

variable {R S : Type*} {x y : R}

/--
theorem `IsNilpotent.neg` / 定理 `IsNilpotent.neg`

English:
theorem IsNilpotent.neg
  given: [Ring R] (h : IsNilpotent x)
  statement: IsNilpotent (-x)
  proof: by
  obtain ⟨n, hn⟩ := h
  use n
  rw [neg_pow]; rw [hn]; rw [mul_zero]

中文:
定理 是幂零.neg
  条件: [环 R] (h : 是幂零 x)
  结论: 是幂零 (-x)
  证明: by
  obtain ⟨n, hn⟩ := h
  use n
  rw [neg_pow]; rw [hn]; rw [mul_zero]

Depends on / 依赖: mul_zero, neg_pow
-/
theorem IsNilpotent.neg [Ring R] (h : IsNilpotent x) : IsNilpotent (-x) := by
  obtain ⟨n, hn⟩ := h
  use n
  rw [neg_pow]; rw [hn]; rw [mul_zero]

/--
theorem `not_isNilpotent_neg_one` / 定理 `not_isNilpotent_neg_one`

English:
theorem not_isNilpotent_neg_one
  given: [Ring R] [Nontrivial R]
  statement: ¬ IsNilpotent (-1 : R)
  proof: by
  intro h
  simpa [not_isNilpotent_one] using h.neg

中文:
定理 not_isNilpotent_neg_one
  条件: [环 R] [非平凡 R]
  结论: ¬ 是幂零 (-1 : R)
  证明: by
  intro h
  simpa [not_isNilpotent_one] using h.neg

Depends on / 依赖: h.neg, not_isNilpotent_one
-/
theorem not_isNilpotent_neg_one [Ring R] [Nontrivial R] : ¬ IsNilpotent (-1 : R) := by
  intro h
  simpa [not_isNilpotent_one] using h.neg

/--
theorem `neg_one_pow_ne_zero` / 定理 `neg_one_pow_ne_zero`

English:
theorem neg_one_pow_ne_zero
  given: [Ring R] [Nontrivial R] (n : Nat)
  statement: (-1 : R) ^ n != 0
  proof: by
  intro h
  exact not_isNilpotent_neg_one ⟨n, h⟩

@[simp]

中文:
定理 neg_one_pow_ne_zero
  条件: [环 R] [非平凡 R] (n : 自然数)
  结论: (-1 : R) ^ n != 0
  证明: by
  intro h
  exact not_isNilpotent_neg_one ⟨n, h⟩

@[simp]

Depends on / 依赖: not_isNilpotent_neg_one
-/
theorem neg_one_pow_ne_zero [Ring R] [Nontrivial R] (n : Nat) : (-1 : R) ^ n != 0 := by
  intro h
  exact not_isNilpotent_neg_one ⟨n, h⟩

@[simp]
/--
theorem `isNilpotent_neg_iff` / 定理 `isNilpotent_neg_iff`

English:
theorem isNilpotent_neg_iff
  given: [Ring R]
  statement: IsNilpotent (-x) ↔ IsNilpotent x
  proof: ⟨fun h => neg_neg x ▸ h.neg, fun h => h.neg⟩

中文:
定理 isNilpotent_neg_iff
  条件: [环 R]
  结论: 是幂零 (-x) ↔ 是幂零 x
  证明: ⟨fun h => neg_neg x ▸ h.neg, fun h => h.neg⟩

Depends on / 依赖: h.neg, neg_neg
-/
theorem isNilpotent_neg_iff [Ring R] : IsNilpotent (-x) ↔ IsNilpotent x :=
  ⟨fun h => neg_neg x ▸ h.neg, fun h => h.neg⟩

/--
lemma `IsNilpotent.smul` / 引理 `IsNilpotent.smul`

English:
lemma IsNilpotent.smul
  statement: [MonoidWithZero R] [MonoidWithZero S] [MulActionWithZero R S]
  proof: by
  obtain ⟨k, ha⟩ := ha
  use k
  rw [smul_pow]; rw [ha]; rw [smul_zero]

中文:
引理 是幂零.smul
  结论: [带零幺半群 R] [带零幺半群 S] [带零乘法作用 R S]
  证明: by
  obtain ⟨k, ha⟩ := ha
  use k
  rw [smul_pow]; rw [ha]; rw [smul_zero]

Depends on / 依赖: smul_pow, smul_zero
-/
lemma IsNilpotent.smul [MonoidWithZero R] [MonoidWithZero S] [MulActionWithZero R S]
    [SMulCommClass R S S] [IsScalarTower R S S] {a : S} (ha : IsNilpotent a) (t : R) :
    IsNilpotent (t • a) := by
  obtain ⟨k, ha⟩ := ha
  use k
  rw [smul_pow]; rw [ha]; rw [smul_zero]

/--
theorem `IsNilpotent.isUnit_sub_one` / 定理 `IsNilpotent.isUnit_sub_one`

English:
theorem IsNilpotent.isUnit_sub_one
  given: [Ring R] {r : R} (hnil : IsNilpotent r)
  statement: IsUnit (r - 1)
  proof: by
  obtain ⟨n, hn⟩ := hnil
  refine ⟨⟨r - 1, -∑ i in Finset.range n, r ^ i, ?_, ?_⟩, rfl⟩
  · simp [mul_geom_sum, hn]
  · simp [geom_sum_mul, hn]

中文:
定理 是幂零.isUnit_sub_one
  条件: [环 R] {r : R} (hnil : 是幂零 r)
  结论: 是单位 (r - 1)
  证明: by
  obtain ⟨n, hn⟩ := hnil
  refine ⟨⟨r - 1, -∑ i in Finset.range n, r ^ i, ?_, ?_⟩, rfl⟩
  · simp [mul_geom_sum, hn]
  · simp [geom_sum_mul, hn]

Depends on / 依赖: Finset, Finset.range, geom_sum_mul, mul_geom_sum
-/
theorem IsNilpotent.isUnit_sub_one [Ring R] {r : R} (hnil : IsNilpotent r) : IsUnit (r - 1) := by
  obtain ⟨n, hn⟩ := hnil
  refine ⟨⟨r - 1, -∑ i in Finset.range n, r ^ i, ?_, ?_⟩, rfl⟩
  · simp [mul_geom_sum, hn]
  · simp [geom_sum_mul, hn]

/--
theorem `IsNilpotent.isUnit_one_sub` / 定理 `IsNilpotent.isUnit_one_sub`

English:
theorem IsNilpotent.isUnit_one_sub
  given: [Ring R] {r : R} (hnil : IsNilpotent r)
  statement: IsUnit (1 - r)
  proof: by
  rw [← IsUnit.neg_iff]; rw [neg_sub]
  exact isUnit_sub_one hnil

中文:
定理 是幂零.isUnit_one_sub
  条件: [环 R] {r : R} (hnil : 是幂零 r)
  结论: 是单位 (1 - r)
  证明: by
  rw [← IsUnit.neg_iff]; rw [neg_sub]
  exact isUnit_sub_one hnil

Depends on / 依赖: IsUnit, IsUnit.neg_iff, isUnit_sub_one, neg_iff, neg_sub
-/
theorem IsNilpotent.isUnit_one_sub [Ring R] {r : R} (hnil : IsNilpotent r) : IsUnit (1 - r) := by
  rw [← IsUnit.neg_iff]; rw [neg_sub]
  exact isUnit_sub_one hnil

/--
theorem `IsNilpotent.isUnit_add_one` / 定理 `IsNilpotent.isUnit_add_one`

English:
theorem IsNilpotent.isUnit_add_one
  given: [Ring R] {r : R} (hnil : IsNilpotent r)
  statement: IsUnit (r + 1)
  proof: by
  rw [← IsUnit.neg_iff]; rw [neg_add']
  exact isUnit_sub_one hnil.neg

中文:
定理 是幂零.isUnit_add_one
  条件: [环 R] {r : R} (hnil : 是幂零 r)
  结论: 是单位 (r + 1)
  证明: by
  rw [← IsUnit.neg_iff]; rw [neg_add']
  exact isUnit_sub_one hnil.neg

Depends on / 依赖: IsUnit, IsUnit.neg_iff, hnil.neg, isUnit_sub_one, neg_add, neg_iff
-/
theorem IsNilpotent.isUnit_add_one [Ring R] {r : R} (hnil : IsNilpotent r) : IsUnit (r + 1) := by
  rw [← IsUnit.neg_iff]; rw [neg_add']
  exact isUnit_sub_one hnil.neg

/--
theorem `IsNilpotent.isUnit_one_add` / 定理 `IsNilpotent.isUnit_one_add`

English:
theorem IsNilpotent.isUnit_one_add
  given: [Ring R] {r : R} (hnil : IsNilpotent r)
  statement: IsUnit (1 + r)
  proof: add_comm r 1 ▸ isUnit_add_one hnil

中文:
定理 是幂零.isUnit_one_add
  条件: [环 R] {r : R} (hnil : 是幂零 r)
  结论: 是单位 (1 + r)
  证明: add_comm r 1 ▸ isUnit_add_one hnil

Depends on / 依赖: add_comm, isUnit_add_one
-/
theorem IsNilpotent.isUnit_one_add [Ring R] {r : R} (hnil : IsNilpotent r) : IsUnit (1 + r) :=
  add_comm r 1 ▸ isUnit_add_one hnil

/--
theorem `IsNilpotent.isUnit_add_left_of_commute` / 定理 `IsNilpotent.isUnit_add_left_of_commute`

English:
theorem IsNilpotent.isUnit_add_left_of_commute
  statement: [Ring R] {r u : R}
  proof: by
  rw [← Units.isUnit_mul_units _ hu.unit⁻¹]; rw [add_mul]; rw [IsUnit.mul_val_inv]
  replace h_comm : Commute r (↑hu.unit⁻¹) := Commute.units_inv_right h_comm
  refine IsNilpotent.isUnit_one_add ?_
  exact (hu.unit⁻¹.isUnit.isNilpotent_mul_unit_of_commute_iff h_comm).mpr hnil

中文:
定理 是幂零.isUnit_add_left_of_commute
  结论: [环 R] {r u : R}
  证明: by
  rw [← Units.isUnit_mul_units _ hu.unit⁻¹]; rw [add_mul]; rw [IsUnit.mul_val_inv]
  replace h_comm : Commute r (↑hu.unit⁻¹) := Commute.units_inv_right h_comm
  refine IsNilpotent.isUnit_one_add ?_
  exact (hu.unit⁻¹.isUnit.isNilpotent_mul_unit_of_commute_iff h_comm).mpr hnil

Depends on / 依赖: Commute, Commute.units_inv_right, IsNilpotent, IsNilpotent.isUnit_one_add, IsUnit, IsUnit.mul_val_inv, Units.isUnit_mul_units, add_mul, h_comm, hu.unit, isNilpotent_mul_unit_of_commute_iff, isUnit, isUnit.isNilpotent_mul_unit_of_commute_iff, isUnit_mul_units, isUnit_one_add, mul_val_inv, replace, units_inv_right
-/
theorem IsNilpotent.isUnit_add_left_of_commute [Ring R] {r u : R}
    (hnil : IsNilpotent r) (hu : IsUnit u) (h_comm : Commute r u) :
    IsUnit (u + r) := by
  rw [← Units.isUnit_mul_units _ hu.unit⁻¹]; rw [add_mul]; rw [IsUnit.mul_val_inv]
  replace h_comm : Commute r (↑hu.unit⁻¹) := Commute.units_inv_right h_comm
  refine IsNilpotent.isUnit_one_add ?_
  exact (hu.unit⁻¹.isUnit.isNilpotent_mul_unit_of_commute_iff h_comm).mpr hnil

/--
theorem `IsNilpotent.isUnit_add_right_of_commute` / 定理 `IsNilpotent.isUnit_add_right_of_commute`

English:
theorem IsNilpotent.isUnit_add_right_of_commute
  statement: [Ring R] {r u : R}
  proof: add_comm r u ▸ hnil.isUnit_add_left_of_commute hu h_comm

中文:
定理 是幂零.isUnit_add_right_of_commute
  结论: [环 R] {r u : R}
  证明: add_comm r u ▸ hnil.isUnit_add_left_of_commute hu h_comm

Depends on / 依赖: add_comm, h_comm, hnil.isUnit_add_left_of_commute, isUnit_add_left_of_commute
-/
theorem IsNilpotent.isUnit_add_right_of_commute [Ring R] {r u : R}
    (hnil : IsNilpotent r) (hu : IsUnit u) (h_comm : Commute r u) :
    IsUnit (r + u) :=
  add_comm r u ▸ hnil.isUnit_add_left_of_commute hu h_comm

/--
lemma `IsUnit.not_isNilpotent` / 引理 `IsUnit.not_isNilpotent`

English:
lemma IsUnit.not_isNilpotent
  given: [Ring R] [Nontrivial R] {x : R} (hx : IsUnit x)
  proof: by
  intro H
  simpa using H.isUnit_add_right_of_commute hx.neg (by simp)

中文:
引理 是单位.not_isNilpotent
  条件: [环 R] [非平凡 R] {x : R} (hx : 是单位 x)
  证明: by
  intro H
  simpa using H.isUnit_add_right_of_commute hx.neg (by simp)

Depends on / 依赖: H.isUnit_add_right_of_commute, hx.neg, isUnit_add_right_of_commute
-/
lemma IsUnit.not_isNilpotent [Ring R] [Nontrivial R] {x : R} (hx : IsUnit x) :
    ¬ IsNilpotent x := by
  intro H
  simpa using H.isUnit_add_right_of_commute hx.neg (by simp)

/--
lemma `IsNilpotent.not_isUnit` / 引理 `IsNilpotent.not_isUnit`

English:
lemma IsNilpotent.not_isUnit
  given: [Ring R] [Nontrivial R] {x : R} (hx : IsNilpotent x)
  proof: mt IsUnit.not_isNilpotent (by simpa only [not_not] using hx)

中文:
引理 是幂零.not_isUnit
  条件: [环 R] [非平凡 R] {x : R} (hx : 是幂零 x)
  证明: mt IsUnit.not_isNilpotent (by simpa only [not_not] using hx)

Depends on / 依赖: IsUnit, IsUnit.not_isNilpotent, not_isNilpotent, not_not
-/
lemma IsNilpotent.not_isUnit [Ring R] [Nontrivial R] {x : R} (hx : IsNilpotent x) :
    ¬ IsUnit x :=
  mt IsUnit.not_isNilpotent (by simpa only [not_not] using hx)

/--
lemma `IsIdempotentElem.eq_zero_of_isNilpotent` / 引理 `IsIdempotentElem.eq_zero_of_isNilpotent`

English:
lemma IsIdempotentElem.eq_zero_of_isNilpotent
  statement: [MonoidWithZero R] {e : R}
  proof: by
  obtain ⟨rfl | n, hn⟩ := nilp
  · rw [pow_zero] at hn; rw [← one_mul e, hn, zero_mul]
  · rw [← hn, idem.pow_succ_eq]

alias IsNilpotent.eq_zero_of_isIdempotentElem := IsIdempotentElem.eq_zero_of_isNilpotent

中文:
引理 IsIdempotentElem.eq_zero_of_isNilpotent
  结论: [带零幺半群 R] {e : R}
  证明: by
  obtain ⟨rfl | n, hn⟩ := nilp
  · rw [pow_zero] at hn; rw [← one_mul e, hn, zero_mul]
  · rw [← hn, idem.pow_succ_eq]

alias IsNilpotent.eq_zero_of_isIdempotentElem := IsIdempotentElem.eq_zero_of_isNilpotent

Depends on / 依赖: idem.pow_succ_eq, one_mul, pow_succ_eq, pow_zero, zero_mul
-/
lemma IsIdempotentElem.eq_zero_of_isNilpotent [MonoidWithZero R] {e : R}
    (idem : IsIdempotentElem e) (nilp : IsNilpotent e) : e = 0 := by
  obtain ⟨rfl | n, hn⟩ := nilp
  · rw [pow_zero] at hn; rw [← one_mul e, hn, zero_mul]
  · rw [← hn, idem.pow_succ_eq]

alias IsNilpotent.eq_zero_of_isIdempotentElem := IsIdempotentElem.eq_zero_of_isNilpotent

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Zero
  signature: R] [Pow R Nat] [Zero S] [Pow S Nat] [IsReduced R] [IsReduced S] : IsReduced (R × S) where
  body: fun ⟨n, hn⟩ => have hn := Prod.ext_iff.1 hn
    Prod.ext (IsReduced.eq_zero _ ⟨n, hn.1⟩) (IsReduced.eq_zero _ ⟨n, hn.2⟩)

中文:
实例 [零
  签名: R] [幂 R 自然数] [零 S] [幂 S 自然数] [是既约 R] [是既约 S] : 是既约 (R × S) where
  定义体: fun ⟨n, hn⟩ => have hn := Prod.ext_iff.1 hn
    Prod.ext (IsReduced.eq_zero _ ⟨n, hn.1⟩) (IsReduced.eq_zero _ ⟨n, hn.2⟩)
-/
instance [Zero R] [Pow R Nat] [Zero S] [Pow S Nat] [IsReduced R] [IsReduced S] : IsReduced (R × S) where
  eq_zero _ := fun ⟨n, hn⟩ => have hn := Prod.ext_iff.1 hn
    Prod.ext (IsReduced.eq_zero _ ⟨n, hn.1⟩) (IsReduced.eq_zero _ ⟨n, hn.2⟩)

/--
theorem `Prime.isRadical` / 定理 `Prime.isRadical`

English:
theorem Prime.isRadical
  given: [CommMonoidWithZero R] {y : R} (hy : Prime y)
  statement: IsRadical y
  proof: fun _ _ => hy.dvd_of_dvd_pow

中文:
定理 素.isRadical
  条件: [带零交换幺半群 R] {y : R} (hy : 素 y)
  结论: IsRadical y
  证明: fun _ _ => hy.dvd_of_dvd_pow

Depends on / 依赖: dvd_of_dvd_pow, hy.dvd_of_dvd_pow
-/
theorem Prime.isRadical [CommMonoidWithZero R] {y : R} (hy : Prime y) : IsRadical y :=
  fun _ _ => hy.dvd_of_dvd_pow

/--
theorem `zero_isRadical_iff` / 定理 `zero_isRadical_iff`

English:
theorem zero_isRadical_iff
  given: [MonoidWithZero R]
  statement: IsRadical (0 : R) ↔ IsReduced R
  proof: by
  simp_rw [isReduced_iff, IsNilpotent, exists_imp, ← zero_dvd_iff]
  exact forall_comm

中文:
定理 zero_isRadical_iff
  条件: [带零幺半群 R]
  结论: IsRadical (0 : R) ↔ 是既约 R
  证明: by
  simp_rw [isReduced_iff, IsNilpotent, exists_imp, ← zero_dvd_iff]
  exact forall_comm

Depends on / 依赖: IsNilpotent, exists_imp, forall_comm, isReduced_iff, simp_rw, zero_dvd_iff
-/
theorem zero_isRadical_iff [MonoidWithZero R] : IsRadical (0 : R) ↔ IsReduced R := by
  simp_rw [isReduced_iff, IsNilpotent, exists_imp, ← zero_dvd_iff]
  exact forall_comm

/--
theorem `isReduced_iff_pow_one_lt` / 定理 `isReduced_iff_pow_one_lt`

English:
theorem isReduced_iff_pow_one_lt
  given: [MonoidWithZero R] (k : Nat) (hk : 1 < k)
  proof: by
  simp_rw [← zero_isRadical_iff, isRadical_iff_pow_one_lt k hk, zero_dvd_iff]

中文:
定理 isReduced_iff_pow_one_lt
  条件: [带零幺半群 R] (k : 自然数) (hk : 1 < k)
  证明: by
  simp_rw [← zero_isRadical_iff, isRadical_iff_pow_one_lt k hk, zero_dvd_iff]

Depends on / 依赖: isRadical_iff_pow_one_lt, simp_rw, zero_dvd_iff, zero_isRadical_iff
-/
theorem isReduced_iff_pow_one_lt [MonoidWithZero R] (k : Nat) (hk : 1 < k) :
    IsReduced R ↔ forall x : R, x ^ k = 0 -> x = 0 := by
  simp_rw [← zero_isRadical_iff, isRadical_iff_pow_one_lt k hk, zero_dvd_iff]

/--
theorem `IsRadical.of_dvd` / 定理 `IsRadical.of_dvd`

English:
theorem IsRadical.of_dvd
  statement: [CommMonoidWithZero R] [IsCancelMulZero R] {x y : R} (hy : IsRadical y)
  proof: (isRadical_iff_pow_one_lt 2 one_lt_two).2 by
  obtain ⟨z, rfl⟩ := hxy
  refine fun w dvd => ((mul_dvd_mul_iff_right <| right_ne_zero_of_mul h0).mp <| hy 2 _ ?_)
  rw [mul_pow]
  gcongr
  exact dvd_pow_self _ two_ne_zero

中文:
定理 IsRadical.of_dvd
  结论: [带零交换幺半群 R] [是乘零消去 R] {x y : R} (hy : IsRadical y)
  证明: (isRadical_iff_pow_one_lt 2 one_lt_two).2 by
  obtain ⟨z, rfl⟩ := hxy
  refine fun w dvd => ((mul_dvd_mul_iff_right <| right_ne_zero_of_mul h0).mp <| hy 2 _ ?_)
  rw [mul_pow]
  gcongr
  exact dvd_pow_self _ two_ne_zero

Depends on / 依赖: dvd_pow_self, isRadical_iff_pow_one_lt, mul_dvd_mul_iff_right, mul_pow, one_lt_two, right_ne_zero_of_mul, two_ne_zero
-/
theorem IsRadical.of_dvd [CommMonoidWithZero R] [IsCancelMulZero R] {x y : R} (hy : IsRadical y)
(h0 : y != 0) (hxy : x ∣ y) : IsRadical x := (isRadical_iff_pow_one_lt 2 one_lt_two).2 by
  obtain ⟨z, rfl⟩ := hxy
  refine fun w dvd => ((mul_dvd_mul_iff_right <| right_ne_zero_of_mul h0).mp <| hy 2 _ ?_)
  rw [mul_pow]
  gcongr
  exact dvd_pow_self _ two_ne_zero

namespace Commute

section Semiring

variable [Semiring R]

/--
theorem `add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero` / 定理 `add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero`

English:
theorem add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero
  statement: (h_comm : Commute x y) {m n k : Nat}
  proof: by
  rw [h_comm.add_pow']
  apply Finset.sum_eq_zero
  rintro ⟨i, j⟩ hij
  suffices x ^ i * y ^ j = 0 by simp only [this, nsmul_eq_mul, mul_zero]
  by_cases hi : m <= i
  · rw [pow_eq_zero_of_le hi hx, zero_mul]
  rw [pow_eq_zero_of_le ?_ hy]; rw [mul_zero]
  linarith [Finset.mem_antidiagonal.mp hij

中文:
定理 add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero
  结论: (h_comm : Commute x y) {m n k : 自然数}
  证明: by
  rw [h_comm.add_pow']
  apply Finset.sum_eq_zero
  rintro ⟨i, j⟩ hij
  suffices x ^ i * y ^ j = 0 by simp only [this, nsmul_eq_mul, mul_zero]
  by_cases hi : m <= i
  · rw [pow_eq_zero_of_le hi hx, zero_mul]
  rw [pow_eq_zero_of_le ?_ hy]; rw [mul_zero]
  linarith [Finset.mem_antidiagonal.mp hij

Depends on / 依赖: Finset, Finset.mem_antidiagonal.mp, Finset.sum_eq_zero, add_pow, h_comm, h_comm.add_pow, mem_antidiagonal, mul_zero, nsmul_eq_mul, pow_eq_zero_of_le, sum_eq_zero, zero_mul
-/
theorem add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero (h_comm : Commute x y) {m n k : Nat}
    (hx : x ^ m = 0) (hy : y ^ n = 0) (h : m + n <= k + 1) :
    (x + y) ^ k = 0 := by
  rw [h_comm.add_pow']
  apply Finset.sum_eq_zero
  rintro ⟨i, j⟩ hij
  suffices x ^ i * y ^ j = 0 by simp only [this, nsmul_eq_mul, mul_zero]
  by_cases hi : m <= i
  · rw [pow_eq_zero_of_le hi hx, zero_mul]
  rw [pow_eq_zero_of_le ?_ hy]; rw [mul_zero]
  linarith [Finset.mem_antidiagonal.mp hij]

/--
theorem `add_pow_add_eq_zero_of_pow_eq_zero` / 定理 `add_pow_add_eq_zero_of_pow_eq_zero`

English:
theorem add_pow_add_eq_zero_of_pow_eq_zero
  statement: (h_comm : Commute x y) {m n : Nat}
  proof: h_comm.add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero hx hy by rw [← Nat.sub_le_iff_le_add]

中文:
定理 add_pow_add_eq_zero_of_pow_eq_zero
  结论: (h_comm : Commute x y) {m n : 自然数}
  证明: h_comm.add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero hx hy by rw [← Nat.sub_le_iff_le_add]

Depends on / 依赖: Nat.sub_le_iff_le_add, add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero, h_comm, h_comm.add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero, sub_le_iff_le_add
-/
theorem add_pow_add_eq_zero_of_pow_eq_zero (h_comm : Commute x y) {m n : Nat}
    (hx : x ^ m = 0) (hy : y ^ n = 0) :
    (x + y) ^ (m + n - 1) = 0 :=
h_comm.add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero hx hy by rw [← Nat.sub_le_iff_le_add]

/--
theorem `isNilpotent_add` / 定理 `isNilpotent_add`

English:
theorem isNilpotent_add
  given: (h_comm : Commute x y) (hx : IsNilpotent x) (hy : IsNilpotent y)
  proof: by
  obtain ⟨n, hn⟩ := hx
  obtain ⟨m, hm⟩ := hy
  exact ⟨_, add_pow_add_eq_zero_of_pow_eq_zero h_comm hn hm⟩

中文:
定理 isNilpotent_add
  条件: (h_comm : Commute x y) (hx : 是幂零 x) (hy : 是幂零 y)
  证明: by
  obtain ⟨n, hn⟩ := hx
  obtain ⟨m, hm⟩ := hy
  exact ⟨_, add_pow_add_eq_zero_of_pow_eq_zero h_comm hn hm⟩

Depends on / 依赖: add_pow_add_eq_zero_of_pow_eq_zero, h_comm
-/
theorem isNilpotent_add (h_comm : Commute x y) (hx : IsNilpotent x) (hy : IsNilpotent y) :
    IsNilpotent (x + y) := by
  obtain ⟨n, hn⟩ := hx
  obtain ⟨m, hm⟩ := hy
  exact ⟨_, add_pow_add_eq_zero_of_pow_eq_zero h_comm hn hm⟩

/--
lemma `isNilpotent_sum` / 引理 `isNilpotent_sum`

English:
lemma isNilpotent_sum
  statement: {ι : Type*} {s : Finset ι} {f : ι -> R}
  proof: by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert j s hj ih => ?_
  rw [Finset.sum_insert hj]
  apply Commute.isNilpotent_add
  · exact Commute.sum_right _ _ _ (fun i hi => h_comm _ _ (by simp) (by simp [hi]))
  · apply hnp; simp
  · exact ih (fun i hi => hnp i (b

中文:
引理 isNilpotent_sum
  结论: {ι : 类型} {s : 有限集 ι} {f : ι -> R}
  证明: by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert j s hj ih => ?_
  rw [Finset.sum_insert hj]
  apply Commute.isNilpotent_add
  · exact Commute.sum_right _ _ _ (fun i hi => h_comm _ _ (by simp) (by simp [hi]))
  · apply hnp; simp
  · exact ih (fun i hi => hnp i (b
-/
protected lemma isNilpotent_sum {ι : Type*} {s : Finset ι} {f : ι -> R}
    (hnp : forall i in s, IsNilpotent (f i)) (h_comm : forall i j, i in s -> j in s -> Commute (f i) (f j)) :
    IsNilpotent (∑ i in s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert j s hj ih => ?_
  rw [Finset.sum_insert hj]
  apply Commute.isNilpotent_add
  · exact Commute.sum_right _ _ _ (fun i hi => h_comm _ _ (by simp) (by simp [hi]))
  · apply hnp; simp
  · exact ih (fun i hi => hnp i (by simp [hi]))
      (fun i j hi hj => h_comm i j (by simp [hi]) (by simp [hj]))

/--
theorem `isNilpotent_finsum` / 定理 `isNilpotent_finsum`

English:
theorem isNilpotent_finsum
  statement: {ι : Type*} {f : ι -> R}
  proof: by
  classical
  by_cases h : HasFiniteSupport f
  · rw [finsum_def, dif_pos h]
    exact Commute.isNilpotent_sum (fun b _ => hf b) (fun _ _ _ _ => h_comm _ _)
  · simp only [finsum_def, dif_neg h, IsNilpotent.zero]

中文:
定理 isNilpotent_finsum
  结论: {ι : 类型} {f : ι -> R}
  证明: by
  classical
  by_cases h : HasFiniteSupport f
  · rw [finsum_def, dif_pos h]
    exact Commute.isNilpotent_sum (fun b _ => hf b) (fun _ _ _ _ => h_comm _ _)
  · simp only [finsum_def, dif_neg h, IsNilpotent.zero]

Depends on / 依赖: Commute, Commute.isNilpotent_sum, HasFiniteSupport, IsNilpotent, IsNilpotent.zero, classical, dif_neg, dif_pos, finsum_def, h_comm, isNilpotent_sum
-/
theorem isNilpotent_finsum {ι : Type*} {f : ι -> R}
    (hf : forall b, IsNilpotent (f b)) (h_comm : forall i j, Commute (f i) (f j)) :
    IsNilpotent (finsum f) := by
  classical
  by_cases h : HasFiniteSupport f
  · rw [finsum_def, dif_pos h]
    exact Commute.isNilpotent_sum (fun b _ => hf b) (fun _ _ _ _ => h_comm _ _)
  · simp only [finsum_def, dif_neg h, IsNilpotent.zero]

/--
lemma `isNilpotent_mul_right_iff` / 引理 `isNilpotent_mul_right_iff`

English:
lemma isNilpotent_mul_right_iff
  given: (h_comm : Commute x y) (hy : y in nonZeroDivisorsRight R)
  proof: by
  refine ⟨?_, h_comm.isNilpotent_mul_right⟩
  rintro ⟨k, hk⟩
  rw [mul_pow h_comm] at hk
  exact ⟨k, (nonZeroDivisorsRight R).pow_mem hy k _ hk⟩

中文:
引理 isNilpotent_mul_right_iff
  条件: (h_comm : Commute x y) (hy : y in nonZeroDivisorsRight R)
  证明: by
  refine ⟨?_, h_comm.isNilpotent_mul_right⟩
  rintro ⟨k, hk⟩
  rw [mul_pow h_comm] at hk
  exact ⟨k, (nonZeroDivisorsRight R).pow_mem hy k _ hk⟩
-/
protected lemma isNilpotent_mul_right_iff (h_comm : Commute x y) (hy : y in nonZeroDivisorsRight R) :
    IsNilpotent (x * y) ↔ IsNilpotent x := by
  refine ⟨?_, h_comm.isNilpotent_mul_right⟩
  rintro ⟨k, hk⟩
  rw [mul_pow h_comm] at hk
  exact ⟨k, (nonZeroDivisorsRight R).pow_mem hy k _ hk⟩

/--
lemma `isNilpotent_mul_left_iff` / 引理 `isNilpotent_mul_left_iff`

English:
lemma isNilpotent_mul_left_iff
  given: (h_comm : Commute x y) (hx : x in nonZeroDivisorsLeft R)
  proof: by
  refine ⟨?_, h_comm.isNilpotent_mul_left⟩
  rintro ⟨k, hk⟩
  rw [mul_pow h_comm] at hk
  exact ⟨k, (nonZeroDivisorsLeft R).pow_mem hx k _ hk⟩

中文:
引理 isNilpotent_mul_left_iff
  条件: (h_comm : Commute x y) (hx : x in nonZeroDivisorsLeft R)
  证明: by
  refine ⟨?_, h_comm.isNilpotent_mul_left⟩
  rintro ⟨k, hk⟩
  rw [mul_pow h_comm] at hk
  exact ⟨k, (nonZeroDivisorsLeft R).pow_mem hx k _ hk⟩
-/
protected lemma isNilpotent_mul_left_iff (h_comm : Commute x y) (hx : x in nonZeroDivisorsLeft R) :
    IsNilpotent (x * y) ↔ IsNilpotent y := by
  refine ⟨?_, h_comm.isNilpotent_mul_left⟩
  rintro ⟨k, hk⟩
  rw [mul_pow h_comm] at hk
  exact ⟨k, (nonZeroDivisorsLeft R).pow_mem hx k _ hk⟩

end Semiring

section Ring

variable [Ring R]

/--
theorem `isNilpotent_sub` / 定理 `isNilpotent_sub`

English:
theorem isNilpotent_sub
  given: (h_comm : Commute x y) (hx : IsNilpotent x) (hy : IsNilpotent y)
  proof: by
  rw [← neg_right_iff] at h_comm
  rw [← isNilpotent_neg_iff] at hy
  rw [sub_eq_add_neg]
  exact h_comm.isNilpotent_add hx hy

中文:
定理 isNilpotent_sub
  条件: (h_comm : Commute x y) (hx : 是幂零 x) (hy : 是幂零 y)
  证明: by
  rw [← neg_right_iff] at h_comm
  rw [← isNilpotent_neg_iff] at hy
  rw [sub_eq_add_neg]
  exact h_comm.isNilpotent_add hx hy

Depends on / 依赖: h_comm, h_comm.isNilpotent_add, isNilpotent_add, isNilpotent_neg_iff, neg_right_iff, sub_eq_add_neg
-/
theorem isNilpotent_sub (h_comm : Commute x y) (hx : IsNilpotent x) (hy : IsNilpotent y) :
    IsNilpotent (x - y) := by
  rw [← neg_right_iff] at h_comm
  rw [← isNilpotent_neg_iff] at hy
  rw [sub_eq_add_neg]
  exact h_comm.isNilpotent_add hx hy

end Ring

end Commute

section CommSemiring

variable [CommSemiring R] {x y : R}

/--
lemma `isNilpotent_sum` / 引理 `isNilpotent_sum`

English:
lemma isNilpotent_sum
  statement: {ι : Type*} {s : Finset ι} {f : ι -> R}
  proof: Commute.isNilpotent_sum hnp fun _ _ _ _ => Commute.all _ _

中文:
引理 isNilpotent_sum
  结论: {ι : 类型} {s : 有限集 ι} {f : ι -> R}
  证明: Commute.isNilpotent_sum hnp fun _ _ _ _ => Commute.all _ _

Depends on / 依赖: Commute, Commute.all, Commute.isNilpotent_sum, isNilpotent_sum
-/
lemma isNilpotent_sum {ι : Type*} {s : Finset ι} {f : ι -> R}
    (hnp : forall i in s, IsNilpotent (f i)) :
    IsNilpotent (∑ i in s, f i) :=
  Commute.isNilpotent_sum hnp fun _ _ _ _ => Commute.all _ _

/--
theorem `isNilpotent_finsum` / 定理 `isNilpotent_finsum`

English:
theorem isNilpotent_finsum
  statement: {ι : Type*} {f : ι -> R}
  proof: Commute.isNilpotent_finsum hf fun _ _ => Commute.all _ _

中文:
定理 isNilpotent_finsum
  结论: {ι : 类型} {f : ι -> R}
  证明: Commute.isNilpotent_finsum hf fun _ _ => Commute.all _ _

Depends on / 依赖: Commute, Commute.all, Commute.isNilpotent_finsum, isNilpotent_finsum
-/
theorem isNilpotent_finsum {ι : Type*} {f : ι -> R}
    (hf : forall b, IsNilpotent (f b)) :
    IsNilpotent (finsum f) :=
  Commute.isNilpotent_finsum hf fun _ _ => Commute.all _ _

end CommSemiring
