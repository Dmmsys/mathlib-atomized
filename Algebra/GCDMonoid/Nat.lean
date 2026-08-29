/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Aaron Anderson
-/
module

public import Mathlib.Algebra.GCDMonoid.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Int
public import Mathlib.Algebra.Ring.Int.Units
public import Mathlib.Algebra.GroupWithZero.Nat

/-!
# ℕ and ℤ are normalized GCD monoids.

## Main statements

* ℕ is a `GCDMonoid`
* ℕ is a `StrongNormalizedGCDMonoid`
* ℤ is a `StrongNormalizationMonoid`
* ℤ is a `GCDMonoid`
* ℤ is a `StrongNormalizedGCDMonoid`

## Tags
natural numbers, integers, normalization monoid, gcd monoid, greatest common divisor
-/

@[expose] public section

assert_not_exists IsOrderedMonoid

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: GCDMonoid Nat
  body: Nat.gcd
  lcm := Nat.lcm
  gcd_dvd_left := Nat.gcd_dvd_left
  gcd_dvd_right := Nat.gcd_dvd_right
  dvd_gcd := Nat.dvd_gcd
  gcd_mul_lcm a b := by rw [Nat.gcd_mul_lcm]; rfl
  lcm_zero_left := Nat.lcm_zero_left
  lcm_zero_right := Nat.lcm_zero_right

中文:
实例 :
  签名: 最大公约数幺半群 自然数
  定义体: Nat.gcd
  lcm := Nat.lcm
  gcd_dvd_left := Nat.gcd_dvd_left
  gcd_dvd_right := Nat.gcd_dvd_right
  dvd_gcd := Nat.dvd_gcd
  gcd_mul_lcm a b := by rw [Nat.gcd_mul_lcm]; rfl
  lcm_zero_left := Nat.lcm_zero_left
  lcm_zero_right := Nat.lcm_zero_right

Depends on / 依赖: Nat.gcd
-/
instance : GCDMonoid Nat where
  gcd := Nat.gcd
  lcm := Nat.lcm
  gcd_dvd_left := Nat.gcd_dvd_left
  gcd_dvd_right := Nat.gcd_dvd_right
  dvd_gcd := Nat.dvd_gcd
  gcd_mul_lcm a b := by rw [Nat.gcd_mul_lcm]; rfl
  lcm_zero_left := Nat.lcm_zero_left
  lcm_zero_right := Nat.lcm_zero_right

/--
theorem `gcd_eq_nat_gcd` / 定理 `gcd_eq_nat_gcd`

English:
theorem gcd_eq_nat_gcd
  given: (m n : Nat)
  statement: gcd m n = Nat.gcd m n
  proof: rfl

中文:
定理 gcd_eq_nat_gcd
  条件: (m n : 自然数)
  结论: 最大公约数 m n = 自然数.最大公约数 m n
  证明: rfl
-/
theorem gcd_eq_nat_gcd (m n : Nat) : gcd m n = Nat.gcd m n :=
  rfl

/--
theorem `lcm_eq_nat_lcm` / 定理 `lcm_eq_nat_lcm`

English:
theorem lcm_eq_nat_lcm
  given: (m n : Nat)
  statement: lcm m n = Nat.lcm m n
  proof: rfl

中文:
定理 lcm_eq_nat_lcm
  条件: (m n : 自然数)
  结论: 最小公倍数 m n = 自然数.最小公倍数 m n
  证明: rfl
-/
theorem lcm_eq_nat_lcm (m n : Nat) : lcm m n = Nat.lcm m n :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: StrongNormalizedGCDMonoid Nat
  body: { (inferInstance : GCDMonoid Nat),
    (inferInstance : StrongNormalizationMonoid Nat) with
    normalize_gcd := fun _ _ => normalize_eq _
    normalize_lcm := fun _ _ => normalize_eq _ }

中文:
实例 :
  签名: StrongNormalizedGCD幺半群 自然数
  定义体: { (inferInstance : GCDMonoid Nat),
    (inferInstance : StrongNormalizationMonoid Nat) with
    normalize_gcd := fun _ _ => normalize_eq _
    normalize_lcm := fun _ _ => normalize_eq _ }

Depends on / 依赖: GCDMonoid, StrongNormalizationMonoid, normalize_eq, normalize_gcd, normalize_lcm
-/
instance : StrongNormalizedGCDMonoid Nat :=
  { (inferInstance : GCDMonoid Nat),
    (inferInstance : StrongNormalizationMonoid Nat) with
    normalize_gcd := fun _ _ => normalize_eq _
    normalize_lcm := fun _ _ => normalize_eq _ }

namespace Int

section NormalizationMonoid

/--
Instance `strongNormalizationMonoid` / 实例 `strongNormalizationMonoid`

English:
instance strongNormalizationMonoid
  signature: : StrongNormalizationMonoid Int where
  body: if 0 <= a then 1 else -1
  normUnit_zero := if_pos le_rfl
  normUnit_mul {a b} hna hnb := by
    rcases hna.lt_or_gt with ha | ha <;> rcases hnb.lt_or_gt with hb | hb <;>
      simp [Int.mul_nonneg_iff, ha.le, ha.not_ge, hb.le, hb.not_ge]
  normUnit_coe_units u :=
    (units_eq_one_or u).elim (fun eq => eq.symm ▸ if_pos Int.one_nonneg) fun eq =>
      eq.symm ▸ if_neg (not_le_of_gt <| show (-1 : Int) < 0 by decide)

@[deprecated (since := "2026-07-08")]
alias normalizationMonoid := strongNormalizationMonoid

中文:
实例 strongNormalizationMonoid
  签名: : StrongNormalization幺半群 整数 where
  定义体: if 0 <= a then 1 else -1
  normUnit_zero := if_pos le_rfl
  normUnit_mul {a b} hna hnb := by
    rcases hna.lt_or_gt with ha | ha <;> rcases hnb.lt_or_gt with hb | hb <;>
      simp [Int.mul_nonneg_iff, ha.le, ha.not_ge, hb.le, hb.not_ge]
  normUnit_coe_units u :=
    (units_eq_one_or u).elim (fun eq => eq.symm ▸ if_pos Int.one_nonneg) fun eq =>
      eq.symm ▸ if_neg (not_le_of_gt <| show (-1 : Int) < 0 by decide)

@[deprecated (since := "2026-07-08")]
alias normalizationMonoid := strongNormalizationMonoid
-/
instance strongNormalizationMonoid : StrongNormalizationMonoid Int where
  normUnit a := if 0 <= a then 1 else -1
  normUnit_zero := if_pos le_rfl
  normUnit_mul {a b} hna hnb := by
    rcases hna.lt_or_gt with ha | ha <;> rcases hnb.lt_or_gt with hb | hb <;>
      simp [Int.mul_nonneg_iff, ha.le, ha.not_ge, hb.le, hb.not_ge]
  normUnit_coe_units u :=
    (units_eq_one_or u).elim (fun eq => eq.symm ▸ if_pos Int.one_nonneg) fun eq =>
      eq.symm ▸ if_neg (not_le_of_gt <| show (-1 : Int) < 0 by decide)

@[deprecated (since := "2026-07-08")]
alias normalizationMonoid := strongNormalizationMonoid

/--
theorem `normUnit_eq` / 定理 `normUnit_eq`

English:
theorem normUnit_eq
  given: (z : Int)
  statement: normUnit z = if 0 <= z then 1 else -1
  proof: rfl

中文:
定理 normUnit_eq
  条件: (z : 整数)
  结论: normUnit z = if 0 <= z then 1 else -1
  证明: rfl
-/
theorem normUnit_eq (z : Int) : normUnit z = if 0 <= z then 1 else -1 := rfl

/--
theorem `normalize_of_nonneg` / 定理 `normalize_of_nonneg`

English:
theorem normalize_of_nonneg
  given: {z : Int} (h : 0 <= z)
  statement: normalize z = z
  proof: by
  rw [normalize_apply]; rw [normUnit_eq]; rw [if_pos h]; rw [Units.val_one]; rw [mul_one]

中文:
定理 normalize_of_nonneg
  条件: {z : 整数} (h : 0 <= z)
  结论: normalize z = z
  证明: by
  rw [normalize_apply]; rw [normUnit_eq]; rw [if_pos h]; rw [Units.val_one]; rw [mul_one]

Depends on / 依赖: Units.val_one, if_pos, mul_one, normUnit_eq, normalize_apply, val_one
-/
theorem normalize_of_nonneg {z : Int} (h : 0 <= z) : normalize z = z := by
  rw [normalize_apply]; rw [normUnit_eq]; rw [if_pos h]; rw [Units.val_one]; rw [mul_one]

/--
theorem `normalize_of_nonpos` / 定理 `normalize_of_nonpos`

English:
theorem normalize_of_nonpos
  given: {z : Int} (h : z <= 0)
  statement: normalize z = -z
  proof: by
  obtain rfl | h := h.eq_or_lt
  · simp
  · rw [normalize_apply, normUnit_eq, if_neg (not_le_of_gt h), Units.val_neg, Units.val_one,
      mul_neg_one]

中文:
定理 normalize_of_nonpos
  条件: {z : 整数} (h : z <= 0)
  结论: normalize z = -z
  证明: by
  obtain rfl | h := h.eq_or_lt
  · simp
  · rw [normalize_apply, normUnit_eq, if_neg (not_le_of_gt h), Units.val_neg, Units.val_one,
      mul_neg_one]

Depends on / 依赖: Units.val_neg, Units.val_one, eq_or_lt, h.eq_or_lt, if_neg, mul_neg_one, normUnit_eq, normalize_apply, not_le_of_gt, val_neg, val_one
-/
theorem normalize_of_nonpos {z : Int} (h : z <= 0) : normalize z = -z := by
  obtain rfl | h := h.eq_or_lt
  · simp
  · rw [normalize_apply, normUnit_eq, if_neg (not_le_of_gt h), Units.val_neg, Units.val_one,
      mul_neg_one]

/--
theorem `normalize_coe_nat` / 定理 `normalize_coe_nat`

English:
theorem normalize_coe_nat
  given: (n : Nat)
  statement: normalize (n : Int) = n
  proof: normalize_of_nonneg (ofNat_le_ofNat_of_le <| Nat.zero_le n)

中文:
定理 normalize_coe_nat
  条件: (n : 自然数)
  结论: normalize (n : 整数) = n
  证明: normalize_of_nonneg (ofNat_le_ofNat_of_le <| Nat.zero_le n)

Depends on / 依赖: Nat.zero_le, normalize_of_nonneg, ofNat_le_ofNat_of_le, zero_le
-/
theorem normalize_coe_nat (n : Nat) : normalize (n : Int) = n :=
  normalize_of_nonneg (ofNat_le_ofNat_of_le <| Nat.zero_le n)

/--
theorem `abs_eq_normalize` / 定理 `abs_eq_normalize`

English:
theorem abs_eq_normalize
  given: (z : Int)
  statement: |z| = normalize z
  proof: by
  cases le_total 0 z <;>
  simp [abs_of_nonneg, abs_of_nonpos, normalize_of_nonneg, normalize_of_nonpos, *]

中文:
定理 abs_eq_normalize
  条件: (z : 整数)
  结论: |z| = normalize z
  证明: by
  cases le_total 0 z <;>
  simp [abs_of_nonneg, abs_of_nonpos, normalize_of_nonneg, normalize_of_nonpos, *]

Depends on / 依赖: abs_of_nonneg, abs_of_nonpos, le_total, normalize_of_nonneg, normalize_of_nonpos
-/
theorem abs_eq_normalize (z : Int) : |z| = normalize z := by
  cases le_total 0 z <;>
  simp [abs_of_nonneg, abs_of_nonpos, normalize_of_nonneg, normalize_of_nonpos, *]

/--
theorem `nonneg_of_normalize_eq_self` / 定理 `nonneg_of_normalize_eq_self`

English:
theorem nonneg_of_normalize_eq_self
  given: {z : Int} (hz : normalize z = z)
  statement: 0 <= z
  proof: by
  by_cases! h : 0 <= z
  · exact h
  · rw [normalize_of_nonpos h.le] at hz
    lia

中文:
定理 nonneg_of_normalize_eq_self
  条件: {z : 整数} (hz : normalize z = z)
  结论: 0 <= z
  证明: by
  by_cases! h : 0 <= z
  · exact h
  · rw [normalize_of_nonpos h.le] at hz
    lia

Depends on / 依赖: h.le, normalize_of_nonpos
-/
theorem nonneg_of_normalize_eq_self {z : Int} (hz : normalize z = z) : 0 <= z := by
  by_cases! h : 0 <= z
  · exact h
  · rw [normalize_of_nonpos h.le] at hz
    lia

/--
theorem `nonneg_iff_normalize_eq_self` / 定理 `nonneg_iff_normalize_eq_self`

English:
theorem nonneg_iff_normalize_eq_self
  given: (z : Int)
  statement: normalize z = z ↔ 0 <= z
  proof: ⟨nonneg_of_normalize_eq_self, normalize_of_nonneg⟩

中文:
定理 nonneg_iff_normalize_eq_self
  条件: (z : 整数)
  结论: normalize z = z ↔ 0 <= z
  证明: ⟨nonneg_of_normalize_eq_self, normalize_of_nonneg⟩

Depends on / 依赖: nonneg_of_normalize_eq_self, normalize_of_nonneg
-/
theorem nonneg_iff_normalize_eq_self (z : Int) : normalize z = z ↔ 0 <= z :=
  ⟨nonneg_of_normalize_eq_self, normalize_of_nonneg⟩

/--
theorem `eq_of_associated_of_nonneg` / 定理 `eq_of_associated_of_nonneg`

English:
theorem eq_of_associated_of_nonneg
  given: {a b : Int} (h : Associated a b) (ha : 0 <= a) (hb : 0 <= b)
  proof: dvd_antisymm_of_normalize_eq (normalize_of_nonneg ha) (normalize_of_nonneg hb) h.dvd h.symm.dvd

中文:
定理 eq_of_associated_of_nonneg
  条件: {a b : 整数} (h : Associated a b) (ha : 0 <= a) (hb : 0 <= b)
  证明: dvd_antisymm_of_normalize_eq (normalize_of_nonneg ha) (normalize_of_nonneg hb) h.dvd h.symm.dvd

Depends on / 依赖: dvd_antisymm_of_normalize_eq, h.dvd, h.symm.dvd, normalize_of_nonneg
-/
theorem eq_of_associated_of_nonneg {a b : Int} (h : Associated a b) (ha : 0 <= a) (hb : 0 <= b) :
    a = b :=
  dvd_antisymm_of_normalize_eq (normalize_of_nonneg ha) (normalize_of_nonneg hb) h.dvd h.symm.dvd

end NormalizationMonoid

section GCDMonoid

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: GCDMonoid Int
  body: Int.gcd a b
  lcm a b := Int.lcm a b
  gcd_dvd_left := Int.gcd_dvd_left
  gcd_dvd_right := Int.gcd_dvd_right
  dvd_gcd := dvd_coe_gcd
  gcd_mul_lcm a b := by
    rw [← Int.natCast_mul]; rw [gcd_mul_lcm]; rw [← natAbs_mul]; rw [natCast_natAbs]; rw [abs_eq_normalize]
    exact normalize_associated (a * b)
lcm_zero_left _ := natCast_eq_zero.2 Nat.lcm_zero_left _
lcm_zero_right _ := natCast_eq_zero.2 Nat.lcm_zero_right _

中文:
实例 :
  签名: 最大公约数幺半群 整数
  定义体: Int.gcd a b
  lcm a b := Int.lcm a b
  gcd_dvd_left := Int.gcd_dvd_left
  gcd_dvd_right := Int.gcd_dvd_right
  dvd_gcd := dvd_coe_gcd
  gcd_mul_lcm a b := by
    rw [← Int.natCast_mul]; rw [gcd_mul_lcm]; rw [← natAbs_mul]; rw [natCast_natAbs]; rw [abs_eq_normalize]
    exact normalize_associated (a * b)
lcm_zero_left _ := natCast_eq_zero.2 Nat.lcm_zero_left _
lcm_zero_right _ := natCast_eq_zero.2 Nat.lcm_zero_right _

Depends on / 依赖: Int.gcd
-/
instance : GCDMonoid Int where
  gcd a b := Int.gcd a b
  lcm a b := Int.lcm a b
  gcd_dvd_left := Int.gcd_dvd_left
  gcd_dvd_right := Int.gcd_dvd_right
  dvd_gcd := dvd_coe_gcd
  gcd_mul_lcm a b := by
    rw [← Int.natCast_mul]; rw [gcd_mul_lcm]; rw [← natAbs_mul]; rw [natCast_natAbs]; rw [abs_eq_normalize]
    exact normalize_associated (a * b)
lcm_zero_left _ := natCast_eq_zero.2 Nat.lcm_zero_left _
lcm_zero_right _ := natCast_eq_zero.2 Nat.lcm_zero_right _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: StrongNormalizedGCDMonoid Int
  body: { Int.strongNormalizationMonoid,
    (inferInstance : GCDMonoid Int) with
    normalize_gcd := fun _ _ => normalize_coe_nat _
    normalize_lcm := fun _ _ => normalize_coe_nat _ }

中文:
实例 :
  签名: StrongNormalizedGCD幺半群 整数
  定义体: { Int.strongNormalizationMonoid,
    (inferInstance : GCDMonoid Int) with
    normalize_gcd := fun _ _ => normalize_coe_nat _
    normalize_lcm := fun _ _ => normalize_coe_nat _ }

Depends on / 依赖: GCDMonoid, Int.strongNormalizationMonoid, normalize_coe_nat, normalize_gcd, normalize_lcm, strongNormalizationMonoid
-/
instance : StrongNormalizedGCDMonoid Int :=
  { Int.strongNormalizationMonoid,
    (inferInstance : GCDMonoid Int) with
    normalize_gcd := fun _ _ => normalize_coe_nat _
    normalize_lcm := fun _ _ => normalize_coe_nat _ }

/--
theorem `coe_gcd` / 定理 `coe_gcd`

English:
theorem coe_gcd
  given: (i j : Int)
  statement: ↑(Int.gcd i j) = GCDMonoid.gcd i j
  proof: rfl

中文:
定理 coe_gcd
  条件: (i j : 整数)
  结论: ↑(整数.最大公约数 i j) = 最大公约数幺半群.最大公约数 i j
  证明: rfl
-/
theorem coe_gcd (i j : Int) : ↑(Int.gcd i j) = GCDMonoid.gcd i j :=
  rfl

/--
theorem `coe_lcm` / 定理 `coe_lcm`

English:
theorem coe_lcm
  given: (i j : Int)
  statement: ↑(Int.lcm i j) = GCDMonoid.lcm i j
  proof: rfl

中文:
定理 coe_lcm
  条件: (i j : 整数)
  结论: ↑(整数.最小公倍数 i j) = 最大公约数幺半群.最小公倍数 i j
  证明: rfl
-/
theorem coe_lcm (i j : Int) : ↑(Int.lcm i j) = GCDMonoid.lcm i j :=
  rfl

/--
theorem `natAbs_gcd` / 定理 `natAbs_gcd`

English:
theorem natAbs_gcd
  given: (i j : Int)
  statement: natAbs (GCDMonoid.gcd i j) = Int.gcd i j
  proof: rfl

中文:
定理 natAbs_gcd
  条件: (i j : 整数)
  结论: natAbs (最大公约数幺半群.最大公约数 i j) = 整数.最大公约数 i j
  证明: rfl
-/
theorem natAbs_gcd (i j : Int) : natAbs (GCDMonoid.gcd i j) = Int.gcd i j :=
  rfl

/--
theorem `natAbs_lcm` / 定理 `natAbs_lcm`

English:
theorem natAbs_lcm
  given: (i j : Int)
  statement: natAbs (GCDMonoid.lcm i j) = Int.lcm i j
  proof: rfl

中文:
定理 natAbs_lcm
  条件: (i j : 整数)
  结论: natAbs (最大公约数幺半群.最小公倍数 i j) = 整数.最小公倍数 i j
  证明: rfl
-/
theorem natAbs_lcm (i j : Int) : natAbs (GCDMonoid.lcm i j) = Int.lcm i j :=
  rfl

/--
lemma `gcd_nonneg` / 引理 `gcd_nonneg`

English:
lemma gcd_nonneg
  given: (i j : Int)
  statement: 0 <= GCDMonoid.gcd i j
  proof: by simp [← coe_gcd]

中文:
引理 gcd_nonneg
  条件: (i j : 整数)
  结论: 0 <= 最大公约数幺半群.最大公约数 i j
  证明: by simp [← coe_gcd]

Depends on / 依赖: coe_gcd
-/
lemma gcd_nonneg (i j : Int) : 0 <= GCDMonoid.gcd i j := by simp [← coe_gcd]
/--
lemma `lcm_nonneg` / 引理 `lcm_nonneg`

English:
lemma lcm_nonneg
  given: (i j : Int)
  statement: 0 <= GCDMonoid.lcm i j
  proof: by simp [← coe_lcm]

中文:
引理 lcm_nonneg
  条件: (i j : 整数)
  结论: 0 <= 最大公约数幺半群.最小公倍数 i j
  证明: by simp [← coe_lcm]

Depends on / 依赖: coe_lcm
-/
lemma lcm_nonneg (i j : Int) : 0 <= GCDMonoid.lcm i j := by simp [← coe_lcm]

end GCDMonoid

/--
theorem `exists_unit_of_abs` / 定理 `exists_unit_of_abs`

English:
theorem exists_unit_of_abs
  given: (a : Int)
  statement: exists (u : Int) (_ : IsUnit u), (Int.natAbs a : Int) = u * a
  proof: by
  rcases natAbs_eq a with h | h
  · use 1, isUnit_one
    rw [← h]; rw [one_mul]
  · use -1, isUnit_one.neg
    rw [← neg_eq_iff_eq_neg.mpr h]
    simp only [neg_mul, one_mul]

中文:
定理 存在_unit_of_abs
  条件: (a : 整数)
  结论: 存在 (u : 整数) (_ : 是单位 u), (整数.natAbs a : 整数) = u * a
  证明: by
  rcases natAbs_eq a with h | h
  · use 1, isUnit_one
    rw [← h]; rw [one_mul]
  · use -1, isUnit_one.neg
    rw [← neg_eq_iff_eq_neg.mpr h]
    simp only [neg_mul, one_mul]

Depends on / 依赖: isUnit_one, isUnit_one.neg, natAbs_eq, neg_eq_iff_eq_neg, neg_eq_iff_eq_neg.mpr, neg_mul, one_mul
-/
theorem exists_unit_of_abs (a : Int) : exists (u : Int) (_ : IsUnit u), (Int.natAbs a : Int) = u * a := by
  rcases natAbs_eq a with h | h
  · use 1, isUnit_one
    rw [← h]; rw [one_mul]
  · use -1, isUnit_one.neg
    rw [← neg_eq_iff_eq_neg.mpr h]
    simp only [neg_mul, one_mul]

/--
theorem `gcd_eq_natAbs` / 定理 `gcd_eq_natAbs`

English:
theorem gcd_eq_natAbs
  given: {a b : Int}
  statement: Int.gcd a b = Nat.gcd a.natAbs b.natAbs
  proof: rfl

中文:
定理 gcd_eq_natAbs
  条件: {a b : 整数}
  结论: 整数.最大公约数 a b = 自然数.最大公约数 a.natAbs b.natAbs
  证明: rfl
-/
theorem gcd_eq_natAbs {a b : Int} : Int.gcd a b = Nat.gcd a.natAbs b.natAbs :=
  rfl
end Int

/--
Definition of `associatesIntEquivNat` / `associatesIntEquivNat` 的定义

English:
definition associatesIntEquivNat
  signature: : Associates Int ≃ Nat
  body: by
  refine ⟨(·.out.natAbs), (Associates.mk ·), ?_, fun n => ?_⟩
  · refine Associates.forall_associated.2 fun a => ?_
refine Associates.mk_eq_mk_iff_associated.2 Associated.symm ⟨normUnit a, ?_⟩
    simp [Int.natCast_natAbs, Int.abs_eq_normalize, normalize_apply]
  · dsimp only [Associates.out_mk]
    rw [← Int.abs_eq_normalize]; rw [Int.natAbs_abs]; rw [Int.natAbs_natCast]

中文:
定义 associates整数Equiv自然数
  签名: : Associates 整数 ≃ 自然数
  定义体: by
  refine ⟨(·.out.natAbs), (Associates.mk ·), ?_, fun n => ?_⟩
  · refine Associates.forall_associated.2 fun a => ?_
refine Associates.mk_eq_mk_iff_associated.2 Associated.symm ⟨normUnit a, ?_⟩
    simp [Int.natCast_natAbs, Int.abs_eq_normalize, normalize_apply]
  · dsimp only [Associates.out_mk]
    rw [← Int.abs_eq_normalize]; rw [Int.natAbs_abs]; rw [Int.natAbs_natCast]

Depends on / 依赖: Associated, Associated.symm, Associates, Associates.forall_associated, Associates.mk, Associates.mk_eq_mk_iff_associated, Associates.out_mk, Int.abs_eq_normalize, Int.natAbs_abs, Int.natAbs_natCast, Int.natCast_natAbs, abs_eq_normalize, forall_associated, mk_eq_mk_iff_associated, natAbs, natAbs_abs, natAbs_natCast, natCast_natAbs, normUnit, normalize_apply
-/
def associatesIntEquivNat : Associates Int ≃ Nat := by
  refine ⟨(·.out.natAbs), (Associates.mk ·), ?_, fun n => ?_⟩
  · refine Associates.forall_associated.2 fun a => ?_
refine Associates.mk_eq_mk_iff_associated.2 Associated.symm ⟨normUnit a, ?_⟩
    simp [Int.natCast_natAbs, Int.abs_eq_normalize, normalize_apply]
  · dsimp only [Associates.out_mk]
    rw [← Int.abs_eq_normalize]; rw [Int.natAbs_abs]; rw [Int.natAbs_natCast]

/--
theorem `Int.associated_natAbs` / 定理 `Int.associated_natAbs`

English:
theorem Int.associated_natAbs
  given: (k : Int)
  statement: Associated k k.natAbs
  proof: associated_of_dvd_dvd (Int.dvd_natCast.mpr dvd_rfl) (Int.natAbs_dvd.mpr dvd_rfl)

中文:
定理 整数.associated_natAbs
  条件: (k : 整数)
  结论: Associated k k.natAbs
  证明: associated_of_dvd_dvd (Int.dvd_natCast.mpr dvd_rfl) (Int.natAbs_dvd.mpr dvd_rfl)

Depends on / 依赖: Int.dvd_natCast.mpr, Int.natAbs_dvd.mpr, associated_of_dvd_dvd, dvd_natCast, dvd_rfl, natAbs_dvd
-/
theorem Int.associated_natAbs (k : Int) : Associated k k.natAbs :=
  associated_of_dvd_dvd (Int.dvd_natCast.mpr dvd_rfl) (Int.natAbs_dvd.mpr dvd_rfl)

/--
theorem `Int.associated_iff_natAbs` / 定理 `Int.associated_iff_natAbs`

English:
theorem Int.associated_iff_natAbs
  given: {a b : Int}
  statement: Associated a b ↔ a.natAbs = b.natAbs
  proof: by
  rw [← dvd_dvd_iff_associated]; rw [← Int.natAbs_dvd_natAbs]; rw [← Int.natAbs_dvd_natAbs]; rw [dvd_dvd_iff_associated]
  exact associated_iff_eq

中文:
定理 整数.associated_iff_natAbs
  条件: {a b : 整数}
  结论: Associated a b ↔ a.natAbs = b.natAbs
  证明: by
  rw [← dvd_dvd_iff_associated]; rw [← Int.natAbs_dvd_natAbs]; rw [← Int.natAbs_dvd_natAbs]; rw [dvd_dvd_iff_associated]
  exact associated_iff_eq

Depends on / 依赖: Int.natAbs_dvd_natAbs, associated_iff_eq, dvd_dvd_iff_associated, natAbs_dvd_natAbs
-/
theorem Int.associated_iff_natAbs {a b : Int} : Associated a b ↔ a.natAbs = b.natAbs := by
  rw [← dvd_dvd_iff_associated]; rw [← Int.natAbs_dvd_natAbs]; rw [← Int.natAbs_dvd_natAbs]; rw [dvd_dvd_iff_associated]
  exact associated_iff_eq

/--
theorem `Int.associated_iff` / 定理 `Int.associated_iff`

English:
theorem Int.associated_iff
  given: {a b : Int}
  statement: Associated a b ↔ a = b ∨ a = -b
  proof: by
  rw [Int.associated_iff_natAbs]
  exact Int.natAbs_eq_natAbs_iff

中文:
定理 整数.associated_iff
  条件: {a b : 整数}
  结论: Associated a b ↔ a = b ∨ a = -b
  证明: by
  rw [Int.associated_iff_natAbs]
  exact Int.natAbs_eq_natAbs_iff

Depends on / 依赖: Int.associated_iff_natAbs, Int.natAbs_eq_natAbs_iff, associated_iff_natAbs, natAbs_eq_natAbs_iff
-/
theorem Int.associated_iff {a b : Int} : Associated a b ↔ a = b ∨ a = -b := by
  rw [Int.associated_iff_natAbs]
  exact Int.natAbs_eq_natAbs_iff
