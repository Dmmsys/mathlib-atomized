/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.Group.Nat.Defs

/-!
# The rational numbers are a commutative ring

This file contains the commutative ring instance on the rational numbers.

See note [foundational algebra order theory].
-/

public section

assert_not_exists IsOrderedMonoid Field PNat Nat.gcd_greatest

namespace Rat


/--
Instance `commRing` / 实例 `commRing`

English:
instance commRing
  signature: : CommRing Rat where
  body: addCommGroup
  __ := commMonoid
  zero_mul := Rat.zero_mul
  mul_zero := Rat.mul_zero
  left_distrib := Rat.mul_add
  right_distrib := Rat.add_mul
  intCast := fun n => n
  natCast n := Int.cast n
  natCast_zero := rfl
  natCast_succ n := by
    simp only [intCast_eq_divInt, divInt_add_divInt _ _ In

中文:
实例 commRing
  签名: : CommRing Rat where
  定义体: addCommGroup
  __ := commMonoid
  zero_mul := Rat.zero_mul
  mul_zero := Rat.mul_zero
  left_distrib := Rat.mul_add
  right_distrib := Rat.add_mul
  intCast := fun n => n
  natCast n := Int.cast n
  natCast_zero := rfl
  natCast_succ n := by
    simp only [intCast_eq_divInt, divInt_add_divInt _ _ In

Depends on / 依赖: addCommGroup
-/
instance commRing : CommRing Rat where
  __ := addCommGroup
  __ := commMonoid
  zero_mul := Rat.zero_mul
  mul_zero := Rat.mul_zero
  left_distrib := Rat.mul_add
  right_distrib := Rat.add_mul
  intCast := fun n => n
  natCast n := Int.cast n
  natCast_zero := rfl
  natCast_succ n := by
    simp only [intCast_eq_divInt, divInt_add_divInt _ _ Int.one_ne_zero Int.one_ne_zero,
      ← divInt_one_one, Int.natCast_add, Int.natCast_one, mul_one]

/--
Instance `commGroupWithZero` / 实例 `commGroupWithZero`

English:
instance commGroupWithZero
  signature: : CommGroupWithZero Rat
  body: { exists_pair_ne := ⟨0, 1, Rat.zero_ne_one⟩
    inv_zero := Rat.inv_zero
    mul_inv_cancel := Rat.mul_inv_cancel
    mul_zero := mul_zero
    zero_mul := zero_mul
    zpow z q := q ^ z
    zpow_zero' := Rat.zpow_zero
    zpow_succ' _ _ := by rw [Rat.zpow_natCast, Rat.zpow_natCast, Rat.pow_succ] }

中文:
实例 commGroupWithZero
  签名: : CommGroupWithZero Rat
  定义体: { exists_pair_ne := ⟨0, 1, Rat.zero_ne_one⟩
    inv_zero := Rat.inv_zero
    mul_inv_cancel := Rat.mul_inv_cancel
    mul_zero := mul_zero
    zero_mul := zero_mul
    zpow z q := q ^ z
    zpow_zero' := Rat.zpow_zero
    zpow_succ' _ _ := by rw [Rat.zpow_natCast, Rat.zpow_natCast, Rat.pow_succ] }

Depends on / 依赖: Rat.inv_zero, Rat.mul_inv_cancel, Rat.pow_succ, Rat.zero_ne_one, Rat.zpow_natCast, Rat.zpow_zero, exists_pair_ne, inv_zero, mul_inv_cancel, mul_zero, pow_succ, zero_mul, zero_ne_one, zpow_natCast, zpow_succ, zpow_zero
-/
instance commGroupWithZero : CommGroupWithZero Rat :=
  { exists_pair_ne := ⟨0, 1, Rat.zero_ne_one⟩
    inv_zero := Rat.inv_zero
    mul_inv_cancel := Rat.mul_inv_cancel
    mul_zero := mul_zero
    zero_mul := zero_mul
    zpow z q := q ^ z
    zpow_zero' := Rat.zpow_zero
    zpow_succ' _ _ := by rw [Rat.zpow_natCast, Rat.zpow_natCast, Rat.pow_succ] }

/--
Instance `isDomain` / 实例 `isDomain`

English:
instance isDomain
  signature: : IsDomain Rat
  body: NoZeroDivisors.to_isDomain _

中文:
实例 isDomain
  签名: : IsDomain Rat
  定义体: NoZeroDivisors.to_isDomain _

Depends on / 依赖: NoZeroDivisors, NoZeroDivisors.to_isDomain, to_isDomain
-/
instance isDomain : IsDomain Rat := NoZeroDivisors.to_isDomain _
/-- The characteristic of `ℚ` is 0. -/
@[stacks 09FS "Second part."]
/--
Instance `instCharZero` / 实例 `instCharZero`

English:
instance instCharZero
  signature: : CharZero Rat where cast_injective a b hab
  body: by simpa using congr_arg num hab

中文:
实例 instCharZero
  签名: : CharZero Rat where cast_injective a b hab
  定义体: by simpa using congr_arg num hab

Depends on / 依赖: congr_arg
-/
instance instCharZero : CharZero Rat where cast_injective a b hab := by simpa using congr_arg num hab


/--
Instance `commSemiring` / 实例 `commSemiring`

English:
instance commSemiring
  signature: : CommSemiring Rat
  body: by infer_instance

中文:
实例 commSemiring
  签名: : CommSemiring Rat
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance commSemiring : CommSemiring Rat := by infer_instance
/--
Instance `semiring` / 实例 `semiring`

English:
instance semiring
  signature: : Semiring Rat
  body: by infer_instance

中文:
实例 semiring
  签名: : Semiring Rat
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance semiring : Semiring Rat := by infer_instance


/--
lemma `divInt_div_divInt_cancel_left` / 引理 `divInt_div_divInt_cancel_left`

English:
lemma divInt_div_divInt_cancel_left
  given: {x : Int} (hx : x != 0) (n d : Int)
  proof: by
  rw [div_eq_mul_inv]; rw [inv_divInt]; rw [divInt_mul_divInt_cancel hx]

中文:
引理 divInt_div_divInt_cancel_left
  条件: {x : 整数} (hx : x != 0) (n d : 整数)
  证明: by
  rw [div_eq_mul_inv]; rw [inv_divInt]; rw [divInt_mul_divInt_cancel hx]

Depends on / 依赖: divInt_mul_divInt_cancel, div_eq_mul_inv, inv_divInt
-/
lemma divInt_div_divInt_cancel_left {x : Int} (hx : x != 0) (n d : Int) :
    n /. x / (d /. x) = n /. d := by
  rw [div_eq_mul_inv]; rw [inv_divInt]; rw [divInt_mul_divInt_cancel hx]

/--
lemma `divInt_div_divInt_cancel_right` / 引理 `divInt_div_divInt_cancel_right`

English:
lemma divInt_div_divInt_cancel_right
  given: {x : Int} (hx : x != 0) (n d : Int)
  proof: by
  rw [div_eq_mul_inv]; rw [inv_divInt]; rw [mul_comm]; rw [divInt_mul_divInt_cancel hx]

中文:
引理 divInt_div_divInt_cancel_right
  条件: {x : 整数} (hx : x != 0) (n d : 整数)
  证明: by
  rw [div_eq_mul_inv]; rw [inv_divInt]; rw [mul_comm]; rw [divInt_mul_divInt_cancel hx]

Depends on / 依赖: divInt_mul_divInt_cancel, div_eq_mul_inv, inv_divInt, mul_comm
-/
lemma divInt_div_divInt_cancel_right {x : Int} (hx : x != 0) (n d : Int) :
    x /. n / (x /. d) = d /. n := by
  rw [div_eq_mul_inv]; rw [inv_divInt]; rw [mul_comm]; rw [divInt_mul_divInt_cancel hx]

/--
lemma `num_div_den` / 引理 `num_div_den`

English:
lemma num_div_den
  given: (r : Rat)
  statement: (r.num : Rat) / (r.den : Rat) = r
  proof: by
  rw [← Int.cast_natCast]; rw [← divInt_eq_div]; rw [num_divInt_den]

中文:
引理 num_div_den
  条件: (r : Rat)
  结论: (r.num : Rat) / (r.den : Rat) = r
  证明: by
  rw [← Int.cast_natCast]; rw [← divInt_eq_div]; rw [num_divInt_den]

Depends on / 依赖: Int.cast_natCast, cast_natCast, divInt_eq_div, num_divInt_den
-/
lemma num_div_den (r : Rat) : (r.num : Rat) / (r.den : Rat) = r := by
  rw [← Int.cast_natCast]; rw [← divInt_eq_div]; rw [num_divInt_den]

/--
lemma `divInt_pow` / 引理 `divInt_pow`

English:
lemma divInt_pow
  given: (num : Nat) (den : Int) (n : Nat)
  statement: (num /. den) ^ n = num ^ n /. den ^ n
  proof: by
  simp [divInt_eq_div, div_pow]

中文:
引理 divInt_pow
  条件: (num : 自然数) (den : 整数) (n : 自然数)
  结论: (num /. den) ^ n = num ^ n /. den ^ n
  证明: by
  simp [divInt_eq_div, div_pow]
-/
@[simp] lemma divInt_pow (num : Nat) (den : Int) (n : Nat) : (num /. den) ^ n = num ^ n /. den ^ n := by
  simp [divInt_eq_div, div_pow]

/--
lemma `mkRat_pow` / 引理 `mkRat_pow`

English:
lemma mkRat_pow
  given: (num den : Nat) (n : Nat)
  statement: mkRat num den ^ n = mkRat (num ^ n) (den ^ n)
  proof: by
  rw [mkRat_eq_divInt]; rw [mkRat_eq_divInt]; rw [divInt_pow]; rw [Int.natCast_pow]

中文:
引理 mkRat_pow
  条件: (num den : 自然数) (n : 自然数)
  结论: mkRat num den ^ n = mkRat (num ^ n) (den ^ n)
  证明: by
  rw [mkRat_eq_divInt]; rw [mkRat_eq_divInt]; rw [divInt_pow]; rw [Int.natCast_pow]
-/
@[simp] lemma mkRat_pow (num den : Nat) (n : Nat) : mkRat num den ^ n = mkRat (num ^ n) (den ^ n) := by
  rw [mkRat_eq_divInt]; rw [mkRat_eq_divInt]; rw [divInt_pow]; rw [Int.natCast_pow]

/--
lemma `natCast_eq_divInt` / 引理 `natCast_eq_divInt`

English:
lemma natCast_eq_divInt
  given: (n : Nat)
  statement: ↑n = n /. 1
  proof: by rw [← Int.cast_natCast, intCast_eq_divInt]

中文:
引理 natCast_eq_divInt
  条件: (n : 自然数)
  结论: ↑n = n /. 1
  证明: by rw [← Int.cast_natCast, intCast_eq_divInt]

Depends on / 依赖: Int.cast_natCast, cast_natCast, intCast_eq_divInt
-/
lemma natCast_eq_divInt (n : Nat) : ↑n = n /. 1 := by rw [← Int.cast_natCast, intCast_eq_divInt]

/--
lemma `mul_den_eq_num` / 引理 `mul_den_eq_num`

English:
lemma mul_den_eq_num
  given: (q : Rat)
  statement: q * q.den = q.num
  proof: by
  suffices (q.num /. ↑q.den) * (↑q.den /. 1) = q.num /. 1 by simp_all
  have : (q.den : Int) != 0 := mod_cast q.den_ne_zero
  rw [divInt_mul_divInt]; rw [mul_comm (q.den : Int) 1]; rw [divInt_mul_right this]

中文:
引理 mul_den_eq_num
  条件: (q : Rat)
  结论: q * q.den = q.num
  证明: by
  suffices (q.num /. ↑q.den) * (↑q.den /. 1) = q.num /. 1 by simp_all
  have : (q.den : Int) != 0 := mod_cast q.den_ne_zero
  rw [divInt_mul_divInt]; rw [mul_comm (q.den : Int) 1]; rw [divInt_mul_right this]
-/
@[simp] lemma mul_den_eq_num (q : Rat) : q * q.den = q.num := by
  suffices (q.num /. ↑q.den) * (↑q.den /. 1) = q.num /. 1 by simp_all
  have : (q.den : Int) != 0 := mod_cast q.den_ne_zero
  rw [divInt_mul_divInt]; rw [mul_comm (q.den : Int) 1]; rw [divInt_mul_right this]

/--
lemma `den_mul_eq_num` / 引理 `den_mul_eq_num`

English:
lemma den_mul_eq_num
  given: (q : Rat)
  statement: q.den * q = q.num
  proof: by rw [mul_comm, mul_den_eq_num]

中文:
引理 den_mul_eq_num
  条件: (q : Rat)
  结论: q.den * q = q.num
  证明: by rw [mul_comm, mul_den_eq_num]
-/
@[simp] lemma den_mul_eq_num (q : Rat) : q.den * q = q.num := by rw [mul_comm, mul_den_eq_num]

end Rat
