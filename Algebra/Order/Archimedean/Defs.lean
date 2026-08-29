/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Order.Ring.Defs

import Mathlib.Algebra.Order.Group.OrderIso
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow

/-!
# Definitions of Archimedean monoids

This file defines the archimedean property for ordered monoids.

## Main definitions

* `Archimedean` is a typeclass for an ordered additive commutative monoid to have the archimedean
  property.
* `MulArchimedean` is a typeclass for an ordered commutative monoid to have the "mul-archimedean
  property" where for `x` and `y > 1`, there exists a natural number `n` such that `x ≤ y ^ n`.
-/

public section

variable {R : Type*}

/--
Definition of `Archimedean` / `Archimedean` 的定义

English:
class Archimedean
  parameters: (R) [AddCommMonoid R] [PartialOrder R]
  axioms and operations (1):
    - arch : forall (x : R) {y : R}, 0 < y -> exists n : Nat, x <= n • y

中文:
类 Archimedean
  参数: (R) [AddCommMonoid R] [PartialOrder R]
  公理与运算 (1 个):
    - arch : 对任意 (x : R) {y : R}, 0 < y -> 存在 n : 自然数, x <= n • y
-/
class Archimedean (R) [AddCommMonoid R] [PartialOrder R] : Prop where
  /-- For any two elements `x`, `y` such that `0 < y`, there exists a natural number `n`
  such that `x ≤ n • y`. -/
  arch : forall (x : R) {y : R}, 0 < y -> exists n : Nat, x <= n • y

/-- An ordered commutative monoid is called `MulArchimedean` if for any two elements `x`, `y`
such that `1 < y`, there exists a natural number `n` such that `x ≤ y ^ n`. -/
@[to_additive Archimedean]
/--
Definition of `MulArchimedean` / `MulArchimedean` 的定义

English:
class MulArchimedean
  parameters: (R) [CommMonoid R] [PartialOrder R]
  axioms and operations (1):
    - arch : forall (x : R) {y : R}, 1 < y -> exists n : Nat, x <= y ^ n

中文:
类 MulArchimedean
  参数: (R) [CommMonoid R] [PartialOrder R]
  公理与运算 (1 个):
    - arch : 对任意 (x : R) {y : R}, 1 < y -> 存在 n : 自然数, x <= y ^ n
-/
class MulArchimedean (R) [CommMonoid R] [PartialOrder R] : Prop where
  /-- For any two elements `x`, `y` such that `1 < y`, there exists a natural number `n`
  such that `x ≤ y ^ n`. -/
  arch : forall (x : R) {y : R}, 1 < y -> exists n : Nat, x <= y ^ n

section OrderedMonoid
variable [CommMonoid R] [PartialOrder R] [MulLeftStrictMono R] [MulArchimedean R]

@[to_additive]
/--
theorem `exists_lt_pow` / 定理 `exists_lt_pow`

English:
theorem exists_lt_pow
  given: {a : R} (ha : 1 < a) (b : R)
  statement: exists n : Nat, b < a ^ n
  proof: let ⟨k, hk⟩ := MulArchimedean.arch b ha
⟨k + 1, hk.trans_lt pow_lt_pow_right' ha k.lt_succ_self⟩

中文:
定理 exists_lt_pow
  条件: {a : R} (ha : 1 < a) (b : R)
  结论: 存在 n : 自然数, b < a ^ n
  证明: let ⟨k, hk⟩ := MulArchimedean.arch b ha
⟨k + 1, hk.trans_lt pow_lt_pow_right' ha k.lt_succ_self⟩

Depends on / 依赖: MulArchimedean, MulArchimedean.arch, hk.trans_lt, k.lt_succ_self, lt_succ_self, pow_lt_pow_right, trans_lt
-/
theorem exists_lt_pow {a : R} (ha : 1 < a) (b : R) : exists n : Nat, b < a ^ n :=
  let ⟨k, hk⟩ := MulArchimedean.arch b ha
⟨k + 1, hk.trans_lt pow_lt_pow_right' ha k.lt_succ_self⟩

end OrderedMonoid

section OrderedGroup
variable [CommGroup R] [LinearOrder R] [IsOrderedMonoid R] [MulArchimedean R]

@[to_additive]
/--
theorem `exists_pow_lt` / 定理 `exists_pow_lt`

English:
theorem exists_pow_lt
  given: {a : R} (ha : a < 1) (b : R)
  statement: exists n : Nat, a ^ n < b
  proof: (exists_lt_pow (one_lt_inv'.mpr ha) b⁻¹).imp by simp

中文:
定理 exists_pow_lt
  条件: {a : R} (ha : a < 1) (b : R)
  结论: 存在 n : 自然数, a ^ n < b
  证明: (exists_lt_pow (one_lt_inv'.mpr ha) b⁻¹).imp by simp

Depends on / 依赖: exists_lt_pow, one_lt_inv
-/
theorem exists_pow_lt {a : R} (ha : a < 1) (b : R) : exists n : Nat, a ^ n < b :=
(exists_lt_pow (one_lt_inv'.mpr ha) b⁻¹).imp by simp

end OrderedGroup

section OrderedSemiring
variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [Archimedean R]

/--
theorem `exists_nat_ge` / 定理 `exists_nat_ge`

English:
theorem exists_nat_ge
  given: (x : R)
  statement: exists n : Nat, x <= n
  proof: by
  nontriviality R
  exact (Archimedean.arch x one_pos).imp fun n h => by rwa [← nsmul_one]

中文:
定理 exists_nat_ge
  条件: (x : R)
  结论: 存在 n : 自然数, x <= n
  证明: by
  nontriviality R
  exact (Archimedean.arch x one_pos).imp fun n h => by rwa [← nsmul_one]

Depends on / 依赖: Archimedean, Archimedean.arch, nontriviality, nsmul_one, one_pos
-/
theorem exists_nat_ge (x : R) : exists n : Nat, x <= n := by
  nontriviality R
  exact (Archimedean.arch x one_pos).imp fun n h => by rwa [← nsmul_one]

end OrderedSemiring

section StrictOrderedSemiring
variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] [Archimedean R] {y : R}

/--
theorem `exists_nat_gt` / 定理 `exists_nat_gt`

English:
theorem exists_nat_gt
  given: (x : R)
  statement: exists n : Nat, x < n
  proof: (exists_lt_nsmul zero_lt_one x).imp fun n hn => by rwa [← nsmul_one]

中文:
定理 exists_nat_gt
  条件: (x : R)
  结论: 存在 n : 自然数, x < n
  证明: (exists_lt_nsmul zero_lt_one x).imp fun n hn => by rwa [← nsmul_one]

Depends on / 依赖: exists_lt_nsmul, nsmul_one, zero_lt_one
-/
theorem exists_nat_gt (x : R) : exists n : Nat, x < n :=
  (exists_lt_nsmul zero_lt_one x).imp fun n hn => by rwa [← nsmul_one]

end StrictOrderedSemiring

section OrderedRing
variable [Ring R] [PartialOrder R] [IsOrderedRing R] [Archimedean R]

/--
theorem `exists_int_ge` / 定理 `exists_int_ge`

English:
theorem exists_int_ge
  given: (x : R)
  statement: exists n : Int, x <= n
  proof: let ⟨n, h⟩ := exists_nat_ge x; ⟨n, mod_cast h⟩

中文:
定理 exists_int_ge
  条件: (x : R)
  结论: 存在 n : 整数, x <= n
  证明: let ⟨n, h⟩ := exists_nat_ge x; ⟨n, mod_cast h⟩

Depends on / 依赖: exists_nat_ge, mod_cast
-/
theorem exists_int_ge (x : R) : exists n : Int, x <= n := let ⟨n, h⟩ := exists_nat_ge x; ⟨n, mod_cast h⟩

/--
theorem `exists_int_le` / 定理 `exists_int_le`

English:
theorem exists_int_le
  given: (x : R)
  statement: exists n : Int, n <= x
  proof: let ⟨n, h⟩ := exists_int_ge (-x); ⟨-n, by simpa [neg_le] using h⟩

中文:
定理 exists_int_le
  条件: (x : R)
  结论: 存在 n : 整数, n <= x
  证明: let ⟨n, h⟩ := exists_int_ge (-x); ⟨-n, by simpa [neg_le] using h⟩

Depends on / 依赖: exists_int_ge, neg_le
-/
theorem exists_int_le (x : R) : exists n : Int, n <= x :=
  let ⟨n, h⟩ := exists_int_ge (-x); ⟨-n, by simpa [neg_le] using h⟩

end OrderedRing

section StrictOrderedRing
variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R] [Archimedean R]

/--
theorem `exists_int_gt` / 定理 `exists_int_gt`

English:
theorem exists_int_gt
  given: (x : R)
  statement: exists n : Int, x < n
  proof: let ⟨n, h⟩ := exists_nat_gt x
  ⟨n, by rwa [Int.cast_natCast]⟩

中文:
定理 exists_int_gt
  条件: (x : R)
  结论: 存在 n : 整数, x < n
  证明: let ⟨n, h⟩ := exists_nat_gt x
  ⟨n, by rwa [Int.cast_natCast]⟩

Depends on / 依赖: Int.cast_natCast, cast_natCast, exists_nat_gt
-/
theorem exists_int_gt (x : R) : exists n : Int, x < n :=
  let ⟨n, h⟩ := exists_nat_gt x
  ⟨n, by rwa [Int.cast_natCast]⟩

/--
theorem `exists_int_lt` / 定理 `exists_int_lt`

English:
theorem exists_int_lt
  given: (x : R)
  statement: exists n : Int, (n : R) < x
  proof: let ⟨n, h⟩ := exists_int_gt (-x)
  ⟨-n, by rw [Int.cast_neg]; exact neg_lt.1 h⟩

中文:
定理 exists_int_lt
  条件: (x : R)
  结论: 存在 n : 整数, (n : R) < x
  证明: let ⟨n, h⟩ := exists_int_gt (-x)
  ⟨-n, by rw [Int.cast_neg]; exact neg_lt.1 h⟩

Depends on / 依赖: Int.cast_neg, cast_neg, exists_int_gt, neg_lt
-/
theorem exists_int_lt (x : R) : exists n : Int, (n : R) < x :=
  let ⟨n, h⟩ := exists_int_gt (-x)
  ⟨-n, by rw [Int.cast_neg]; exact neg_lt.1 h⟩

end StrictOrderedRing
