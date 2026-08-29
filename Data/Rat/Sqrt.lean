/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Order.Ring.Unbundled.Rat
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Data.Int.Sqrt

/-!
# Square root on rational numbers

This file defines the square root function on rational numbers `Rat.sqrt`
and proves several theorems about it.

-/

@[expose] public section


namespace Rat

/-- Square root function on rational numbers, defined by taking the (integer) square root of the
numerator and the square root (on natural numbers) of the denominator. -/
@[pp_nodot]
/--
Definition of `sqrt` / `sqrt` 的定义

English:
definition sqrt
  signature: (q : Rat)
  body: mkRat (Int.sqrt q.num) (Nat.sqrt q.den)

中文:
定义 sqrt
  签名: (q : Rat)
  定义体: mkRat (Int.sqrt q.num) (Nat.sqrt q.den)

Depends on / 依赖: Int.sqrt, Nat.sqrt, q.den, q.num
-/
def sqrt (q : Rat) : Rat := mkRat (Int.sqrt q.num) (Nat.sqrt q.den)

/--
theorem `sqrt_eq` / 定理 `sqrt_eq`

English:
theorem sqrt_eq
  given: (q : Rat)
  statement: Rat.sqrt (q * q) = |q|
  proof: by
  rw [sqrt]; rw [mul_self_num]; rw [mul_self_den]; rw [Int.sqrt_eq]; rw [Nat.sqrt_eq]; rw [abs_def]; rw [divInt_ofNat]

中文:
定理 sqrt_eq
  条件: (q : Rat)
  结论: Rat.sqrt (q * q) = |q|
  证明: by
  rw [sqrt]; rw [mul_self_num]; rw [mul_self_den]; rw [Int.sqrt_eq]; rw [Nat.sqrt_eq]; rw [abs_def]; rw [divInt_ofNat]

Depends on / 依赖: Int.sqrt_eq, Nat.sqrt_eq, abs_def, divInt_ofNat, mul_self_den, mul_self_num, sqrt_eq
-/
theorem sqrt_eq (q : Rat) : Rat.sqrt (q * q) = |q| := by
  rw [sqrt]; rw [mul_self_num]; rw [mul_self_den]; rw [Int.sqrt_eq]; rw [Nat.sqrt_eq]; rw [abs_def]; rw [divInt_ofNat]

/--
theorem `exists_mul_self` / 定理 `exists_mul_self`

English:
theorem exists_mul_self
  given: (x : Rat)
  statement: (exists q, q * q = x) ↔ Rat.sqrt x * Rat.sqrt x = x
  proof: ⟨fun ⟨n, hn⟩ => by rw [← hn, sqrt_eq, abs_mul_abs_self], fun h => ⟨Rat.sqrt x, h⟩⟩

中文:
定理 exists_mul_self
  条件: (x : Rat)
  结论: (存在 q, q * q = x) ↔ Rat.sqrt x * Rat.sqrt x = x
  证明: ⟨fun ⟨n, hn⟩ => by rw [← hn, sqrt_eq, abs_mul_abs_self], fun h => ⟨Rat.sqrt x, h⟩⟩

Depends on / 依赖: Rat.sqrt, abs_mul_abs_self, sqrt_eq
-/
theorem exists_mul_self (x : Rat) : (exists q, q * q = x) ↔ Rat.sqrt x * Rat.sqrt x = x :=
  ⟨fun ⟨n, hn⟩ => by rw [← hn, sqrt_eq, abs_mul_abs_self], fun h => ⟨Rat.sqrt x, h⟩⟩

/--
lemma `sqrt_nonneg` / 引理 `sqrt_nonneg`

English:
lemma sqrt_nonneg
  given: (q : Rat)
  statement: 0 <= Rat.sqrt q
  proof: mkRat_nonneg (Int.sqrt_nonneg _) _

中文:
引理 sqrt_nonneg
  条件: (q : Rat)
  结论: 0 <= Rat.sqrt q
  证明: mkRat_nonneg (Int.sqrt_nonneg _) _

Depends on / 依赖: Int.sqrt_nonneg, mkRat_nonneg, sqrt_nonneg
-/
lemma sqrt_nonneg (q : Rat) : 0 <= Rat.sqrt q := mkRat_nonneg (Int.sqrt_nonneg _) _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DecidablePred (IsSquare : Rat -> Prop)
  body: fun m => decidable_of_iff' (sqrt m * sqrt m = m) by
    simp_rw [← exists_mul_self m, IsSquare, eq_comm]

@[simp, norm_cast]

中文:
实例 :
  签名: DecidablePred (IsSquare : Rat -> 命题)
  定义体: fun m => decidable_of_iff' (sqrt m * sqrt m = m) by
    simp_rw [← exists_mul_self m, IsSquare, eq_comm]

@[simp, norm_cast]

Depends on / 依赖: IsSquare, decidable_of_iff, eq_comm, exists_mul_self, simp_rw
-/
instance : DecidablePred (IsSquare : Rat -> Prop) :=
fun m => decidable_of_iff' (sqrt m * sqrt m = m) by
    simp_rw [← exists_mul_self m, IsSquare, eq_comm]

@[simp, norm_cast]
/--
theorem `sqrt_intCast` / 定理 `sqrt_intCast`

English:
theorem sqrt_intCast
  given: (z : Int)
  statement: Rat.sqrt (z : Rat) = Int.sqrt z
  proof: by
  simp only [sqrt, num_intCast, den_intCast, Nat.sqrt_one, mkRat_one]

@[simp, norm_cast]

中文:
定理 sqrt_intCast
  条件: (z : 整数)
  结论: Rat.sqrt (z : Rat) = 整数.sqrt z
  证明: by
  simp only [sqrt, num_intCast, den_intCast, Nat.sqrt_one, mkRat_one]

@[simp, norm_cast]

Depends on / 依赖: Nat.sqrt_one, den_intCast, mkRat_one, num_intCast, sqrt_one
-/
theorem sqrt_intCast (z : Int) : Rat.sqrt (z : Rat) = Int.sqrt z := by
  simp only [sqrt, num_intCast, den_intCast, Nat.sqrt_one, mkRat_one]

@[simp, norm_cast]
/--
theorem `sqrt_natCast` / 定理 `sqrt_natCast`

English:
theorem sqrt_natCast
  given: (n : Nat)
  statement: Rat.sqrt (n : Rat) = Nat.sqrt n
  proof: by
  rw [← Int.cast_natCast]; rw [sqrt_intCast]; rw [Int.sqrt_natCast]; rw [Int.cast_natCast]

@[simp]

中文:
定理 sqrt_natCast
  条件: (n : 自然数)
  结论: Rat.sqrt (n : Rat) = 自然数.sqrt n
  证明: by
  rw [← Int.cast_natCast]; rw [sqrt_intCast]; rw [Int.sqrt_natCast]; rw [Int.cast_natCast]

@[simp]

Depends on / 依赖: Int.cast_natCast, Int.sqrt_natCast, cast_natCast, sqrt_intCast, sqrt_natCast
-/
theorem sqrt_natCast (n : Nat) : Rat.sqrt (n : Rat) = Nat.sqrt n := by
  rw [← Int.cast_natCast]; rw [sqrt_intCast]; rw [Int.sqrt_natCast]; rw [Int.cast_natCast]

@[simp]
/--
theorem `sqrt_ofNat` / 定理 `sqrt_ofNat`

English:
theorem sqrt_ofNat
  given: (n : Nat)
  statement: Rat.sqrt (ofNat(n) : Rat) = Nat.sqrt (OfNat.ofNat n)
  proof: sqrt_natCast _

中文:
定理 sqrt_ofNat
  条件: (n : 自然数)
  结论: Rat.sqrt (of自然数(n) : Rat) = 自然数.sqrt (Of自然数.of自然数 n)
  证明: sqrt_natCast _

Depends on / 依赖: sqrt_natCast
-/
theorem sqrt_ofNat (n : Nat) : Rat.sqrt (ofNat(n) : Rat) = Nat.sqrt (OfNat.ofNat n) :=
  sqrt_natCast _

end Rat
