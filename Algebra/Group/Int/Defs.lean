/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
module

public import Mathlib.Algebra.Group.Defs

/-!
# The integers form a group

This file contains the additive group and multiplicative monoid instances on the integers.

See note [foundational algebra order theory].
-/

public section

assert_not_exists Ring DenselyOrdered

open Nat

namespace Int


/--
Instance `instCommMonoid` / 实例 `instCommMonoid`

English:
instance instCommMonoid
  signature: : CommMonoid Int where
  body: Int.mul_comm
  mul_one := Int.mul_one
  one_mul := Int.one_mul
  npow n x := x ^ n
  npow_zero _ := by simp [Int.pow_zero]
  npow_succ _ _ := by simp [Int.pow_succ]
  mul_assoc := Int.mul_assoc

中文:
实例 instCommMonoid
  签名: : CommMonoid 整数 where
  定义体: Int.mul_comm
  mul_one := Int.mul_one
  one_mul := Int.one_mul
  npow n x := x ^ n
  npow_zero _ := by simp [Int.pow_zero]
  npow_succ _ _ := by simp [Int.pow_succ]
  mul_assoc := Int.mul_assoc

Depends on / 依赖: Int.mul_comm, mul_comm
-/
instance instCommMonoid : CommMonoid Int where
  mul_comm := Int.mul_comm
  mul_one := Int.mul_one
  one_mul := Int.one_mul
  npow n x := x ^ n
  npow_zero _ := by simp [Int.pow_zero]
  npow_succ _ _ := by simp [Int.pow_succ]
  mul_assoc := Int.mul_assoc

/--
Instance `instAddCommGroup` / 实例 `instAddCommGroup`

English:
instance instAddCommGroup
  signature: : AddCommGroup Int where
  body: Int.add_comm
  add_assoc := Int.add_assoc
  add_zero := Int.add_zero
  zero_add := Int.zero_add
  neg_add_cancel := Int.add_left_neg
  nsmul := (· * ·)
  nsmul_zero := Int.zero_mul
  nsmul_succ n x :=
    show (n + 1 : Int) * x = n * x + x by rw [Int.add_mul, Int.one_mul]
  zsmul := (· * ·)
  zsmul_

中文:
实例 instAddCommGroup
  签名: : AddCommGroup 整数 where
  定义体: Int.add_comm
  add_assoc := Int.add_assoc
  add_zero := Int.add_zero
  zero_add := Int.zero_add
  neg_add_cancel := Int.add_left_neg
  nsmul := (· * ·)
  nsmul_zero := Int.zero_mul
  nsmul_succ n x :=
    show (n + 1 : Int) * x = n * x + x by rw [Int.add_mul, Int.one_mul]
  zsmul := (· * ·)
  zsmul_

Depends on / 依赖: Int.add_comm, add_comm
-/
instance instAddCommGroup : AddCommGroup Int where
  add_comm := Int.add_comm
  add_assoc := Int.add_assoc
  add_zero := Int.add_zero
  zero_add := Int.zero_add
  neg_add_cancel := Int.add_left_neg
  nsmul := (· * ·)
  nsmul_zero := Int.zero_mul
  nsmul_succ n x :=
    show (n + 1 : Int) * x = n * x + x by rw [Int.add_mul, Int.one_mul]
  zsmul := (· * ·)
  zsmul_zero' := Int.zero_mul
  zsmul_succ' m n := by
    simp only [HSMul.hSMul, SMul.smul, natCast_succ, Int.add_mul, Int.add_comm, Int.one_mul]
  zsmul_neg' m n := by simp only [HSMul.hSMul, SMul.smul, negSucc_eq, natCast_succ, Int.neg_mul]
  sub_eq_add_neg _ _ := Int.sub_eq_add_neg

-- This instance can also be found from the `LinearOrderedCommMonoidWithZero ℤ` instance by
-- typeclass search, but it is better practice to not rely on algebraic order theory to prove
-- purely algebraic results on concrete types. Eg the results can be made available earlier.

/--
Instance `instIsAddTorsionFree` / 实例 `instIsAddTorsionFree`

English:
instance instIsAddTorsionFree
  signature: : IsAddTorsionFree Int where
  body: Int.eq_of_mul_eq_mul_left (by lia)

中文:
实例 instIsAddTorsionFree
  签名: : IsAddTorsionFree 整数 where
  定义体: Int.eq_of_mul_eq_mul_left (by lia)

Depends on / 依赖: Int.eq_of_mul_eq_mul_left, eq_of_mul_eq_mul_left
-/
instance instIsAddTorsionFree : IsAddTorsionFree Int where
  nsmul_right_injective _n hn _x _y := Int.eq_of_mul_eq_mul_left (by lia)

/-!
### Extra instances to short-circuit type class resolution

These also prevent non-computable instances like `Int.instNormedCommRing` being used to construct
these instances non-computably.
-/

section
set_option linter.style.whitespace false -- manual alignment is not recognised

/--
Instance `instAddCommMonoid` / 实例 `instAddCommMonoid`

English:
instance instAddCommMonoid
  signature: : AddCommMonoid Int
  body: by infer_instance

中文:
实例 instAddCommMonoid
  签名: : AddCommMonoid 整数
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance instAddCommMonoid : AddCommMonoid Int := by infer_instance
/--
Instance `instAddMonoid` / 实例 `instAddMonoid`

English:
instance instAddMonoid
  signature: : AddMonoid Int
  body: by infer_instance

中文:
实例 instAddMonoid
  签名: : AddMonoid 整数
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance instAddMonoid : AddMonoid Int := by infer_instance
/--
Instance `instMonoid` / 实例 `instMonoid`

English:
instance instMonoid
  signature: : Monoid Int
  body: by infer_instance

中文:
实例 instMonoid
  签名: : Monoid 整数
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance instMonoid : Monoid Int := by infer_instance
/--
Instance `instCommSemigroup` / 实例 `instCommSemigroup`

English:
instance instCommSemigroup
  signature: : CommSemigroup Int
  body: by infer_instance

中文:
实例 instCommSemigroup
  签名: : CommSemigroup 整数
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance instCommSemigroup : CommSemigroup Int := by infer_instance
/--
Instance `instSemigroup` / 实例 `instSemigroup`

English:
instance instSemigroup
  signature: : Semigroup Int
  body: by infer_instance

中文:
实例 instSemigroup
  签名: : Semigroup 整数
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance instSemigroup : Semigroup Int := by infer_instance
/--
Instance `instAddGroup` / 实例 `instAddGroup`

English:
instance instAddGroup
  signature: : AddGroup Int
  body: by infer_instance

中文:
实例 instAddGroup
  签名: : AddGroup 整数
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance instAddGroup : AddGroup Int := by infer_instance
/--
Instance `instAddCommSemigroup` / 实例 `instAddCommSemigroup`

English:
instance instAddCommSemigroup
  signature: : AddCommSemigroup Int
  body: by infer_instance

中文:
实例 instAddCommSemigroup
  签名: : AddCommSemigroup 整数
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance instAddCommSemigroup : AddCommSemigroup Int := by infer_instance
/--
Instance `instAddSemigroup` / 实例 `instAddSemigroup`

English:
instance instAddSemigroup
  signature: : AddSemigroup Int
  body: by infer_instance

中文:
实例 instAddSemigroup
  签名: : AddSemigroup 整数
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance instAddSemigroup : AddSemigroup Int := by infer_instance

end

-- This lemma is higher priority than later `_root_.nsmul_eq_mul` so that the `simpNF` is happy
/--
lemma `nsmul_eq_mul` / 引理 `nsmul_eq_mul`

English:
lemma nsmul_eq_mul
  given: (n : Nat) (a : Int)
  statement: n • a = n * a
  proof: rfl

中文:
引理 nsmul_eq_mul
  条件: (n : 自然数) (a : 整数)
  结论: n • a = n * a
  证明: rfl
-/
@[simp high] protected lemma nsmul_eq_mul (n : Nat) (a : Int) : n • a = n * a := rfl

-- This lemma is higher priority than later `_root_.zsmul_eq_mul` so that the `simpNF` is happy
/--
lemma `zsmul_eq_mul` / 引理 `zsmul_eq_mul`

English:
lemma zsmul_eq_mul
  given: (n a : Int)
  statement: n • a = n * a
  proof: rfl

中文:
引理 zsmul_eq_mul
  条件: (n a : 整数)
  结论: n • a = n * a
  证明: rfl
-/
@[simp high] protected lemma zsmul_eq_mul (n a : Int) : n • a = n * a := rfl

end Int

@[deprecated "use `zsmul_eq_mul`" (since := "2026-01-05")]
/--
lemma `zsmul_int_int` / 引理 `zsmul_int_int`

English:
lemma zsmul_int_int
  given: (a b : Int)
  statement: a • b = a * b
  proof: rfl

@[deprecated "use `zsmul_one`" (since := "2026-01-05")]

中文:
引理 zsmul_int_int
  条件: (a b : 整数)
  结论: a • b = a * b
  证明: rfl

@[deprecated "use `zsmul_one`" (since := "2026-01-05")]
-/
lemma zsmul_int_int (a b : Int) : a • b = a * b := rfl

@[deprecated "use `zsmul_one`" (since := "2026-01-05")]
/--
lemma `zsmul_int_one` / 引理 `zsmul_int_one`

English:
lemma zsmul_int_one
  given: (n : Int)
  statement: n • (1 : Int) = n
  proof: mul_one _

中文:
引理 zsmul_int_one
  条件: (n : 整数)
  结论: n • (1 : 整数) = n
  证明: mul_one _

Depends on / 依赖: mul_one
-/
lemma zsmul_int_one (n : Int) : n • (1 : Int) = n := mul_one _
