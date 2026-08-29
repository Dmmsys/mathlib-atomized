/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

public import Mathlib.Algebra.Group.Defs

/-!
# The natural numbers form a monoid

This file contains the additive and multiplicative monoid instances on the natural numbers.

See note [foundational algebra order theory].
-/

public section

assert_not_exists MonoidWithZero DenselyOrdered

namespace Nat


/--
Instance `instMulOneClass` / 实例 `instMulOneClass`

English:
instance instMulOneClass
  signature: : MulOneClass Nat where
  body: Nat.one_mul
  mul_one := Nat.mul_one

中文:
实例 instMulOneClass
  签名: : MulOne类 自然数 where
  定义体: Nat.one_mul
  mul_one := Nat.mul_one

Depends on / 依赖: Nat.one_mul, one_mul
-/
instance instMulOneClass : MulOneClass Nat where
  one_mul := Nat.one_mul
  mul_one := Nat.mul_one

/--
Instance `instAddCancelCommMonoid` / 实例 `instAddCancelCommMonoid`

English:
instance instAddCancelCommMonoid
  signature: : AddCancelCommMonoid Nat where
  body: Nat.add
  add_assoc := Nat.add_assoc
  zero := Nat.zero
  zero_add := Nat.zero_add
  add_zero := Nat.add_zero
  add_comm := Nat.add_comm
  nsmul m n := m * n
  nsmul_zero := Nat.zero_mul
  nsmul_succ := succ_mul
  add_left_cancel _ _ _ := Nat.add_left_cancel

中文:
实例 instAddCancelCommMonoid
  签名: : 加法消去交换幺半群 自然数 where
  定义体: Nat.add
  add_assoc := Nat.add_assoc
  zero := Nat.zero
  zero_add := Nat.zero_add
  add_zero := Nat.add_zero
  add_comm := Nat.add_comm
  nsmul m n := m * n
  nsmul_zero := Nat.zero_mul
  nsmul_succ := succ_mul
  add_left_cancel _ _ _ := Nat.add_left_cancel

Depends on / 依赖: Nat.add
-/
instance instAddCancelCommMonoid : AddCancelCommMonoid Nat where
  add := Nat.add
  add_assoc := Nat.add_assoc
  zero := Nat.zero
  zero_add := Nat.zero_add
  add_zero := Nat.add_zero
  add_comm := Nat.add_comm
  nsmul m n := m * n
  nsmul_zero := Nat.zero_mul
  nsmul_succ := succ_mul
  add_left_cancel _ _ _ := Nat.add_left_cancel

/--
Instance `instCommMonoid` / 实例 `instCommMonoid`

English:
instance instCommMonoid
  signature: : CommMonoid Nat where
  body: Nat.mul
  mul_assoc := Nat.mul_assoc
  one := Nat.succ Nat.zero
  one_mul := Nat.one_mul
  mul_one := Nat.mul_one
  mul_comm := Nat.mul_comm
  npow m n := n ^ m
  npow_zero := Nat.pow_zero
  npow_succ _ _ := rfl

中文:
实例 instCommMonoid
  签名: : 交换幺半群 自然数 where
  定义体: Nat.mul
  mul_assoc := Nat.mul_assoc
  one := Nat.succ Nat.zero
  one_mul := Nat.one_mul
  mul_one := Nat.mul_one
  mul_comm := Nat.mul_comm
  npow m n := n ^ m
  npow_zero := Nat.pow_zero
  npow_succ _ _ := rfl

Depends on / 依赖: Nat.mul
-/
instance instCommMonoid : CommMonoid Nat where
  mul := Nat.mul
  mul_assoc := Nat.mul_assoc
  one := Nat.succ Nat.zero
  one_mul := Nat.one_mul
  mul_one := Nat.mul_one
  mul_comm := Nat.mul_comm
  npow m n := n ^ m
  npow_zero := Nat.pow_zero
  npow_succ _ _ := rfl

-- These instances can also be found from the `LinearOrderedCommMonoidWithZero ℕ` instance by
-- typeclass search, but it is better practice to not rely on algebraic order theory to prove
-- purely algebraic results on concrete types. Eg the results can be made available earlier.

/--
Instance `instIsMulTorsionFree` / 实例 `instIsMulTorsionFree`

English:
instance instIsMulTorsionFree
  signature: : IsMulTorsionFree Nat where
  body: (Nat.pow_left_inj h).mp

中文:
实例 instIsMulTorsionFree
  签名: : 是MulTorsionFree 自然数 where
  定义体: (Nat.pow_left_inj h).mp

Depends on / 依赖: Nat.pow_left_inj, pow_left_inj
-/
instance instIsMulTorsionFree : IsMulTorsionFree Nat where
  pow_left_injective _ h _ _ := (Nat.pow_left_inj h).mp

/--
Instance `instIsAddTorsionFree` / 实例 `instIsAddTorsionFree`

English:
instance instIsAddTorsionFree
  signature: : IsAddTorsionFree Nat where
  body: Nat.mul_left_cancel (Nat.pos_of_ne_zero hn) hxy

中文:
实例 instIsAddTorsionFree
  签名: : 是加法无挠 自然数 where
  定义体: Nat.mul_left_cancel (Nat.pos_of_ne_zero hn) hxy

Depends on / 依赖: Nat.mul_left_cancel, Nat.pos_of_ne_zero, mul_left_cancel, pos_of_ne_zero
-/
instance instIsAddTorsionFree : IsAddTorsionFree Nat where
  nsmul_right_injective _n hn _x _y hxy := Nat.mul_left_cancel (Nat.pos_of_ne_zero hn) hxy

/-!
### Extra instances to short-circuit type class resolution

These also prevent non-computable instances being used to construct these instances non-computably.
-/

set_option linter.style.whitespace false -- manual alignment is not recognised

/--
Instance `instAddCommMonoid` / 实例 `instAddCommMonoid`

English:
instance instAddCommMonoid
  signature: : AddCommMonoid Nat
  body: by infer_instance

中文:
实例 instAddCommMonoid
  签名: : 加法交换幺半群 自然数
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance instAddCommMonoid : AddCommMonoid Nat := by infer_instance
/--
Instance `instAddMonoid` / 实例 `instAddMonoid`

English:
instance instAddMonoid
  signature: : AddMonoid Nat
  body: by infer_instance

中文:
实例 instAddMonoid
  签名: : 加法幺半群 自然数
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance instAddMonoid : AddMonoid Nat := by infer_instance
/--
Instance `instMonoid` / 实例 `instMonoid`

English:
instance instMonoid
  signature: : Monoid Nat
  body: by infer_instance

中文:
实例 instMonoid
  签名: : 幺半群 自然数
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance instMonoid : Monoid Nat := by infer_instance
/--
Instance `instCommSemigroup` / 实例 `instCommSemigroup`

English:
instance instCommSemigroup
  signature: : CommSemigroup Nat
  body: by infer_instance

中文:
实例 instCommSemigroup
  签名: : 交换半群 自然数
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance instCommSemigroup : CommSemigroup Nat := by infer_instance
/--
Instance `instSemigroup` / 实例 `instSemigroup`

English:
instance instSemigroup
  signature: : Semigroup Nat
  body: by infer_instance

中文:
实例 instSemigroup
  签名: : 半群 自然数
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance instSemigroup : Semigroup Nat := by infer_instance
/--
Instance `instAddCommSemigroup` / 实例 `instAddCommSemigroup`

English:
instance instAddCommSemigroup
  signature: : AddCommSemigroup Nat
  body: by infer_instance

中文:
实例 instAddCommSemigroup
  签名: : 加法交换半群 自然数
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance instAddCommSemigroup : AddCommSemigroup Nat := by infer_instance
/--
Instance `instAddSemigroup` / 实例 `instAddSemigroup`

English:
instance instAddSemigroup
  signature: : AddSemigroup Nat
  body: by infer_instance

中文:
实例 instAddSemigroup
  签名: : 加法半群 自然数
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance instAddSemigroup : AddSemigroup Nat := by infer_instance
/--
Instance `instOne` / 实例 `instOne`

English:
instance instOne
  signature: : One Nat
  body: inferInstance

中文:
实例 instOne
  签名: : 幺 自然数
  定义体: inferInstance
-/
instance instOne : One Nat := inferInstance

set_option linter.style.whitespace true


-- We set the simp priority slightly lower than default; later more general lemmas will replace it.
/--
lemma `nsmul_eq_mul` / 引理 `nsmul_eq_mul`

English:
lemma nsmul_eq_mul
  given: (m n : Nat)
  statement: m • n = m * n
  proof: rfl

中文:
引理 nsmul_eq_mul
  条件: (m n : 自然数)
  结论: m • n = m * n
  证明: rfl
-/
@[simp 900] protected lemma nsmul_eq_mul (m n : Nat) : m • n = m * n := rfl

end Nat
