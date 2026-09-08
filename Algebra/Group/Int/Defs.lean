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

/-! ### Instances -/

/-
**Int.instCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Int`。
形式化陈述：instCommMonoid : CommMonoid Int where mul_comm
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.mul_assoc`：∀ (a b c : ℤ), a * b * c = a * (b * c)
· 使用定理 `Int.one_mul`：∀ (a : ℤ), 1 * a = a
· 使用定理 `Int.mul_one`：∀ (a : ℤ), a * 1 = a
· 使用定理 `Int.mul_comm`：∀ (a b : ℤ), a * b = b * a

--- 原说明 ---
### Instances
-/
instance instCommMonoid : CommMonoid ℤ where
  mul_comm := Int.mul_comm
  mul_one := Int.mul_one
  one_mul := Int.one_mul
  npow n x := x ^ n
  npow_zero _ := by simp [Int.pow_zero]
  npow_succ _ _ := by simp [Int.pow_succ]
  mul_assoc := Int.mul_assoc
/-
**Int.instAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `Int`。
形式化陈述：instAddCommGroup : AddCommGroup Int where add_comm
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.add_assoc`：∀ (a b c : ℤ), a + b + c = a + (b + c)
· 使用定理 `Int.zero_add`：∀ (a : ℤ), 0 + a = a
· 使用定理 `Int.add_zero`：∀ (a : ℤ), a + 0 = a
· 使用定理 `Int.zero_mul`：∀ (a : ℤ), 0 * a = 0
· 使用定理 `Int.sub_eq_add_neg`：∀ {a b : ℤ}, a - b = a + -b
· 使用定理 `Int.add_left_neg`：∀ (a : ℤ), -a + a = 0
· 使用定理 `Int.add_comm`：∀ (a b : ℤ), a + b = b + a
-/
instance instAddCommGroup : AddCommGroup ℤ where
  add_comm := Int.add_comm
  add_assoc := Int.add_assoc
  add_zero := Int.add_zero
  zero_add := Int.zero_add
  neg_add_cancel := Int.add_left_neg
  nsmul := (· * ·)
  nsmul_zero := Int.zero_mul
  nsmul_succ n x :=
    show (n + 1 : ℤ) * x = n * x + x by rw [Int.add_mul, Int.one_mul]
  zsmul := (· * ·)
  zsmul_zero' := Int.zero_mul
  zsmul_succ' m n := by
    simp only [HSMul.hSMul, SMul.smul, natCast_succ, Int.add_mul, Int.add_comm, Int.one_mul]
  zsmul_neg' m n := by simp only [HSMul.hSMul, SMul.smul, negSucc_eq, natCast_succ, Int.neg_mul]
  sub_eq_add_neg _ _ := Int.sub_eq_add_neg

-- This instance can also be found from the `LinearOrderedCommMonoidWithZero ℤ` instance by
-- typeclass search, but it is better practice to not rely on algebraic order theory to prove
-- purely algebraic results on concrete types. Eg the results can be made available earlier.
/-
**Int.instIsAddTorsionFree** 是 Mathlib 中的一个实例，位于命名空间 `Int`。
形式化陈述：instIsAddTorsionFree : IsAddTorsionFree Int where nsmul_right_injective _n
 hn _x _y
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.eq_of_mul_eq_mul_left`：∀ {a b c : ℤ}, a ≠ 0 → a * b = a * c → b = c
-/
instance instIsAddTorsionFree : IsAddTorsionFree ℤ where
  nsmul_right_injective _n hn _x _y := Int.eq_of_mul_eq_mul_left (by lia)

/-!
### Extra instances to short-circuit type class resolution

These also prevent non-computable instances like `Int.instNormedCommRing` being used to construct
these instances non-computably.
-/

section
set_option linter.style.whitespace false -- manual alignment is not recognised

/-
**Int.instAddCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Int`。
形式化陈述：instAddCommMonoid : AddCommMonoid Int
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddCommMonoid    : AddCommMonoid ℤ    := by infer_instance
/-
**Int.instAddMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Int`。
形式化陈述：instAddMonoid : AddMonoid Int
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddMonoid        : AddMonoid ℤ        := by infer_instance
/-
**Int.instMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Int`。
形式化陈述：instMonoid : Monoid Int
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMonoid           : Monoid ℤ           := by infer_instance
/-
**Int.instCommSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `Int`。
形式化陈述：instCommSemigroup : CommSemigroup Int
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommSemigroup    : CommSemigroup ℤ    := by infer_instance
/-
**Int.instSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `Int`。
形式化陈述：instSemigroup : Semigroup Int
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSemigroup        : Semigroup ℤ        := by infer_instance
/-
**Int.instAddGroup** 是 Mathlib 中的一个实例，位于命名空间 `Int`。
形式化陈述：instAddGroup : AddGroup Int
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddGroup         : AddGroup ℤ         := by infer_instance
/-
**Int.instAddCommSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `Int`。
形式化陈述：instAddCommSemigroup : AddCommSemigroup Int
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddCommSemigroup : AddCommSemigroup ℤ := by infer_instance
/-
**Int.instAddSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `Int`。
形式化陈述：instAddSemigroup : AddSemigroup Int
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddSemigroup     : AddSemigroup ℤ     := by infer_instance

end

-- This lemma is higher priority than later `_root_.nsmul_eq_mul` so that the `simpNF` is happy
/-
**Int.nsmul_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ (n : ℕ) (a : ℤ), n • a = ↑n * a
参数：n : ℕ；a : ℤ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp high] protected lemma nsmul_eq_mul (n : ℕ) (a : ℤ) : n • a = n * a := rfl

-- This lemma is higher priority than later `_root_.zsmul_eq_mul` so that the `simpNF` is happy
/-
**Int.zsmul_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ (n a : ℤ), n • a = n * a
参数：n a : ℤ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp high] protected lemma zsmul_eq_mul (n a : ℤ) : n • a = n * a := rfl

end Int

@[deprecated "use `zsmul_eq_mul`" (since := "2026-01-05")]
/-
**zsmul_int_int** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zsmul_int_int (a b : Int) : a • b = a * b
参数：a b : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma zsmul_int_int (a b : ℤ) : a • b = a * b := rfl

@[deprecated "use `zsmul_one`" (since := "2026-01-05")]
/-
**zsmul_int_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zsmul_int_one (n : Int) : n • (1 : Int) = n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
lemma zsmul_int_one (n : ℤ) : n • (1 : ℤ) = n := mul_one _
