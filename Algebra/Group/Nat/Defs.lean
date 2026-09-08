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

/-! ### Instances -/

/-
**Nat.instMulOneClass** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
形式化陈述：instMulOneClass : MulOneClass Nat where one_mul
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.one_mul`：∀ (n : ℕ), 1 * n = n
· 使用定理 `Nat.mul_one`：∀ (n : ℕ), n * 1 = n

--- 原说明 ---
### Instances
-/
instance instMulOneClass : MulOneClass ℕ where
  one_mul := Nat.one_mul
  mul_one := Nat.mul_one
/-
**Nat.instAddCancelCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
形式化陈述：instAddCancelCommMonoid : AddCancelCommMonoid Nat where add
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.add_assoc`：∀ (n m k : ℕ), n + m + k = n + (m + k)
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `Nat.add_zero`：∀ (n : ℕ), n + 0 = n
· 使用定理 `Nat.zero_mul`：∀ (n : ℕ), 0 * n = 0
· 使用定理 `Nat.succ_mul`：∀ (n m : ℕ), n.succ * m = n * m + m
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n
-/
instance instAddCancelCommMonoid : AddCancelCommMonoid ℕ where
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
/-
**Nat.instCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
形式化陈述：instCommMonoid : CommMonoid Nat where mul
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.mul_assoc`：∀ (n m k : ℕ), n * m * k = n * (m * k)
· 使用定理 `Nat.one_mul`：∀ (n : ℕ), 1 * n = n
· 使用定理 `Nat.mul_one`：∀ (n : ℕ), n * 1 = n
· 使用定理 `Nat.pow_zero`：∀ (n : ℕ), n ^ 0 = 1
· 使用定理 `Nat.mul_comm`：∀ (n m : ℕ), n * m = m * n
-/
instance instCommMonoid : CommMonoid ℕ where
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
/-
**Nat.instIsMulTorsionFree** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
形式化陈述：instIsMulTorsionFree : IsMulTorsionFree Nat where pow_left_injective _ h _
 _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.pow_left_inj`：∀ {a b n : ℕ}, n ≠ 0 → (a ^ n = b ^ n ↔ a = b)
-/
instance instIsMulTorsionFree : IsMulTorsionFree ℕ where
  pow_left_injective _ h _ _ := (Nat.pow_left_inj h).mp
/-
**Nat.instIsAddTorsionFree** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
形式化陈述：instIsAddTorsionFree : IsAddTorsionFree Nat where nsmul_right_injective _n
 hn _x _y hxy
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.mul_left_cancel`：∀ {n m k : ℕ}, 0 < n → n * m = n * k → m = k
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
-/
instance instIsAddTorsionFree : IsAddTorsionFree ℕ where
  nsmul_right_injective _n hn _x _y hxy := Nat.mul_left_cancel (Nat.pos_of_ne_zero hn) hxy

/-!
### Extra instances to short-circuit type class resolution

These also prevent non-computable instances being used to construct these instances non-computably.
-/

set_option linter.style.whitespace false -- manual alignment is not recognised

/-
**Nat.instAddCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
形式化陈述：instAddCommMonoid : AddCommMonoid Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Extra instances to short-circuit type class resolution

These also prevent non-computable instances being used to construct these instan
ces non-computably.
-/
instance instAddCommMonoid    : AddCommMonoid ℕ    := by infer_instance
/-
**Nat.instAddMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
形式化陈述：instAddMonoid : AddMonoid Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddMonoid        : AddMonoid ℕ        := by infer_instance
/-
**Nat.instMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
形式化陈述：instMonoid : Monoid Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMonoid           : Monoid ℕ           := by infer_instance
/-
**Nat.instCommSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
形式化陈述：instCommSemigroup : CommSemigroup Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommSemigroup    : CommSemigroup ℕ    := by infer_instance
/-
**Nat.instSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
形式化陈述：instSemigroup : Semigroup Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSemigroup        : Semigroup ℕ        := by infer_instance
/-
**Nat.instAddCommSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
形式化陈述：instAddCommSemigroup : AddCommSemigroup Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddCommSemigroup : AddCommSemigroup ℕ := by infer_instance
/-
**Nat.instAddSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
形式化陈述：instAddSemigroup : AddSemigroup Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddSemigroup     : AddSemigroup ℕ     := by infer_instance
/-
**Nat.instOne** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
形式化陈述：instOne : One Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instOne              : One ℕ              := inferInstance

set_option linter.style.whitespace true

/-! ### Miscellaneous lemmas -/

-- We set the simp priority slightly lower than default; later more general lemmas will replace it.
/-
**Nat.nsmul_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (m n : ℕ), m • n = m * n
参数：m n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp 900] protected lemma nsmul_eq_mul (m n : ℕ) : m • n = m * n := rfl

end Nat

