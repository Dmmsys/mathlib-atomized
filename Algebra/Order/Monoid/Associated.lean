/-
Copyright (c) 2022 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
module

public import Mathlib.Algebra.GroupWithZero.Associated
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs

/-!
# Order on associates

This file shows that divisibility makes associates into a canonically ordered monoid.
-/

public section

variable {M : Type*} [CommMonoidWithZero M]

namespace Associates

/-
**Associates.instIsOrderedMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Associates`。
形式化陈述：instIsOrderedMonoid : IsOrderedMonoid (Associates M) where mul_le_mul_left
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_right_comm`：mul_right_comm (a b c : G) : a * b * c = a * c * b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
instance instIsOrderedMonoid : IsOrderedMonoid (Associates M) where
  mul_le_mul_left := by rintro a _ ⟨d, rfl⟩ c; exact ⟨d, mul_right_comm ..⟩
/-
**Associates.** 是 Mathlib 中的一个实例，位于命名空间 `Associates`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CanonicallyOrderedMul (Associates M) where
  exists_mul_of_le h := h
  le_mul_self _ b := ⟨b, mul_comm ..⟩
  le_self_mul _ b := ⟨b, rfl⟩

end Associates

