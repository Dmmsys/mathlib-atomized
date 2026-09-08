/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Units

/-!
# The units of an ordered commutative monoid form an ordered commutative group
-/

public section


variable {α : Type*}

/-- The units of an ordered commutative monoid form an ordered commutative group. -/
@[to_additive
      /-- The units of an ordered commutative additive monoid form an ordered commutative
      additive group. -/]
/-
**Units.isOrderedMonoid** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Units.isOrderedMonoid [CommMonoid α] [Preorder α] [IsOrderedMonoid α] : Is
OrderedMonoid αˣ where mul_le_mul_left _ _ h _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_le_mul_left`：mul_le_mul_left [i : MulRightMono α] {b c : α} (bc : b 
<= c) (a : α) : b * a <= c * a
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
instance Units.isOrderedMonoid [CommMonoid α] [Preorder α] [IsOrderedMonoid α] :
    IsOrderedMonoid αˣ where
  mul_le_mul_left _ _ h _ := mul_le_mul_left (α := α) h _
