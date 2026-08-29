/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Group.Synonym

/-!
# Group with zero structure on the order type synonyms

Transfer algebraic instances from `α` to `αᵒᵈ` and `Lex α`.
-/

public section


open Function

variable {α : Type*}


/-! ### Order dual -/


namespace OrderDual

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MulZeroClass
  signature: α] : MulZeroClass αᵒᵈ
  body: inferInstanceAs MulZeroClass α

中文:
实例 [乘零类
  签名: α] : 乘零类 αᵒᵈ
  定义体: inferInstanceAs MulZeroClass α

Depends on / 依赖: MulZeroClass
-/
instance [MulZeroClass α] : MulZeroClass αᵒᵈ := inferInstanceAs MulZeroClass α

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MulZeroOneClass
  signature: α] : MulZeroOneClass αᵒᵈ
  body: inferInstanceAs MulZeroOneClass α

中文:
实例 [乘零幺类
  签名: α] : 乘零幺类 αᵒᵈ
  定义体: inferInstanceAs MulZeroOneClass α
-/
instance [MulZeroOneClass α] : MulZeroOneClass αᵒᵈ := inferInstanceAs MulZeroOneClass α

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mul
  signature: α] [Zero α] [NoZeroDivisors α] : NoZeroDivisors αᵒᵈ
  body: inferInstanceAs NoZeroDivisors α

中文:
实例 [乘法
  签名: α] [零 α] [无零因子 α] : 无零因子 αᵒᵈ
  定义体: inferInstanceAs NoZeroDivisors α

Depends on / 依赖: NoZeroDivisors
-/
instance [Mul α] [Zero α] [NoZeroDivisors α] : NoZeroDivisors αᵒᵈ :=
inferInstanceAs NoZeroDivisors α

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SemigroupWithZero
  signature: α] : SemigroupWithZero αᵒᵈ
  body: inferInstanceAs SemigroupWithZero α

中文:
实例 [带零半群
  签名: α] : 带零半群 αᵒᵈ
  定义体: inferInstanceAs SemigroupWithZero α

Depends on / 依赖: SemigroupWithZero
-/
instance [SemigroupWithZero α] : SemigroupWithZero αᵒᵈ := inferInstanceAs SemigroupWithZero α

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MonoidWithZero
  signature: α] : MonoidWithZero αᵒᵈ
  body: inferInstanceAs MonoidWithZero α

中文:
实例 [带零幺半群
  签名: α] : 带零幺半群 αᵒᵈ
  定义体: inferInstanceAs MonoidWithZero α
-/
instance [MonoidWithZero α] : MonoidWithZero αᵒᵈ := inferInstanceAs MonoidWithZero α

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mul
  signature: α] [Zero α] [IsLeftCancelMulZero α] : IsLeftCancelMulZero αᵒᵈ
  body: inferInstanceAs IsLeftCancelMulZero α

中文:
实例 [乘法
  签名: α] [零 α] [是左消去MulZero α] : 是左消去MulZero αᵒᵈ
  定义体: inferInstanceAs IsLeftCancelMulZero α

Depends on / 依赖: IsLeftCancelMulZero
-/
instance [Mul α] [Zero α] [IsLeftCancelMulZero α] : IsLeftCancelMulZero αᵒᵈ :=
inferInstanceAs IsLeftCancelMulZero α

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mul
  signature: α] [Zero α] [IsRightCancelMulZero α] : IsRightCancelMulZero αᵒᵈ
  body: inferInstanceAs IsRightCancelMulZero α

中文:
实例 [乘法
  签名: α] [零 α] [是右消去MulZero α] : 是右消去MulZero αᵒᵈ
  定义体: inferInstanceAs IsRightCancelMulZero α

Depends on / 依赖: IsRightCancelMulZero
-/
instance [Mul α] [Zero α] [IsRightCancelMulZero α] : IsRightCancelMulZero αᵒᵈ :=
inferInstanceAs IsRightCancelMulZero α

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mul
  signature: α] [Zero α] [IsCancelMulZero α] : IsCancelMulZero αᵒᵈ where

中文:
实例 [乘法
  签名: α] [零 α] [是乘零消去 α] : 是乘零消去 αᵒᵈ where
-/
instance [Mul α] [Zero α] [IsCancelMulZero α] : IsCancelMulZero αᵒᵈ where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommMonoidWithZero
  signature: α] : CommMonoidWithZero αᵒᵈ
  body: inferInstanceAs CommMonoidWithZero α

中文:
实例 [带零交换幺半群
  签名: α] : 带零交换幺半群 αᵒᵈ
  定义体: inferInstanceAs CommMonoidWithZero α

Depends on / 依赖: CommMonoidWithZero
-/
instance [CommMonoidWithZero α] : CommMonoidWithZero αᵒᵈ := inferInstanceAs CommMonoidWithZero α

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [GroupWithZero
  signature: α] : GroupWithZero αᵒᵈ
  body: inferInstanceAs GroupWithZero α

中文:
实例 [带零群
  签名: α] : 带零群 αᵒᵈ
  定义体: inferInstanceAs GroupWithZero α
-/
instance [GroupWithZero α] : GroupWithZero αᵒᵈ := inferInstanceAs GroupWithZero α

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommGroupWithZero
  signature: α] : CommGroupWithZero αᵒᵈ
  body: inferInstanceAs CommGroupWithZero α

中文:
实例 [带零交换群
  签名: α] : 带零交换群 αᵒᵈ
  定义体: inferInstanceAs CommGroupWithZero α

Depends on / 依赖: CommGroupWithZero
-/
instance [CommGroupWithZero α] : CommGroupWithZero αᵒᵈ := inferInstanceAs CommGroupWithZero α

end OrderDual

/-! ### Lexicographic order -/


namespace Lex

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MulZeroClass
  signature: α] : MulZeroClass (Lex α)
  body: inferInstanceAs MulZeroClass α

中文:
实例 [乘零类
  签名: α] : 乘零类 (Lex α)
  定义体: inferInstanceAs MulZeroClass α

Depends on / 依赖: MulZeroClass
-/
instance [MulZeroClass α] : MulZeroClass (Lex α) := inferInstanceAs MulZeroClass α

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MulZeroOneClass
  signature: α] : MulZeroOneClass (Lex α)
  body: inferInstanceAs MulZeroOneClass α

中文:
实例 [乘零幺类
  签名: α] : 乘零幺类 (Lex α)
  定义体: inferInstanceAs MulZeroOneClass α

Depends on / 依赖: MulZeroOneClass
-/
instance [MulZeroOneClass α] : MulZeroOneClass (Lex α) := inferInstanceAs MulZeroOneClass α

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mul
  signature: α] [Zero α] [NoZeroDivisors α] : NoZeroDivisors (Lex α)
  body: inferInstanceAs NoZeroDivisors α

中文:
实例 [乘法
  签名: α] [零 α] [无零因子 α] : 无零因子 (Lex α)
  定义体: inferInstanceAs NoZeroDivisors α

Depends on / 依赖: NoZeroDivisors
-/
instance [Mul α] [Zero α] [NoZeroDivisors α] : NoZeroDivisors (Lex α) :=
inferInstanceAs NoZeroDivisors α

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SemigroupWithZero
  signature: α] : SemigroupWithZero (Lex α)
  body: inferInstanceAs SemigroupWithZero α

中文:
实例 [带零半群
  签名: α] : 带零半群 (Lex α)
  定义体: inferInstanceAs SemigroupWithZero α

Depends on / 依赖: SemigroupWithZero
-/
instance [SemigroupWithZero α] : SemigroupWithZero (Lex α) := inferInstanceAs SemigroupWithZero α

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MonoidWithZero
  signature: α] : MonoidWithZero (Lex α)
  body: inferInstanceAs MonoidWithZero α

中文:
实例 [带零幺半群
  签名: α] : 带零幺半群 (Lex α)
  定义体: inferInstanceAs MonoidWithZero α

Depends on / 依赖: MonoidWithZero
-/
instance [MonoidWithZero α] : MonoidWithZero (Lex α) := inferInstanceAs MonoidWithZero α

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mul
  signature: α] [Zero α] [IsLeftCancelMulZero α] : IsLeftCancelMulZero (Lex α)
  body: inferInstanceAs IsLeftCancelMulZero α

中文:
实例 [乘法
  签名: α] [零 α] [是左消去MulZero α] : 是左消去MulZero (Lex α)
  定义体: inferInstanceAs IsLeftCancelMulZero α

Depends on / 依赖: IsLeftCancelMulZero
-/
instance [Mul α] [Zero α] [IsLeftCancelMulZero α] : IsLeftCancelMulZero (Lex α) :=
inferInstanceAs IsLeftCancelMulZero α

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mul
  signature: α] [Zero α] [IsRightCancelMulZero α] : IsRightCancelMulZero (Lex α)
  body: inferInstanceAs IsRightCancelMulZero α

中文:
实例 [乘法
  签名: α] [零 α] [是右消去MulZero α] : 是右消去MulZero (Lex α)
  定义体: inferInstanceAs IsRightCancelMulZero α

Depends on / 依赖: IsRightCancelMulZero
-/
instance [Mul α] [Zero α] [IsRightCancelMulZero α] : IsRightCancelMulZero (Lex α) :=
inferInstanceAs IsRightCancelMulZero α

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mul
  signature: α] [Zero α] [IsCancelMulZero α] : IsCancelMulZero (Lex α)
  body: inferInstanceAs IsCancelMulZero α

中文:
实例 [乘法
  签名: α] [零 α] [是乘零消去 α] : 是乘零消去 (Lex α)
  定义体: inferInstanceAs IsCancelMulZero α

Depends on / 依赖: IsCancelMulZero
-/
instance [Mul α] [Zero α] [IsCancelMulZero α] : IsCancelMulZero (Lex α) :=
inferInstanceAs IsCancelMulZero α

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommMonoidWithZero
  signature: α] : CommMonoidWithZero (Lex α)
  body: inferInstanceAs CommMonoidWithZero α

中文:
实例 [带零交换幺半群
  签名: α] : 带零交换幺半群 (Lex α)
  定义体: inferInstanceAs CommMonoidWithZero α

Depends on / 依赖: CommMonoidWithZero
-/
instance [CommMonoidWithZero α] : CommMonoidWithZero (Lex α) :=
inferInstanceAs CommMonoidWithZero α

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [GroupWithZero
  signature: α] : GroupWithZero (Lex α)
  body: inferInstanceAs GroupWithZero α

中文:
实例 [带零群
  签名: α] : 带零群 (Lex α)
  定义体: inferInstanceAs GroupWithZero α

Depends on / 依赖: GroupWithZero
-/
instance [GroupWithZero α] : GroupWithZero (Lex α) := inferInstanceAs GroupWithZero α

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommGroupWithZero
  signature: α] : CommGroupWithZero (Lex α)
  body: inferInstanceAs CommGroupWithZero α

中文:
实例 [带零交换群
  签名: α] : 带零交换群 (Lex α)
  定义体: inferInstanceAs CommGroupWithZero α

Depends on / 依赖: CommGroupWithZero
-/
instance [CommGroupWithZero α] : CommGroupWithZero (Lex α) := inferInstanceAs CommGroupWithZero α

end Lex
