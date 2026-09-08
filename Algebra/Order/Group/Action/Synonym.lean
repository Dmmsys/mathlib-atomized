/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Order.Group.Synonym

/-!
# Actions by and on order synonyms

This PR transfers group action instances from a type `α` to `αᵒᵈ` and `Lex α`.

## See also

* `Mathlib/Algebra/Order/GroupWithZero/Action/Synonym.lean`
* `Mathlib/Algebra/Order/Module/Synonym.lean`
-/

public section

variable {M N α : Type*}

namespace OrderDual

@[to_additive]
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monoid M] [MulAction M α] : MulAction Mᵒᵈ α := inferInstanceAs <| MulAction M α

@[to_additive]
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monoid M] [MulAction M α] : MulAction M αᵒᵈ := inferInstanceAs <| MulAction M α

@[to_additive]
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul M α] [SMul N α] [SMulCommClass M N α] : SMulCommClass Mᵒᵈ N α :=
  ‹SMulCommClass M N α›

@[to_additive]
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul M α] [SMul N α] [SMulCommClass M N α] : SMulCommClass M Nᵒᵈ α :=
  ‹SMulCommClass M N α›

@[to_additive]
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul M α] [SMul N α] [SMulCommClass M N α] : SMulCommClass M N αᵒᵈ :=
  ‹SMulCommClass M N α›

@[to_additive]
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul M N] [SMul M α] [SMul N α] [IsScalarTower M N α] : IsScalarTower Mᵒᵈ N α :=
  ‹IsScalarTower M N α›

@[to_additive]
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul M N] [SMul M α] [SMul N α] [IsScalarTower M N α] : IsScalarTower M Nᵒᵈ α :=
  ‹IsScalarTower M N α›

@[to_additive]
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul M N] [SMul M α] [SMul N α] [IsScalarTower M N α] : IsScalarTower M N αᵒᵈ :=
  ‹IsScalarTower M N α›

end OrderDual

namespace Lex

@[to_additive]
/-
**Lex.instMulAction** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
形式化陈述：instMulAction [Monoid M] [MulAction M α] : MulAction (Lex M) α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMulAction [Monoid M] [MulAction M α] : MulAction (Lex M) α :=
  inferInstanceAs <| MulAction M α

@[to_additive]
/-
**Lex.instMulAction'** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
形式化陈述：instMulAction' [Monoid M] [MulAction M α] : MulAction M (Lex α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMulAction' [Monoid M] [MulAction M α] : MulAction M (Lex α) :=
  inferInstanceAs <| MulAction M α

@[to_additive]
/-
**Lex.instSMulCommClass** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
形式化陈述：instSMulCommClass [SMul M α] [SMul N α] [SMulCommClass M N α] : SMulCommCl
ass (Lex M) N α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSMulCommClass [SMul M α] [SMul N α] [SMulCommClass M N α] :
    SMulCommClass (Lex M) N α := inferInstanceAs <| SMulCommClass M N α

@[to_additive]
/-
**Lex.instSMulCommClass'** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
形式化陈述：instSMulCommClass' [SMul M α] [SMul N α] [SMulCommClass M N α] : SMulCommC
lass M (Lex N) α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSMulCommClass' [SMul M α] [SMul N α] [SMulCommClass M N α] :
    SMulCommClass M (Lex N) α := inferInstanceAs <| SMulCommClass M N α

@[to_additive]
/-
**Lex.instSMulCommClass''** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
形式化陈述：instSMulCommClass'' [SMul M α] [SMul N α] [SMulCommClass M N α] : SMulComm
Class M N (Lex α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSMulCommClass'' [SMul M α] [SMul N α] [SMulCommClass M N α] :
    SMulCommClass M N (Lex α) := inferInstanceAs <| SMulCommClass M N α

@[to_additive]
/-
**Lex.instIsScalarTower** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
形式化陈述：instIsScalarTower [SMul M N] [SMul M α] [SMul N α] [IsScalarTower M N α] :
 IsScalarTower (Lex M) N α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instIsScalarTower [SMul M N] [SMul M α] [SMul N α] [IsScalarTower M N α] :
    IsScalarTower (Lex M) N α := inferInstanceAs <| IsScalarTower M N α

@[to_additive]
/-
**Lex.instIsScalarTower'** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
形式化陈述：instIsScalarTower' [SMul M N] [SMul M α] [SMul N α] [IsScalarTower M N α] 
: IsScalarTower M (Lex N) α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instIsScalarTower' [SMul M N] [SMul M α] [SMul N α] [IsScalarTower M N α] :
    IsScalarTower M (Lex N) α := inferInstanceAs <| IsScalarTower M N α

@[to_additive]
/-
**Lex.instIsScalarTower''** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
形式化陈述：instIsScalarTower'' [SMul M N] [SMul M α] [SMul N α] [IsScalarTower M N α]
 : IsScalarTower M N (Lex α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instIsScalarTower'' [SMul M N] [SMul M α] [SMul N α] [IsScalarTower M N α] :
    IsScalarTower M N (Lex α) := inferInstanceAs <| IsScalarTower M N α

end Lex

