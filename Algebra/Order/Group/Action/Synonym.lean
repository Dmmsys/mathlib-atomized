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
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: M] [MulAction M α] : MulAction Mᵒᵈ α
  body: inferInstanceAs MulAction M α

@[to_additive]

中文:
实例 [幺半群
  签名: M] [乘法作用 M α] : 乘法作用 Mᵒᵈ α
  定义体: inferInstanceAs MulAction M α

@[to_additive]

Depends on / 依赖: MulAction
-/
instance [Monoid M] [MulAction M α] : MulAction Mᵒᵈ α := inferInstanceAs MulAction M α

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: M] [MulAction M α] : MulAction M αᵒᵈ
  body: inferInstanceAs MulAction M α

@[to_additive]

中文:
实例 [幺半群
  签名: M] [乘法作用 M α] : 乘法作用 M αᵒᵈ
  定义体: inferInstanceAs MulAction M α

@[to_additive]

Depends on / 依赖: MulAction
-/
instance [Monoid M] [MulAction M α] : MulAction M αᵒᵈ := inferInstanceAs MulAction M α

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: M α] [SMul N α] [SMulCommClass M N α] : SMulCommClass Mᵒᵈ N α
  body: ‹SMulCommClass M N α›

@[to_additive]

中文:
实例 [标量乘法
  签名: M α] [标量乘法 N α] [标量交换类 M N α] : 标量交换类 Mᵒᵈ N α
  定义体: ‹SMulCommClass M N α›

@[to_additive]

Depends on / 依赖: SMulCommClass
-/
instance [SMul M α] [SMul N α] [SMulCommClass M N α] : SMulCommClass Mᵒᵈ N α :=
  ‹SMulCommClass M N α›

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: M α] [SMul N α] [SMulCommClass M N α] : SMulCommClass M Nᵒᵈ α
  body: ‹SMulCommClass M N α›

@[to_additive]

中文:
实例 [标量乘法
  签名: M α] [标量乘法 N α] [标量交换类 M N α] : 标量交换类 M Nᵒᵈ α
  定义体: ‹SMulCommClass M N α›

@[to_additive]

Depends on / 依赖: SMulCommClass
-/
instance [SMul M α] [SMul N α] [SMulCommClass M N α] : SMulCommClass M Nᵒᵈ α :=
  ‹SMulCommClass M N α›

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: M α] [SMul N α] [SMulCommClass M N α] : SMulCommClass M N αᵒᵈ
  body: ‹SMulCommClass M N α›

@[to_additive]

中文:
实例 [标量乘法
  签名: M α] [标量乘法 N α] [标量交换类 M N α] : 标量交换类 M N αᵒᵈ
  定义体: ‹SMulCommClass M N α›

@[to_additive]
-/
instance [SMul M α] [SMul N α] [SMulCommClass M N α] : SMulCommClass M N αᵒᵈ :=
  ‹SMulCommClass M N α›

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: M N] [SMul M α] [SMul N α] [IsScalarTower M N α] : IsScalarTower Mᵒᵈ N α
  body: ‹IsScalarTower M N α›

@[to_additive]

中文:
实例 [标量乘法
  签名: M N] [标量乘法 M α] [标量乘法 N α] [标量塔 M N α] : 标量塔 Mᵒᵈ N α
  定义体: ‹IsScalarTower M N α›

@[to_additive]
-/
instance [SMul M N] [SMul M α] [SMul N α] [IsScalarTower M N α] : IsScalarTower Mᵒᵈ N α :=
  ‹IsScalarTower M N α›

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: M N] [SMul M α] [SMul N α] [IsScalarTower M N α] : IsScalarTower M Nᵒᵈ α
  body: ‹IsScalarTower M N α›

@[to_additive]

中文:
实例 [标量乘法
  签名: M N] [标量乘法 M α] [标量乘法 N α] [标量塔 M N α] : 标量塔 M Nᵒᵈ α
  定义体: ‹IsScalarTower M N α›

@[to_additive]

Depends on / 依赖: IsScalarTower
-/
instance [SMul M N] [SMul M α] [SMul N α] [IsScalarTower M N α] : IsScalarTower M Nᵒᵈ α :=
  ‹IsScalarTower M N α›

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: M N] [SMul M α] [SMul N α] [IsScalarTower M N α] : IsScalarTower M N αᵒᵈ
  body: ‹IsScalarTower M N α›

中文:
实例 [标量乘法
  签名: M N] [标量乘法 M α] [标量乘法 N α] [标量塔 M N α] : 标量塔 M N αᵒᵈ
  定义体: ‹IsScalarTower M N α›

Depends on / 依赖: IsScalarTower
-/
instance [SMul M N] [SMul M α] [SMul N α] [IsScalarTower M N α] : IsScalarTower M N αᵒᵈ :=
  ‹IsScalarTower M N α›

end OrderDual

namespace Lex

@[to_additive]
/--
Instance `instMulAction` / 实例 `instMulAction`

English:
instance instMulAction
  signature: [Monoid M] [MulAction M α]
  body: inferInstanceAs MulAction M α

@[to_additive]

中文:
实例 instMulAction
  签名: [幺半群 M] [乘法作用 M α]
  定义体: inferInstanceAs MulAction M α

@[to_additive]

Depends on / 依赖: MulAction
-/
instance instMulAction [Monoid M] [MulAction M α] : MulAction (Lex M) α :=
inferInstanceAs MulAction M α

@[to_additive]
/--
Instance `instMulAction'` / 实例 `instMulAction'`

English:
instance instMulAction'
  signature: [Monoid M] [MulAction M α]
  body: inferInstanceAs MulAction M α

@[to_additive]

中文:
实例 instMulAction'
  签名: [幺半群 M] [乘法作用 M α]
  定义体: inferInstanceAs MulAction M α

@[to_additive]

Depends on / 依赖: MulAction
-/
instance instMulAction' [Monoid M] [MulAction M α] : MulAction M (Lex α) :=
inferInstanceAs MulAction M α

@[to_additive]
/--
Instance `instSMulCommClass` / 实例 `instSMulCommClass`

English:
instance instSMulCommClass
  signature: [SMul M α] [SMul N α] [SMulCommClass M N α]
  body: inferInstanceAs SMulCommClass M N α

@[to_additive]

中文:
实例 instSMulCommClass
  签名: [标量乘法 M α] [标量乘法 N α] [标量交换类 M N α]
  定义体: inferInstanceAs SMulCommClass M N α

@[to_additive]

Depends on / 依赖: SMulCommClass
-/
instance instSMulCommClass [SMul M α] [SMul N α] [SMulCommClass M N α] :
SMulCommClass (Lex M) N α := inferInstanceAs SMulCommClass M N α

@[to_additive]
/--
Instance `instSMulCommClass'` / 实例 `instSMulCommClass'`

English:
instance instSMulCommClass'
  signature: [SMul M α] [SMul N α] [SMulCommClass M N α]
  body: inferInstanceAs SMulCommClass M N α

@[to_additive]

中文:
实例 instSMulCommClass'
  签名: [标量乘法 M α] [标量乘法 N α] [标量交换类 M N α]
  定义体: inferInstanceAs SMulCommClass M N α

@[to_additive]

Depends on / 依赖: SMulCommClass
-/
instance instSMulCommClass' [SMul M α] [SMul N α] [SMulCommClass M N α] :
SMulCommClass M (Lex N) α := inferInstanceAs SMulCommClass M N α

@[to_additive]
/--
Instance `instSMulCommClass''` / 实例 `instSMulCommClass''`

English:
instance instSMulCommClass''
  signature: [SMul M α] [SMul N α] [SMulCommClass M N α]
  body: inferInstanceAs SMulCommClass M N α

@[to_additive]

中文:
实例 instSMulCommClass''
  签名: [标量乘法 M α] [标量乘法 N α] [标量交换类 M N α]
  定义体: inferInstanceAs SMulCommClass M N α

@[to_additive]

Depends on / 依赖: SMulCommClass
-/
instance instSMulCommClass'' [SMul M α] [SMul N α] [SMulCommClass M N α] :
SMulCommClass M N (Lex α) := inferInstanceAs SMulCommClass M N α

@[to_additive]
/--
Instance `instIsScalarTower` / 实例 `instIsScalarTower`

English:
instance instIsScalarTower
  signature: [SMul M N] [SMul M α] [SMul N α] [IsScalarTower M N α]
  body: inferInstanceAs IsScalarTower M N α

@[to_additive]

中文:
实例 instIsScalarTower
  签名: [标量乘法 M N] [标量乘法 M α] [标量乘法 N α] [标量塔 M N α]
  定义体: inferInstanceAs IsScalarTower M N α

@[to_additive]

Depends on / 依赖: IsScalarTower
-/
instance instIsScalarTower [SMul M N] [SMul M α] [SMul N α] [IsScalarTower M N α] :
IsScalarTower (Lex M) N α := inferInstanceAs IsScalarTower M N α

@[to_additive]
/--
Instance `instIsScalarTower'` / 实例 `instIsScalarTower'`

English:
instance instIsScalarTower'
  signature: [SMul M N] [SMul M α] [SMul N α] [IsScalarTower M N α]
  body: inferInstanceAs IsScalarTower M N α

@[to_additive]

中文:
实例 instIsScalarTower'
  签名: [标量乘法 M N] [标量乘法 M α] [标量乘法 N α] [标量塔 M N α]
  定义体: inferInstanceAs IsScalarTower M N α

@[to_additive]

Depends on / 依赖: IsScalarTower
-/
instance instIsScalarTower' [SMul M N] [SMul M α] [SMul N α] [IsScalarTower M N α] :
IsScalarTower M (Lex N) α := inferInstanceAs IsScalarTower M N α

@[to_additive]
/--
Instance `instIsScalarTower''` / 实例 `instIsScalarTower''`

English:
instance instIsScalarTower''
  signature: [SMul M N] [SMul M α] [SMul N α] [IsScalarTower M N α]
  body: inferInstanceAs IsScalarTower M N α

中文:
实例 instIsScalarTower''
  签名: [标量乘法 M N] [标量乘法 M α] [标量乘法 N α] [标量塔 M N α]
  定义体: inferInstanceAs IsScalarTower M N α

Depends on / 依赖: IsScalarTower
-/
instance instIsScalarTower'' [SMul M N] [SMul M α] [SMul N α] [IsScalarTower M N α] :
IsScalarTower M N (Lex α) := inferInstanceAs IsScalarTower M N α

end Lex
