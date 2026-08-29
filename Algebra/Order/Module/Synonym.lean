/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Action.Synonym
public import Mathlib.Algebra.Order.Ring.Synonym

/-!
# Action instances for `OrderDual`


This PR transfers group action with zero instances from a type `α` to `αᵒᵈ` and `Lex α`. Note that
the `SMul` instances are already defined in `Mathlib/Algebra/Order/Group/Synonym.lean`.

## See also

* `Mathlib/Algebra/Order/Group/Action/Synonym.lean`
* `Mathlib/Algebra/Order/GroupWithZero/Action/Synonym.lean`
-/

public section

variable {α β : Type*}

namespace OrderDual

/--
Instance `instModule` / 实例 `instModule`

English:
instance instModule
  signature: [Semiring α] [AddCommMonoid β] [Module α β]
  body: add_smul (R := α)
  zero_smul := zero_smul _

中文:
实例 instModule
  签名: [半环 α] [加法交换幺半群 β] [模 α β]
  定义体: add_smul (R := α)
  zero_smul := zero_smul _

Depends on / 依赖: add_smul
-/
instance instModule [Semiring α] [AddCommMonoid β] [Module α β] : Module αᵒᵈ β where
  add_smul := add_smul (R := α)
  zero_smul := zero_smul _

/--
Instance `instModule'` / 实例 `instModule'`

English:
instance instModule'
  signature: [Semiring α] [AddCommMonoid β] [Module α β]
  body: add_smul (M := β)
  zero_smul := zero_smul _

中文:
实例 instModule'
  签名: [半环 α] [加法交换幺半群 β] [模 α β]
  定义体: add_smul (M := β)
  zero_smul := zero_smul _

Depends on / 依赖: add_smul
-/
instance instModule' [Semiring α] [AddCommMonoid β] [Module α β] : Module α βᵒᵈ where
  add_smul := add_smul (M := β)
  zero_smul := zero_smul _

end OrderDual

namespace Lex

/--
Instance `instModule` / 实例 `instModule`

English:
instance instModule
  signature: [Semiring α] [AddCommMonoid β] [Module α β]
  body: ‹Module α β›

中文:
实例 instModule
  签名: [半环 α] [加法交换幺半群 β] [模 α β]
  定义体: ‹Module α β›

Depends on / 依赖: Module
-/
instance instModule [Semiring α] [AddCommMonoid β] [Module α β] : Module (Lex α) β :=
  ‹Module α β›

/--
Instance `instModule'` / 实例 `instModule'`

English:
instance instModule'
  signature: [Semiring α] [AddCommMonoid β] [Module α β]
  body: ‹Module α β›

中文:
实例 instModule'
  签名: [半环 α] [加法交换幺半群 β] [模 α β]
  定义体: ‹Module α β›

Depends on / 依赖: Module
-/
instance instModule' [Semiring α] [AddCommMonoid β] [Module α β] : Module α (Lex β) :=
  ‹Module α β›

end Lex
