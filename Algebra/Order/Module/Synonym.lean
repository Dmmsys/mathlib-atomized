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

/-
**OrderDual.instModule** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
形式化陈述：instModule [Semiring α] [AddCommMonoid β] [Module α β] : Module αᵒᵈ β wher
e add_smul
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
-/
instance instModule [Semiring α] [AddCommMonoid β] [Module α β] : Module αᵒᵈ β where
  add_smul := add_smul (R := α)
  zero_smul := zero_smul _
/-
**OrderDual.instModule'** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
形式化陈述：instModule' [Semiring α] [AddCommMonoid β] [Module α β] : Module α βᵒᵈ whe
re add_smul
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
-/
instance instModule' [Semiring α] [AddCommMonoid β] [Module α β] : Module α βᵒᵈ where
  add_smul := add_smul (M := β)
  zero_smul := zero_smul _

end OrderDual

namespace Lex

/-
**Lex.instModule** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
形式化陈述：instModule [Semiring α] [AddCommMonoid β] [Module α β] : Module (Lex α) β
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instModule [Semiring α] [AddCommMonoid β] [Module α β] : Module (Lex α) β :=
  ‹Module α β›
/-
**Lex.instModule'** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
形式化陈述：instModule' [Semiring α] [AddCommMonoid β] [Module α β] : Module α (Lex β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instModule' [Semiring α] [AddCommMonoid β] [Module α β] : Module α (Lex β) :=
  ‹Module α β›

end Lex

