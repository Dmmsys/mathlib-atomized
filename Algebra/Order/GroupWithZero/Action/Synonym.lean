/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Order.Group.Action.Synonym
public import Mathlib.Algebra.Order.GroupWithZero.Synonym
public import Mathlib.Tactic.Common

/-!
# Actions by and on order synonyms

This PR transfers group action with zero instances from a type `α` to `αᵒᵈ` and `Lex α`. Note that
the `SMul` instances are already defined in `Mathlib/Algebra/Order/Group/Synonym.lean`.

## See also

* `Mathlib/Algebra/Order/Group/Action/Synonym.lean`
* `Mathlib/Algebra/Order/Module/Synonym.lean`
-/

public section

variable {G₀ M₀ : Type*}

namespace OrderDual

/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Zero M₀] [SMulZeroClass G₀ M₀] : SMulZeroClass G₀ᵒᵈ M₀ :=
  inferInstanceAs <| SMulZeroClass G₀ M₀
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Zero M₀] [SMulZeroClass G₀ M₀] : SMulZeroClass G₀ M₀ᵒᵈ :=
  inferInstanceAs <| SMulZeroClass G₀ M₀
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Zero G₀] [Zero M₀] [SMulWithZero G₀ M₀] : SMulWithZero G₀ᵒᵈ M₀ :=
  inferInstanceAs <| SMulWithZero G₀ M₀
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Zero G₀] [Zero M₀] [SMulWithZero G₀ M₀] : SMulWithZero G₀ M₀ᵒᵈ :=
  inferInstanceAs <| SMulWithZero G₀ M₀
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddZeroClass M₀] [DistribSMul G₀ M₀] : DistribSMul G₀ᵒᵈ M₀ :=
  inferInstanceAs <| DistribSMul G₀ M₀
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddZeroClass M₀] [DistribSMul G₀ M₀] : DistribSMul G₀ M₀ᵒᵈ :=
  inferInstanceAs <| DistribSMul G₀ M₀
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monoid G₀] [AddMonoid M₀] [DistribMulAction G₀ M₀] : DistribMulAction G₀ᵒᵈ M₀ :=
  inferInstanceAs <| DistribMulAction G₀ M₀
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monoid G₀] [AddMonoid M₀] [DistribMulAction G₀ M₀] : DistribMulAction G₀ M₀ᵒᵈ :=
  inferInstanceAs <| DistribMulAction G₀ M₀
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [MonoidWithZero G₀] [AddMonoid M₀] [MulActionWithZero G₀ M₀] :
    MulActionWithZero G₀ᵒᵈ M₀ := inferInstanceAs <| MulActionWithZero G₀ M₀
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [MonoidWithZero G₀] [AddMonoid M₀] [MulActionWithZero G₀ M₀] :
    MulActionWithZero G₀ M₀ᵒᵈ := inferInstanceAs <| MulActionWithZero G₀ M₀

end OrderDual

namespace Lex

/-
**Lex.instSMulWithZero** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
形式化陈述：instSMulWithZero [Zero G₀] [Zero M₀] [SMulWithZero G₀ M₀] : SMulWithZero (
Lex G₀) M₀
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSMulWithZero [Zero G₀] [Zero M₀] [SMulWithZero G₀ M₀] : SMulWithZero (Lex G₀) M₀ :=
  inferInstanceAs <| SMulWithZero G₀ M₀
/-
**Lex.instSMulWithZero'** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
形式化陈述：instSMulWithZero' [Zero G₀] [Zero M₀] [SMulWithZero G₀ M₀] : SMulWithZero 
G₀ (Lex M₀)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSMulWithZero' [Zero G₀] [Zero M₀] [SMulWithZero G₀ M₀] : SMulWithZero G₀ (Lex M₀) :=
  inferInstanceAs <| SMulWithZero G₀ M₀
/-
**Lex.instDistribSMul** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
形式化陈述：instDistribSMul [AddZeroClass M₀] [DistribSMul G₀ M₀] : DistribSMul (Lex G
₀) M₀
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDistribSMul [AddZeroClass M₀] [DistribSMul G₀ M₀] : DistribSMul (Lex G₀) M₀ :=
  inferInstanceAs <| DistribSMul G₀ M₀
/-
**Lex.instDistribSMul'** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
形式化陈述：instDistribSMul' [AddZeroClass M₀] [DistribSMul G₀ M₀] : DistribSMul G₀ (L
ex M₀)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDistribSMul' [AddZeroClass M₀] [DistribSMul G₀ M₀] : DistribSMul G₀ (Lex M₀) :=
  inferInstanceAs <| DistribSMul G₀ M₀
/-
**Lex.instDistribMulAction** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
形式化陈述：instDistribMulAction [Monoid G₀] [AddMonoid M₀] [DistribMulAction G₀ M₀] :
 DistribMulAction (Lex G₀) M₀
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDistribMulAction [Monoid G₀] [AddMonoid M₀] [DistribMulAction G₀ M₀] :
    DistribMulAction (Lex G₀) M₀ := inferInstanceAs <| DistribMulAction G₀ M₀
/-
**Lex.instDistribMulAction'** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
形式化陈述：instDistribMulAction' [Monoid G₀] [AddMonoid M₀] [DistribMulAction G₀ M₀] 
: DistribMulAction G₀ (Lex M₀)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDistribMulAction' [Monoid G₀] [AddMonoid M₀] [DistribMulAction G₀ M₀] :
    DistribMulAction G₀ (Lex M₀) := inferInstanceAs <| DistribMulAction G₀ M₀
/-
**Lex.instMulActionWithZero** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
形式化陈述：instMulActionWithZero [MonoidWithZero G₀] [AddMonoid M₀] [MulActionWithZer
o G₀ M₀] : MulActionWithZero (Lex G₀) M₀
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMulActionWithZero [MonoidWithZero G₀] [AddMonoid M₀] [MulActionWithZero G₀ M₀] :
    MulActionWithZero (Lex G₀) M₀ := inferInstanceAs <| MulActionWithZero G₀ M₀
/-
**Lex.instMulActionWithZero'** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
形式化陈述：instMulActionWithZero' [MonoidWithZero G₀] [AddMonoid M₀] [MulActionWithZe
ro G₀ M₀] : MulActionWithZero G₀ (Lex M₀)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMulActionWithZero' [MonoidWithZero G₀] [AddMonoid M₀] [MulActionWithZero G₀ M₀] :
    MulActionWithZero G₀ (Lex M₀) := inferInstanceAs <| MulActionWithZero G₀ M₀

end Lex

