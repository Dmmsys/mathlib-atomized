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

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Zero
  signature: M₀] [SMulZeroClass G₀ M₀] : SMulZeroClass G₀ᵒᵈ M₀
  body: inferInstanceAs SMulZeroClass G₀ M₀

中文:
实例 [Zero
  签名: M₀] [SMulZeroClass G₀ M₀] : SMulZeroClass G₀ᵒᵈ M₀
  定义体: inferInstanceAs SMulZeroClass G₀ M₀

Depends on / 依赖: SMulZeroClass
-/
instance [Zero M₀] [SMulZeroClass G₀ M₀] : SMulZeroClass G₀ᵒᵈ M₀ :=
inferInstanceAs SMulZeroClass G₀ M₀

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Zero
  signature: M₀] [SMulZeroClass G₀ M₀] : SMulZeroClass G₀ M₀ᵒᵈ
  body: inferInstanceAs SMulZeroClass G₀ M₀

中文:
实例 [Zero
  签名: M₀] [SMulZeroClass G₀ M₀] : SMulZeroClass G₀ M₀ᵒᵈ
  定义体: inferInstanceAs SMulZeroClass G₀ M₀
-/
instance [Zero M₀] [SMulZeroClass G₀ M₀] : SMulZeroClass G₀ M₀ᵒᵈ :=
inferInstanceAs SMulZeroClass G₀ M₀

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Zero
  signature: G₀] [Zero M₀] [SMulWithZero G₀ M₀] : SMulWithZero G₀ᵒᵈ M₀
  body: inferInstanceAs SMulWithZero G₀ M₀

中文:
实例 [Zero
  签名: G₀] [Zero M₀] [SMulWithZero G₀ M₀] : SMulWithZero G₀ᵒᵈ M₀
  定义体: inferInstanceAs SMulWithZero G₀ M₀
-/
instance [Zero G₀] [Zero M₀] [SMulWithZero G₀ M₀] : SMulWithZero G₀ᵒᵈ M₀ :=
inferInstanceAs SMulWithZero G₀ M₀

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Zero
  signature: G₀] [Zero M₀] [SMulWithZero G₀ M₀] : SMulWithZero G₀ M₀ᵒᵈ
  body: inferInstanceAs SMulWithZero G₀ M₀

中文:
实例 [Zero
  签名: G₀] [Zero M₀] [SMulWithZero G₀ M₀] : SMulWithZero G₀ M₀ᵒᵈ
  定义体: inferInstanceAs SMulWithZero G₀ M₀

Depends on / 依赖: SMulWithZero
-/
instance [Zero G₀] [Zero M₀] [SMulWithZero G₀ M₀] : SMulWithZero G₀ M₀ᵒᵈ :=
inferInstanceAs SMulWithZero G₀ M₀

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddZeroClass
  signature: M₀] [DistribSMul G₀ M₀] : DistribSMul G₀ᵒᵈ M₀
  body: inferInstanceAs DistribSMul G₀ M₀

中文:
实例 [AddZeroClass
  签名: M₀] [DistribSMul G₀ M₀] : DistribSMul G₀ᵒᵈ M₀
  定义体: inferInstanceAs DistribSMul G₀ M₀
-/
instance [AddZeroClass M₀] [DistribSMul G₀ M₀] : DistribSMul G₀ᵒᵈ M₀ :=
inferInstanceAs DistribSMul G₀ M₀

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddZeroClass
  signature: M₀] [DistribSMul G₀ M₀] : DistribSMul G₀ M₀ᵒᵈ
  body: inferInstanceAs DistribSMul G₀ M₀

中文:
实例 [AddZeroClass
  签名: M₀] [DistribSMul G₀ M₀] : DistribSMul G₀ M₀ᵒᵈ
  定义体: inferInstanceAs DistribSMul G₀ M₀

Depends on / 依赖: DistribSMul
-/
instance [AddZeroClass M₀] [DistribSMul G₀ M₀] : DistribSMul G₀ M₀ᵒᵈ :=
inferInstanceAs DistribSMul G₀ M₀

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: G₀] [AddMonoid M₀] [DistribMulAction G₀ M₀] : DistribMulAction G₀ᵒᵈ M₀
  body: inferInstanceAs DistribMulAction G₀ M₀

中文:
实例 [Monoid
  签名: G₀] [AddMonoid M₀] [DistribMulAction G₀ M₀] : DistribMulAction G₀ᵒᵈ M₀
  定义体: inferInstanceAs DistribMulAction G₀ M₀
-/
instance [Monoid G₀] [AddMonoid M₀] [DistribMulAction G₀ M₀] : DistribMulAction G₀ᵒᵈ M₀ :=
inferInstanceAs DistribMulAction G₀ M₀

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: G₀] [AddMonoid M₀] [DistribMulAction G₀ M₀] : DistribMulAction G₀ M₀ᵒᵈ
  body: inferInstanceAs DistribMulAction G₀ M₀

中文:
实例 [Monoid
  签名: G₀] [AddMonoid M₀] [DistribMulAction G₀ M₀] : DistribMulAction G₀ M₀ᵒᵈ
  定义体: inferInstanceAs DistribMulAction G₀ M₀

Depends on / 依赖: DistribMulAction
-/
instance [Monoid G₀] [AddMonoid M₀] [DistribMulAction G₀ M₀] : DistribMulAction G₀ M₀ᵒᵈ :=
inferInstanceAs DistribMulAction G₀ M₀

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MonoidWithZero
  signature: G₀] [AddMonoid M₀] [MulActionWithZero G₀ M₀] :
  body: inferInstanceAs MulActionWithZero G₀ M₀

中文:
实例 [MonoidWithZero
  签名: G₀] [AddMonoid M₀] [MulActionWithZero G₀ M₀] :
  定义体: inferInstanceAs MulActionWithZero G₀ M₀
-/
instance [MonoidWithZero G₀] [AddMonoid M₀] [MulActionWithZero G₀ M₀] :
MulActionWithZero G₀ᵒᵈ M₀ := inferInstanceAs MulActionWithZero G₀ M₀

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MonoidWithZero
  signature: G₀] [AddMonoid M₀] [MulActionWithZero G₀ M₀] :
  body: inferInstanceAs MulActionWithZero G₀ M₀

中文:
实例 [MonoidWithZero
  签名: G₀] [AddMonoid M₀] [MulActionWithZero G₀ M₀] :
  定义体: inferInstanceAs MulActionWithZero G₀ M₀
-/
instance [MonoidWithZero G₀] [AddMonoid M₀] [MulActionWithZero G₀ M₀] :
MulActionWithZero G₀ M₀ᵒᵈ := inferInstanceAs MulActionWithZero G₀ M₀

end OrderDual

namespace Lex

/--
Instance `instSMulWithZero` / 实例 `instSMulWithZero`

English:
instance instSMulWithZero
  signature: [Zero G₀] [Zero M₀] [SMulWithZero G₀ M₀]
  body: inferInstanceAs SMulWithZero G₀ M₀

中文:
实例 instSMulWithZero
  签名: [Zero G₀] [Zero M₀] [SMulWithZero G₀ M₀]
  定义体: inferInstanceAs SMulWithZero G₀ M₀

Depends on / 依赖: SMulWithZero
-/
instance instSMulWithZero [Zero G₀] [Zero M₀] [SMulWithZero G₀ M₀] : SMulWithZero (Lex G₀) M₀ :=
inferInstanceAs SMulWithZero G₀ M₀

/--
Instance `instSMulWithZero'` / 实例 `instSMulWithZero'`

English:
instance instSMulWithZero'
  signature: [Zero G₀] [Zero M₀] [SMulWithZero G₀ M₀]
  body: inferInstanceAs SMulWithZero G₀ M₀

中文:
实例 instSMulWithZero'
  签名: [Zero G₀] [Zero M₀] [SMulWithZero G₀ M₀]
  定义体: inferInstanceAs SMulWithZero G₀ M₀

Depends on / 依赖: SMulWithZero
-/
instance instSMulWithZero' [Zero G₀] [Zero M₀] [SMulWithZero G₀ M₀] : SMulWithZero G₀ (Lex M₀) :=
inferInstanceAs SMulWithZero G₀ M₀

/--
Instance `instDistribSMul` / 实例 `instDistribSMul`

English:
instance instDistribSMul
  signature: [AddZeroClass M₀] [DistribSMul G₀ M₀]
  body: inferInstanceAs DistribSMul G₀ M₀

中文:
实例 instDistribSMul
  签名: [AddZeroClass M₀] [DistribSMul G₀ M₀]
  定义体: inferInstanceAs DistribSMul G₀ M₀

Depends on / 依赖: DistribSMul
-/
instance instDistribSMul [AddZeroClass M₀] [DistribSMul G₀ M₀] : DistribSMul (Lex G₀) M₀ :=
inferInstanceAs DistribSMul G₀ M₀

/--
Instance `instDistribSMul'` / 实例 `instDistribSMul'`

English:
instance instDistribSMul'
  signature: [AddZeroClass M₀] [DistribSMul G₀ M₀]
  body: inferInstanceAs DistribSMul G₀ M₀

中文:
实例 instDistribSMul'
  签名: [AddZeroClass M₀] [DistribSMul G₀ M₀]
  定义体: inferInstanceAs DistribSMul G₀ M₀

Depends on / 依赖: DistribSMul
-/
instance instDistribSMul' [AddZeroClass M₀] [DistribSMul G₀ M₀] : DistribSMul G₀ (Lex M₀) :=
inferInstanceAs DistribSMul G₀ M₀

/--
Instance `instDistribMulAction` / 实例 `instDistribMulAction`

English:
instance instDistribMulAction
  signature: [Monoid G₀] [AddMonoid M₀] [DistribMulAction G₀ M₀]
  body: inferInstanceAs DistribMulAction G₀ M₀

中文:
实例 instDistribMulAction
  签名: [Monoid G₀] [AddMonoid M₀] [DistribMulAction G₀ M₀]
  定义体: inferInstanceAs DistribMulAction G₀ M₀

Depends on / 依赖: DistribMulAction
-/
instance instDistribMulAction [Monoid G₀] [AddMonoid M₀] [DistribMulAction G₀ M₀] :
DistribMulAction (Lex G₀) M₀ := inferInstanceAs DistribMulAction G₀ M₀

/--
Instance `instDistribMulAction'` / 实例 `instDistribMulAction'`

English:
instance instDistribMulAction'
  signature: [Monoid G₀] [AddMonoid M₀] [DistribMulAction G₀ M₀]
  body: inferInstanceAs DistribMulAction G₀ M₀

中文:
实例 instDistribMulAction'
  签名: [Monoid G₀] [AddMonoid M₀] [DistribMulAction G₀ M₀]
  定义体: inferInstanceAs DistribMulAction G₀ M₀

Depends on / 依赖: DistribMulAction
-/
instance instDistribMulAction' [Monoid G₀] [AddMonoid M₀] [DistribMulAction G₀ M₀] :
DistribMulAction G₀ (Lex M₀) := inferInstanceAs DistribMulAction G₀ M₀

/--
Instance `instMulActionWithZero` / 实例 `instMulActionWithZero`

English:
instance instMulActionWithZero
  signature: [MonoidWithZero G₀] [AddMonoid M₀] [MulActionWithZero G₀ M₀]
  body: inferInstanceAs MulActionWithZero G₀ M₀

中文:
实例 instMulActionWithZero
  签名: [MonoidWithZero G₀] [AddMonoid M₀] [MulActionWithZero G₀ M₀]
  定义体: inferInstanceAs MulActionWithZero G₀ M₀

Depends on / 依赖: CovariantClass, Group.covconv, MulActionWithZero, covconv
-/
instance instMulActionWithZero [MonoidWithZero G₀] [AddMonoid M₀] [MulActionWithZero G₀ M₀] :
MulActionWithZero (Lex G₀) M₀ := inferInstanceAs MulActionWithZero G₀ M₀

/--
Instance `instMulActionWithZero'` / 实例 `instMulActionWithZero'`

English:
instance instMulActionWithZero'
  signature: [MonoidWithZero G₀] [AddMonoid M₀] [MulActionWithZero G₀ M₀]
  body: inferInstanceAs MulActionWithZero G₀ M₀

中文:
实例 instMulActionWithZero'
  签名: [MonoidWithZero G₀] [AddMonoid M₀] [MulActionWithZero G₀ M₀]
  定义体: inferInstanceAs MulActionWithZero G₀ M₀

Depends on / 依赖: MulActionWithZero
-/
instance instMulActionWithZero' [MonoidWithZero G₀] [AddMonoid M₀] [MulActionWithZero G₀ M₀] :
MulActionWithZero G₀ (Lex M₀) := inferInstanceAs MulActionWithZero G₀ M₀

end Lex
