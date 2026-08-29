/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Group.Defs

/-!
# `PUnit` is a commutative group

This file collects facts about algebraic structures on the one-element type, e.g. that it is a
commutative ring.
-/

public section

assert_not_exists MonoidWithZero

namespace PUnit

@[to_additive]
/--
Instance `commGroup` / 实例 `commGroup`

English:
instance commGroup
  signature: : CommGroup PUnit where
  body: unit
  one := unit
  inv _ := unit
  div _ _ := unit
  npow _ _ := unit
  zpow _ _ := unit
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
  inv_mul_cancel _ := rfl
  mul_comm _ _ := rfl

中文:
实例 commGroup
  签名: : 交换群 命题单元 where
  定义体: unit
  one := unit
  inv _ := unit
  div _ _ := unit
  npow _ _ := unit
  zpow _ _ := unit
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
  inv_mul_cancel _ := rfl
  mul_comm _ _ := rfl
-/
instance commGroup : CommGroup PUnit where
  mul _ _ := unit
  one := unit
  inv _ := unit
  div _ _ := unit
  npow _ _ := unit
  zpow _ _ := unit
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
  inv_mul_cancel _ := rfl
  mul_comm _ _ := rfl

-- shortcut instances
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One PUnit
  body: unit

中文:
实例 :
  签名: 幺 命题单元
  定义体: unit
-/
@[to_additive] instance : One PUnit where one := unit
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul PUnit
  body: unit

中文:
实例 :
  签名: 乘法 命题单元
  定义体: unit
-/
@[to_additive] instance : Mul PUnit where mul _ _ := unit
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Div PUnit
  body: unit

中文:
实例 :
  签名: 除法 命题单元
  定义体: unit
-/
@[to_additive] instance : Div PUnit where div _ _ := unit
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inv PUnit
  body: unit

中文:
实例 :
  签名: 取逆 命题单元
  定义体: unit
-/
@[to_additive] instance : Inv PUnit where inv _ := unit

/--
lemma `one_eq` / 引理 `one_eq`

English:
lemma one_eq
  statement: (1 : PUnit) = unit
  proof: rfl

中文:
引理 one_eq
  结论: (1 : 命题单元) = unit
  证明: rfl
-/
@[to_additive (attr := simp)] lemma one_eq : (1 : PUnit) = unit := rfl

-- note simp can prove this when the Boolean ring structure is introduced
/--
lemma `mul_eq` / 引理 `mul_eq`

English:
lemma mul_eq
  given: (x y : PUnit)
  statement: x * y = unit
  proof: rfl

中文:
引理 mul_eq
  条件: (x y : 命题单元)
  结论: x * y = unit
  证明: rfl
-/
@[to_additive] lemma mul_eq (x y : PUnit) : x * y = unit := rfl

/--
lemma `div_eq` / 引理 `div_eq`

English:
lemma div_eq
  given: (x y : PUnit)
  statement: x / y = unit
  proof: rfl

中文:
引理 div_eq
  条件: (x y : 命题单元)
  结论: x / y = unit
  证明: rfl
-/
@[to_additive (attr := simp)] lemma div_eq (x y : PUnit) : x / y = unit := rfl
/--
lemma `inv_eq` / 引理 `inv_eq`

English:
lemma inv_eq
  given: (x : PUnit)
  statement: x⁻¹ = unit
  proof: rfl

中文:
引理 inv_eq
  条件: (x : 命题单元)
  结论: x⁻¹ = unit
  证明: rfl
-/
@[to_additive (attr := simp)] lemma inv_eq (x : PUnit) : x⁻¹ = unit := rfl

end PUnit
