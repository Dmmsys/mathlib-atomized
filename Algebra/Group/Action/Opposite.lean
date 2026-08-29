/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Opposite

/-!
# Scalar actions on and by `Mᵐᵒᵖ`

This file defines the actions on the opposite type `SMul R Mᵐᵒᵖ`, and actions by the opposite
type, `SMul Rᵐᵒᵖ M`.

Note that `MulOpposite.smul` is provided in an earlier file as it is needed to
provide the `NSMul.nsmul` and `ZSMul.zsmul` fields.

## Notation

With `open scoped RightActions`, this provides:

* `r •> m` as an alias for `r • m`
* `m <• r` as an alias for `MulOpposite.op r • m`
* `v +ᵥ> p` as an alias for `v +ᵥ p`
* `p <+ᵥ v` as an alias for `AddOpposite.op v +ᵥ p`
-/

public section

assert_not_exists MonoidWithZero Units FaithfulSMul MonoidHom

variable {M N α β : Type*}

/-!
### Actions _on_ the opposite type

Actions on the opposite type just act on the underlying type.
-/

namespace MulOpposite

@[to_additive]
/--
Instance `instMulAction` / 实例 `instMulAction`

English:
instance instMulAction
  signature: [Monoid M] [MulAction M α]
  body: unop_injective one_smul _ _
mul_smul _ _ _ := unop_injective mul_smul _ _ _

@[to_additive]

中文:
实例 instMulAction
  签名: [幺半群 M] [乘法作用 M α]
  定义体: unop_injective one_smul _ _
mul_smul _ _ _ := unop_injective mul_smul _ _ _

@[to_additive]

Depends on / 依赖: one_smul, unop_injective
-/
instance instMulAction [Monoid M] [MulAction M α] : MulAction M αᵐᵒᵖ where
one_smul _ := unop_injective one_smul _ _
mul_smul _ _ _ := unop_injective mul_smul _ _ _

@[to_additive]
/--
Instance `instIsScalarTower` / 实例 `instIsScalarTower`

English:
instance instIsScalarTower
  signature: [SMul M N] [SMul M α] [SMul N α] [IsScalarTower M N α]
  body: unop_injective smul_assoc _ _ _

@[to_additive]

中文:
实例 instIsScalarTower
  签名: [标量乘法 M N] [标量乘法 M α] [标量乘法 N α] [标量塔 M N α]
  定义体: unop_injective smul_assoc _ _ _

@[to_additive]

Depends on / 依赖: smul_assoc, unop_injective
-/
instance instIsScalarTower [SMul M N] [SMul M α] [SMul N α] [IsScalarTower M N α] :
    IsScalarTower M N αᵐᵒᵖ where
smul_assoc _ _ _ := unop_injective smul_assoc _ _ _

@[to_additive]
/--
Instance `instSMulCommClass` / 实例 `instSMulCommClass`

English:
instance instSMulCommClass
  signature: [SMul M α] [SMul N α] [SMulCommClass M N α]
  body: unop_injective smul_comm _ _ _

@[to_additive]

中文:
实例 instSMulCommClass
  签名: [标量乘法 M α] [标量乘法 N α] [标量交换类 M N α]
  定义体: unop_injective smul_comm _ _ _

@[to_additive]

Depends on / 依赖: smul_comm, unop_injective
-/
instance instSMulCommClass [SMul M α] [SMul N α] [SMulCommClass M N α] :
    SMulCommClass M N αᵐᵒᵖ where
smul_comm _ _ _ := unop_injective smul_comm _ _ _

@[to_additive]
/--
Instance `instIsCentralScalar` / 实例 `instIsCentralScalar`

English:
instance instIsCentralScalar
  signature: [SMul M α] [SMul Mᵐᵒᵖ α] [IsCentralScalar M α]
  body: unop_injective op_smul_eq_smul _ _

@[to_additive]

中文:
实例 instIsCentralScalar
  签名: [标量乘法 M α] [标量乘法 Mᵐᵒᵖ α] [中心标量 M α]
  定义体: unop_injective op_smul_eq_smul _ _

@[to_additive]

Depends on / 依赖: op_smul_eq_smul, unop_injective
-/
instance instIsCentralScalar [SMul M α] [SMul Mᵐᵒᵖ α] [IsCentralScalar M α] :
    IsCentralScalar M αᵐᵒᵖ where
op_smul_eq_smul _ _ := unop_injective op_smul_eq_smul _ _

@[to_additive]
/--
lemma `op_smul_eq_op_smul_op` / 引理 `op_smul_eq_op_smul_op`

English:
lemma op_smul_eq_op_smul_op
  given: [SMul M α] [SMul Mᵐᵒᵖ α] [IsCentralScalar M α] (r : M) (a : α)
  proof: (op_smul_eq_smul r (op a)).symm

@[to_additive]

中文:
引理 op_smul_eq_op_smul_op
  条件: [标量乘法 M α] [标量乘法 Mᵐᵒᵖ α] [中心标量 M α] (r : M) (a : α)
  证明: (op_smul_eq_smul r (op a)).symm

@[to_additive]

Depends on / 依赖: op_smul_eq_smul
-/
lemma op_smul_eq_op_smul_op [SMul M α] [SMul Mᵐᵒᵖ α] [IsCentralScalar M α] (r : M) (a : α) :
    op (r • a) = op r • op a := (op_smul_eq_smul r (op a)).symm

@[to_additive]
/--
lemma `unop_smul_eq_unop_smul_unop` / 引理 `unop_smul_eq_unop_smul_unop`

English:
lemma unop_smul_eq_unop_smul_unop
  statement: [SMul M α] [SMul Mᵐᵒᵖ α] [IsCentralScalar M α] (r : Mᵐᵒᵖ)
  proof: (unop_smul_eq_smul r (unop a)).symm

中文:
引理 unop_smul_eq_unop_smul_unop
  结论: [标量乘法 M α] [标量乘法 Mᵐᵒᵖ α] [中心标量 M α] (r : Mᵐᵒᵖ)
  证明: (unop_smul_eq_smul r (unop a)).symm

Depends on / 依赖: unop_smul_eq_smul
-/
lemma unop_smul_eq_unop_smul_unop [SMul M α] [SMul Mᵐᵒᵖ α] [IsCentralScalar M α] (r : Mᵐᵒᵖ)
    (a : αᵐᵒᵖ) : unop (r • a) = unop r • unop a := (unop_smul_eq_smul r (unop a)).symm

end MulOpposite

/-!
### Right actions

In this section we establish `SMul αᵐᵒᵖ β` as the canonical spelling of right scalar multiplication
of `β` by `α`, and provide convenient notations.
-/

namespace RightActions

/-- With `open scoped RightActions`, an alternative symbol for left actions, `r • m`.

In lemma names this is still called `smul`. -/
scoped notation3:74 r:75 " •> " m:74 => r • m

/-- With `open scoped RightActions`, a shorthand for right actions, `op r • m`.

In lemma names this is still called `op_smul`. -/
scoped notation3:73 m:73 " <• " r:74 => MulOpposite.op r • m

/-- With `open scoped RightActions`, an alternative symbol for left actions, `r +ᵥ m`.

In lemma names this is still called `vadd`. -/
scoped notation3:74 r:75 " +ᵥ> " m:74 => r +ᵥ m

/-- With `open scoped RightActions`, a shorthand for right actions, `op r +ᵥ m`.

In lemma names this is still called `op_vadd`. -/
scoped notation3:73 m:73 " <+ᵥ " r:74 => AddOpposite.op r +ᵥ m

section examples
variable [SMul α β] [SMul αᵐᵒᵖ β] [VAdd α β] [VAdd αᵃᵒᵖ β] {a a₁ a₂ a₃ a₄ : α} {b : β}

-- Left and right actions are just notation around the general `•` and `+ᵥ` notations
example : a •> b = a • b := rfl
example : b <• a = MulOpposite.op a • b := rfl

example : a +ᵥ> b = a +ᵥ b := rfl
example : b <+ᵥ a = AddOpposite.op a +ᵥ b := rfl

-- Left actions right-associate, right actions left-associate
example : a₁ •> a₂ •> b = a₁ •> (a₂ •> b) := rfl
example : b <• a₂ <• a₁ = (b <• a₂) <• a₁ := rfl

example : a₁ +ᵥ> a₂ +ᵥ> b = a₁ +ᵥ> (a₂ +ᵥ> b) := rfl
example : b <+ᵥ a₂ <+ᵥ a₁ = (b <+ᵥ a₂) <+ᵥ a₁ := rfl

-- When left and right actions coexist, they associate to the left
example : a₁ •> b <• a₂ = (a₁ •> b) <• a₂ := rfl
example : a₁ •> a₂ •> b <• a₃ <• a₄ = ((a₁ •> (a₂ •> b)) <• a₃) <• a₄ := rfl

example : a₁ +ᵥ> b <+ᵥ a₂ = (a₁ +ᵥ> b) <+ᵥ a₂ := rfl
example : a₁ +ᵥ> a₂ +ᵥ> b <+ᵥ a₃ <+ᵥ a₄ = ((a₁ +ᵥ> (a₂ +ᵥ> b)) <+ᵥ a₃) <+ᵥ a₄ := rfl

end examples
end RightActions

section
variable [Monoid α] [MulAction αᵐᵒᵖ β]

open scoped RightActions

@[to_additive]
/--
lemma `op_smul_op_smul` / 引理 `op_smul_op_smul`

English:
lemma op_smul_op_smul
  given: (b : β) (a₁ a₂ : α)
  statement: b <• a₁ <• a₂ = b <• (a₁ * a₂)
  proof: smul_smul _ _ _

@[to_additive]

中文:
引理 op_smul_op_smul
  条件: (b : β) (a₁ a₂ : α)
  结论: b <• a₁ <• a₂ = b <• (a₁ * a₂)
  证明: smul_smul _ _ _

@[to_additive]

Depends on / 依赖: smul_smul
-/
lemma op_smul_op_smul (b : β) (a₁ a₂ : α) : b <• a₁ <• a₂ = b <• (a₁ * a₂) := smul_smul _ _ _

@[to_additive]
/--
lemma `op_smul_mul` / 引理 `op_smul_mul`

English:
lemma op_smul_mul
  given: (b : β) (a₁ a₂ : α)
  statement: b <• (a₁ * a₂) = b <• a₁ <• a₂
  proof: mul_smul _ _ _

中文:
引理 op_smul_mul
  条件: (b : β) (a₁ a₂ : α)
  结论: b <• (a₁ * a₂) = b <• a₁ <• a₂
  证明: mul_smul _ _ _

Depends on / 依赖: mul_smul
-/
lemma op_smul_mul (b : β) (a₁ a₂ : α) : b <• (a₁ * a₂) = b <• a₁ <• a₂ := mul_smul _ _ _

end

/-! ### Actions _by_ the opposite type (right actions) -/

open MulOpposite

@[to_additive]
/--
Instance `Semigroup.opposite_smulCommClass` / 实例 `Semigroup.opposite_smulCommClass`

English:
instance Semigroup.opposite_smulCommClass
  signature: [Semigroup α]
  body: mul_assoc _ _ _

@[to_additive]

中文:
实例 半群.opposite_smulCommClass
  签名: [半群 α]
  定义体: mul_assoc _ _ _

@[to_additive]

Depends on / 依赖: mul_assoc
-/
instance Semigroup.opposite_smulCommClass [Semigroup α] : SMulCommClass αᵐᵒᵖ α α where
  smul_comm _ _ _ := mul_assoc _ _ _

@[to_additive]
/--
Instance `Semigroup.opposite_smulCommClass'` / 实例 `Semigroup.opposite_smulCommClass'`

English:
instance Semigroup.opposite_smulCommClass'
  signature: [Semigroup α]
  body: SMulCommClass.symm _ _ _

@[to_additive]

中文:
实例 半群.opposite_smulCommClass'
  签名: [半群 α]
  定义体: SMulCommClass.symm _ _ _

@[to_additive]

Depends on / 依赖: SMulCommClass, SMulCommClass.symm
-/
instance Semigroup.opposite_smulCommClass' [Semigroup α] : SMulCommClass α αᵐᵒᵖ α :=
  SMulCommClass.symm _ _ _

@[to_additive]
/--
Instance `CommSemigroup.isCentralScalar` / 实例 `CommSemigroup.isCentralScalar`

English:
instance CommSemigroup.isCentralScalar
  signature: [CommSemigroup α]
  body: mul_comm _ _

中文:
实例 交换半群.isCentralScalar
  签名: [交换半群 α]
  定义体: mul_comm _ _

Depends on / 依赖: mul_comm
-/
instance CommSemigroup.isCentralScalar [CommSemigroup α] : IsCentralScalar α α where
  op_smul_eq_smul _ _ := mul_comm _ _

/-- Like `Monoid.toMulAction`, but multiplies on the right. -/
@[to_additive /-- Like `AddMonoid.toAddAction`, but adds on the right. -/]
/--
Instance `Monoid.toOppositeMulAction` / 实例 `Monoid.toOppositeMulAction`

English:
instance Monoid.toOppositeMulAction
  signature: [Monoid α]
  body: mul_one
  mul_smul _ _ _ := (mul_assoc _ _ _).symm

@[to_additive]

中文:
实例 幺半群.toOppositeMulAction
  签名: [幺半群 α]
  定义体: mul_one
  mul_smul _ _ _ := (mul_assoc _ _ _).symm

@[to_additive]

Depends on / 依赖: Nat.mul_succ, Nat.strongRecOn, mul_assoc, mul_one, mul_succ, npowRec, strongRecOn
-/
instance Monoid.toOppositeMulAction [Monoid α] : MulAction αᵐᵒᵖ α where
  one_smul := mul_one
  mul_smul _ _ _ := (mul_assoc _ _ _).symm

@[to_additive]
/--
Instance `IsScalarTower.opposite_mid` / 实例 `IsScalarTower.opposite_mid`

English:
instance IsScalarTower.opposite_mid
  signature: {M N} [Mul N] [SMul M N] [SMulCommClass M N N]
  body: mul_smul_comm _ _ _

@[to_additive]

中文:
实例 标量塔.opposite_mid
  签名: {M N} [乘法 N] [标量乘法 M N] [标量交换类 M N N]
  定义体: mul_smul_comm _ _ _

@[to_additive]

Depends on / 依赖: Nat.strongRecOn, mul_assoc, mul_smul_comm, npowRec, strongRecOn
-/
instance IsScalarTower.opposite_mid {M N} [Mul N] [SMul M N] [SMulCommClass M N N] :
    IsScalarTower M Nᵐᵒᵖ N where
  smul_assoc _ _ _ := mul_smul_comm _ _ _

@[to_additive]
/--
Instance `SMulCommClass.opposite_mid` / 实例 `SMulCommClass.opposite_mid`

English:
instance SMulCommClass.opposite_mid
  signature: {M N} [Mul N] [SMul M N] [IsScalarTower M N N]
  body: by
    induction y using MulOpposite.rec'
    simp only [smul_mul_assoc, MulOpposite.smul_eq_mul_unop]

中文:
实例 标量交换类.opposite_mid
  签名: {M N} [乘法 N] [标量乘法 M N] [标量塔 M N N]
  定义体: by
    induction y using MulOpposite.rec'
    simp only [smul_mul_assoc, MulOpposite.smul_eq_mul_unop]

Depends on / 依赖: MulOpposite, MulOpposite.rec, MulOpposite.smul_eq_mul_unop, smul_eq_mul_unop, smul_mul_assoc
-/
instance SMulCommClass.opposite_mid {M N} [Mul N] [SMul M N] [IsScalarTower M N N] :
    SMulCommClass M Nᵐᵒᵖ N where
  smul_comm x y z := by
    induction y using MulOpposite.rec'
    simp only [smul_mul_assoc, MulOpposite.smul_eq_mul_unop]

-- The above instance does not create an unwanted diamond, the two paths to
-- `MulAction αᵐᵒᵖ αᵐᵒᵖ` are defeq.
example [Monoid α] : Monoid.toMulAction αᵐᵒᵖ = MulOpposite.instMulAction := by
  with_reducible_and_instances rfl
