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
/-
**MulOpposite.instMulAction** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instMulAction [Monoid M] [MulAction M α] : MulAction M αᵐᵒᵖ where one_smul
 _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMulAction [Monoid M] [MulAction M α] : MulAction M αᵐᵒᵖ where
  one_smul _ := unop_injective <| one_smul _ _
  mul_smul _ _ _ := unop_injective <| mul_smul _ _ _

@[to_additive]
/-
**MulOpposite.instIsScalarTower** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instIsScalarTower [SMul M N] [SMul M α] [SMul N α] [IsScalarTower M N α] :
 IsScalarTower M N αᵐᵒᵖ where smul_assoc _ _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MulOpposite.unop_injective`：unop_injective : Injective (unop : αᵐᵒᵖ -> α
)
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
-/
instance instIsScalarTower [SMul M N] [SMul M α] [SMul N α] [IsScalarTower M N α] :
    IsScalarTower M N αᵐᵒᵖ where
  smul_assoc _ _ _ := unop_injective <| smul_assoc _ _ _

@[to_additive]
/-
**MulOpposite.instSMulCommClass** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instSMulCommClass [SMul M α] [SMul N α] [SMulCommClass M N α] : SMulCommCl
ass M N αᵐᵒᵖ where smul_comm _ _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MulOpposite.unop_injective`：unop_injective : Injective (unop : αᵐᵒᵖ -> α
)
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
-/
instance instSMulCommClass [SMul M α] [SMul N α] [SMulCommClass M N α] :
    SMulCommClass M N αᵐᵒᵖ where
  smul_comm _ _ _ := unop_injective <| smul_comm _ _ _

@[to_additive]
/-
**MulOpposite.instIsCentralScalar** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instIsCentralScalar [SMul M α] [SMul Mᵐᵒᵖ α] [IsCentralScalar M α] : IsCen
tralScalar M αᵐᵒᵖ where op_smul_eq_smul _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MulOpposite.unop_injective`：unop_injective : Injective (unop : αᵐᵒᵖ -> α
)
· 使用定理 `IsCentralScalar.op_smul_eq_smul`：∀ {M : Type u_9} {α : Type u_10} {inst 
: SMul M α} {inst_1 : SMul Mᵐᵒᵖ α} [self : IsCentralScalar M α] (m : M) (a : α),
   MulOpposite.op m •…
-/
instance instIsCentralScalar [SMul M α] [SMul Mᵐᵒᵖ α] [IsCentralScalar M α] :
    IsCentralScalar M αᵐᵒᵖ where
  op_smul_eq_smul _ _ := unop_injective <| op_smul_eq_smul _ _

@[to_additive]
/-
**MulOpposite.op_smul_eq_op_smul_op** 是 Mathlib 中的一个引理，位于命名空间 `MulOpposite`。
形式化陈述：op_smul_eq_op_smul_op [SMul M α] [SMul Mᵐᵒᵖ α] [IsCentralScalar M α] (r : 
M) (a : α) : op (r • a) = op r • op a
参数：r : M；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsCentralScalar.op_smul_eq_smul`：∀ {M : Type u_9} {α : Type u_10} {inst 
: SMul M α} {inst_1 : SMul Mᵐᵒᵖ α} [self : IsCentralScalar M α] (m : M) (a : α),
   MulOpposite.op m •…
-/
lemma op_smul_eq_op_smul_op [SMul M α] [SMul Mᵐᵒᵖ α] [IsCentralScalar M α] (r : M) (a : α) :
    op (r • a) = op r • op a := (op_smul_eq_smul r (op a)).symm

@[to_additive]
/-
**MulOpposite.unop_smul_eq_unop_smul_unop** 是 Mathlib 中的一个引理，位于命名空间 `MulOpposite
`。
形式化陈述：unop_smul_eq_unop_smul_unop [SMul M α] [SMul Mᵐᵒᵖ α] [IsCentralScalar M α]
 (r : Mᵐᵒᵖ) (a : αᵐᵒᵖ) : unop (r • a) = unop r • unop a
参数：r : Mᵐᵒᵖ；a : αᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `IsCentralScalar.unop_smul_eq_smul`：IsCentralScalar.unop_smul_eq_smul {M 
α : Type*} [SMul M α] [SMul Mᵐᵒᵖ α] [IsCentralScalar M α] (m : Mᵐᵒᵖ) (a : α) : M
ulOpposite.unop m • a =…
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
/-
**RightActions.** 是 Mathlib 中的一个示例，位于命名空间 `RightActions`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : a •> b = a • b := rfl
/-
**RightActions.** 是 Mathlib 中的一个示例，位于命名空间 `RightActions`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : b <• a = MulOpposite.op a • b := rfl
/-
**RightActions.** 是 Mathlib 中的一个示例，位于命名空间 `RightActions`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : a +ᵥ> b = a +ᵥ b := rfl
/-
**RightActions.** 是 Mathlib 中的一个示例，位于命名空间 `RightActions`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : b <+ᵥ a = AddOpposite.op a +ᵥ b := rfl

-- Left actions right-associate, right actions left-associate
/-
**RightActions.** 是 Mathlib 中的一个示例，位于命名空间 `RightActions`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : a₁ •> a₂ •> b = a₁ •> (a₂ •> b) := rfl
/-
**RightActions.** 是 Mathlib 中的一个示例，位于命名空间 `RightActions`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : b <• a₂ <• a₁ = (b <• a₂) <• a₁ := rfl
/-
**RightActions.** 是 Mathlib 中的一个示例，位于命名空间 `RightActions`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : a₁ +ᵥ> a₂ +ᵥ> b = a₁ +ᵥ> (a₂ +ᵥ> b) := rfl
/-
**RightActions.** 是 Mathlib 中的一个示例，位于命名空间 `RightActions`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : b <+ᵥ a₂ <+ᵥ a₁ = (b <+ᵥ a₂) <+ᵥ a₁ := rfl

-- When left and right actions coexist, they associate to the left
/-
**RightActions.** 是 Mathlib 中的一个示例，位于命名空间 `RightActions`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : a₁ •> b <• a₂ = (a₁ •> b) <• a₂ := rfl
/-
**RightActions.** 是 Mathlib 中的一个示例，位于命名空间 `RightActions`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : a₁ •> a₂ •> b <• a₃ <• a₄ = ((a₁ •> (a₂ •> b)) <• a₃) <• a₄ := rfl
/-
**RightActions.** 是 Mathlib 中的一个示例，位于命名空间 `RightActions`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : a₁ +ᵥ> b <+ᵥ a₂ = (a₁ +ᵥ> b) <+ᵥ a₂ := rfl
/-
**RightActions.** 是 Mathlib 中的一个示例，位于命名空间 `RightActions`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : a₁ +ᵥ> a₂ +ᵥ> b <+ᵥ a₃ <+ᵥ a₄ = ((a₁ +ᵥ> (a₂ +ᵥ> b)) <+ᵥ a₃) <+ᵥ a₄ := rfl

end examples
end RightActions

section
variable [Monoid α] [MulAction αᵐᵒᵖ β]

open scoped RightActions

@[to_additive]
/-
**op_smul_op_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：op_smul_op_smul (b : β) (a₁ a₂ : α) : b <• a₁ <• a₂ = b <• (a₁ * a₂)
参数：b : β；a₁ a₂ : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
-/
lemma op_smul_op_smul (b : β) (a₁ a₂ : α) : b <• a₁ <• a₂ = b <• (a₁ * a₂) := smul_smul _ _ _

@[to_additive]
/-
**op_smul_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：op_smul_mul (b : β) (a₁ a₂ : α) : b <• (a₁ * a₂) = b <• a₁ <• a₂
参数：b : β；a₁ a₂ : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
-/
lemma op_smul_mul (b : β) (a₁ a₂ : α) : b <• (a₁ * a₂) = b <• a₁ <• a₂ := mul_smul _ _ _

end

/-! ### Actions _by_ the opposite type (right actions) -/

open MulOpposite

@[to_additive]
/-
**Semigroup.opposite_smulCommClass** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Semigroup.opposite_smulCommClass [Semigroup α] : SMulCommClass αᵐᵒᵖ α α wh
ere smul_comm _ _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
instance Semigroup.opposite_smulCommClass [Semigroup α] : SMulCommClass αᵐᵒᵖ α α where
  smul_comm _ _ _ := mul_assoc _ _ _

@[to_additive]
/-
**Semigroup.opposite_smulCommClass'** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Semigroup.opposite_smulCommClass' [Semigroup α] : SMulCommClass α αᵐᵒᵖ α
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
-/
instance Semigroup.opposite_smulCommClass' [Semigroup α] : SMulCommClass α αᵐᵒᵖ α :=
  SMulCommClass.symm _ _ _

@[to_additive]
/-
**CommSemigroup.isCentralScalar** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：CommSemigroup.isCentralScalar [CommSemigroup α] : IsCentralScalar α α wher
e op_smul_eq_smul _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
instance CommSemigroup.isCentralScalar [CommSemigroup α] : IsCentralScalar α α where
  op_smul_eq_smul _ _ := mul_comm _ _

/-- Like `Monoid.toMulAction`, but multiplies on the right. -/
@[to_additive /-- Like `AddMonoid.toAddAction`, but adds on the right. -/]
/-
**Monoid.toOppositeMulAction** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Monoid.toOppositeMulAction [Monoid α] : MulAction αᵐᵒᵖ α where one_smul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Like `Monoid.toMulAction`, but multiplies on the right.
-/
instance Monoid.toOppositeMulAction [Monoid α] : MulAction αᵐᵒᵖ α where
  one_smul := mul_one
  mul_smul _ _ _ := (mul_assoc _ _ _).symm

@[to_additive]
/-
**IsScalarTower.opposite_mid** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsScalarTower.opposite_mid {M N} [Mul N] [SMul M N] [SMulCommClass M N N] 
: IsScalarTower M Nᵐᵒᵖ N where smul_assoc _ _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `mul_smul_comm`：mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s
 : α) (x y : β) : x * s • y = s • (x * y)
-/
instance IsScalarTower.opposite_mid {M N} [Mul N] [SMul M N] [SMulCommClass M N N] :
    IsScalarTower M Nᵐᵒᵖ N where
  smul_assoc _ _ _ := mul_smul_comm _ _ _

@[to_additive]
/-
**SMulCommClass.opposite_mid** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：SMulCommClass.opposite_mid {M N} [Mul N] [SMul M N] [IsScalarTower M N N] 
: SMulCommClass M Nᵐᵒᵖ N where smul_comm x y z
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance SMulCommClass.opposite_mid {M N} [Mul N] [SMul M N] [IsScalarTower M N N] :
    SMulCommClass M Nᵐᵒᵖ N where
  smul_comm x y z := by
    induction y using MulOpposite.rec'
    simp only [smul_mul_assoc, MulOpposite.smul_eq_mul_unop]

-- The above instance does not create an unwanted diamond, the two paths to
-- `MulAction αᵐᵒᵖ αᵐᵒᵖ` are defeq.
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example [Monoid α] : Monoid.toMulAction αᵐᵒᵖ = MulOpposite.instMulAction := by
  with_reducible_and_instances rfl
