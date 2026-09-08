/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Group.Action.Faithful
public import Mathlib.Algebra.Group.Action.Opposite
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero

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

assert_not_exists Ring

variable {M α : Type*}

/-! ### Actions _on_ the opposite type

Actions on the opposite type just act on the underlying type.
-/

namespace MulOpposite

/-
**MulOpposite.instSMulZeroClass** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instSMulZeroClass [AddMonoid α] [SMulZeroClass M α] : SMulZeroClass M αᵐᵒᵖ
 where smul_zero _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSMulZeroClass [AddMonoid α] [SMulZeroClass M α] : SMulZeroClass M αᵐᵒᵖ where
  smul_zero _ := unop_injective <| smul_zero _
/-
**MulOpposite.instSMulWithZero** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instSMulWithZero [MonoidWithZero M] [AddMonoid α] [SMulWithZero M α] : SMu
lWithZero M αᵐᵒᵖ where zero_smul _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSMulWithZero [MonoidWithZero M] [AddMonoid α] [SMulWithZero M α] :
    SMulWithZero M αᵐᵒᵖ where
  zero_smul _ := unop_injective <| zero_smul _ _
/-
**MulOpposite.instMulActionWithZero** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instMulActionWithZero [MonoidWithZero M] [AddMonoid α] [MulActionWithZero 
M α] : MulActionWithZero M αᵐᵒᵖ where smul_zero _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMulActionWithZero [MonoidWithZero M] [AddMonoid α] [MulActionWithZero M α] :
    MulActionWithZero M αᵐᵒᵖ where
  smul_zero _ := unop_injective <| smul_zero _
  zero_smul _ := unop_injective <| zero_smul _ _
/-
**MulOpposite.instDistribMulAction** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instDistribMulAction [Monoid M] [AddMonoid α] [DistribMulAction M α] : Dis
tribMulAction M αᵐᵒᵖ where smul_add _ _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDistribMulAction [Monoid M] [AddMonoid α] [DistribMulAction M α] :
    DistribMulAction M αᵐᵒᵖ where
  smul_add _ _ _ := unop_injective <| smul_add _ _ _
  smul_zero _ := unop_injective <| smul_zero _
/-
**MulOpposite.instMulDistribMulAction** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instMulDistribMulAction [Monoid M] [Monoid α] [MulDistribMulAction M α] : 
MulDistribMulAction M αᵐᵒᵖ where smul_mul _ _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMulDistribMulAction [Monoid M] [Monoid α] [MulDistribMulAction M α] :
    MulDistribMulAction M αᵐᵒᵖ where
  smul_mul _ _ _ := unop_injective <| smul_mul' _ _ _
  smul_one _ := unop_injective <| smul_one _

end MulOpposite


/-! ### Actions _by_ the opposite type (right actions)

In `Mul.toSMul` in another file, we define the left action `a₁ • a₂ = a₁ * a₂`. For the
multiplicative opposite, we define `MulOpposite.op a₁ • a₂ = a₂ * a₁`, with the multiplication
reversed.
-/

open MulOpposite

/-- `Monoid.toOppositeMulAction` is faithful on nontrivial cancellative monoids with zero. -/
/-
**IsLeftCancelMulZero.toFaithfulSMul_opposite** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsLeftCancelMulZero.toFaithfulSMul_opposite [MonoidWithZero α] [IsLeftCanc
elMulZero α] : FaithfulSMul αᵐᵒᵖ α where eq_of_smul_eq_smul h
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `MulOpposite.unop_injective`：unop_injective : Injective (unop : αᵐᵒᵖ -> α
)
· 使用定理 `mul_left_cancel₀`：mul_left_cancel₀ (ha : a != 0) (h : a * b = a * c) : b
 = c
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0

--- 原说明 ---
`Monoid.toOppositeMulAction` is faithful on nontrivial cancellative monoids with
 zero.
-/
instance IsLeftCancelMulZero.toFaithfulSMul_opposite [MonoidWithZero α] [IsLeftCancelMulZero α] :
    FaithfulSMul αᵐᵒᵖ α where
  eq_of_smul_eq_smul h := by
    cases subsingleton_or_nontrivial α
    · exact Subsingleton.elim ..
    · exact unop_injective <| mul_left_cancel₀ one_ne_zero (h 1)
