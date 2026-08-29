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

/--
Instance `instSMulZeroClass` / 实例 `instSMulZeroClass`

English:
instance instSMulZeroClass
  signature: [AddMonoid α] [SMulZeroClass M α]
  body: unop_injective smul_zero _

中文:
实例 instSMulZeroClass
  签名: [加法幺半群 α] [SMulZero类 M α]
  定义体: unop_injective smul_zero _

Depends on / 依赖: smul_zero, unop_injective
-/
instance instSMulZeroClass [AddMonoid α] [SMulZeroClass M α] : SMulZeroClass M αᵐᵒᵖ where
smul_zero _ := unop_injective smul_zero _

/--
Instance `instSMulWithZero` / 实例 `instSMulWithZero`

English:
instance instSMulWithZero
  signature: [MonoidWithZero M] [AddMonoid α] [SMulWithZero M α]
  body: unop_injective zero_smul _ _

中文:
实例 instSMulWithZero
  签名: [带零幺半群 M] [加法幺半群 α] [带零标量乘法 M α]
  定义体: unop_injective zero_smul _ _

Depends on / 依赖: unop_injective, zero_smul
-/
instance instSMulWithZero [MonoidWithZero M] [AddMonoid α] [SMulWithZero M α] :
    SMulWithZero M αᵐᵒᵖ where
zero_smul _ := unop_injective zero_smul _ _

/--
Instance `instMulActionWithZero` / 实例 `instMulActionWithZero`

English:
instance instMulActionWithZero
  signature: [MonoidWithZero M] [AddMonoid α] [MulActionWithZero M α]
  body: unop_injective smul_zero _
zero_smul _ := unop_injective zero_smul _ _

中文:
实例 instMulActionWithZero
  签名: [带零幺半群 M] [加法幺半群 α] [带零乘法作用 M α]
  定义体: unop_injective smul_zero _
zero_smul _ := unop_injective zero_smul _ _

Depends on / 依赖: smul_zero, unop_injective
-/
instance instMulActionWithZero [MonoidWithZero M] [AddMonoid α] [MulActionWithZero M α] :
    MulActionWithZero M αᵐᵒᵖ where
smul_zero _ := unop_injective smul_zero _
zero_smul _ := unop_injective zero_smul _ _

/--
Instance `instDistribMulAction` / 实例 `instDistribMulAction`

English:
instance instDistribMulAction
  signature: [Monoid M] [AddMonoid α] [DistribMulAction M α]
  body: unop_injective smul_add _ _ _
smul_zero _ := unop_injective smul_zero _

中文:
实例 instDistribMulAction
  签名: [幺半群 M] [加法幺半群 α] [分配乘法作用 M α]
  定义体: unop_injective smul_add _ _ _
smul_zero _ := unop_injective smul_zero _

Depends on / 依赖: smul_add, unop_injective
-/
instance instDistribMulAction [Monoid M] [AddMonoid α] [DistribMulAction M α] :
    DistribMulAction M αᵐᵒᵖ where
smul_add _ _ _ := unop_injective smul_add _ _ _
smul_zero _ := unop_injective smul_zero _

/--
Instance `instMulDistribMulAction` / 实例 `instMulDistribMulAction`

English:
instance instMulDistribMulAction
  signature: [Monoid M] [Monoid α] [MulDistribMulAction M α]
  body: unop_injective smul_mul' _ _ _
smul_one _ := unop_injective smul_one _

中文:
实例 instMulDistribMulAction
  签名: [幺半群 M] [幺半群 α] [MulDistribMul作用 M α]
  定义体: unop_injective smul_mul' _ _ _
smul_one _ := unop_injective smul_one _

Depends on / 依赖: smul_mul, unop_injective
-/
instance instMulDistribMulAction [Monoid M] [Monoid α] [MulDistribMulAction M α] :
    MulDistribMulAction M αᵐᵒᵖ where
smul_mul _ _ _ := unop_injective smul_mul' _ _ _
smul_one _ := unop_injective smul_one _

end MulOpposite


/-! ### Actions _by_ the opposite type (right actions)

In `Mul.toSMul` in another file, we define the left action `a₁ • a₂ = a₁ * a₂`. For the
multiplicative opposite, we define `MulOpposite.op a₁ • a₂ = a₂ * a₁`, with the multiplication
reversed.
-/

open MulOpposite

/--
Instance `IsLeftCancelMulZero.toFaithfulSMul_opposite` / 实例 `IsLeftCancelMulZero.toFaithfulSMul_opposite`

English:
instance IsLeftCancelMulZero.toFaithfulSMul_opposite
  signature: [MonoidWithZero α] [IsLeftCancelMulZero α]
  body: by
    cases subsingleton_or_nontrivial α
    · exact Subsingleton.elim ..
· exact unop_injective mul_left_cancel₀ one_ne_zero (h 1)

中文:
实例 是左消去MulZero.toFaithfulSMul_opposite
  签名: [带零幺半群 α] [是左消去MulZero α]
  定义体: by
    cases subsingleton_or_nontrivial α
    · exact Subsingleton.elim ..
· exact unop_injective mul_left_cancel₀ one_ne_zero (h 1)

Depends on / 依赖: Subsingleton, Subsingleton.elim, one_ne_zero, subsingleton_or_nontrivial, unop_injective
-/
instance IsLeftCancelMulZero.toFaithfulSMul_opposite [MonoidWithZero α] [IsLeftCancelMulZero α] :
    FaithfulSMul αᵐᵒᵖ α where
  eq_of_smul_eq_smul h := by
    cases subsingleton_or_nontrivial α
    · exact Subsingleton.elim ..
· exact unop_injective mul_left_cancel₀ one_ne_zero (h 1)
