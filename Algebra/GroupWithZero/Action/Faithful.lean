/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yury Kudryashov
-/
module -- shake: keep-all

public import Mathlib.Algebra.Group.Action.Faithful
public import Mathlib.Algebra.GroupWithZero.NeZero

/-!
# Faithful actions involving groups with zero
-/
deprecated_module (since := "2026-02-03")

public section

assert_not_exists Equiv.Perm.equivUnitsEnd Prod.fst_mul Ring

open Function

variable {α : Type*}

/-- `Monoid.toMulAction` is faithful on nontrivial cancellative monoids with zero. -/
@[nolint unusedArguments, deprecated "subsumed by `instFaithfulSMul`" (since := "2026-02-03")]
/-
**IsRightCancelMulZero.faithfulSMul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsRightCancelMulZero.faithfulSMul [MonoidWithZero α] [IsRightCancelMulZero
 α] : FaithfulSMul α α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instFaithfulSMul`：∀ (R : Type u_4) [inst : MulOneClass R], FaithfulSMul 
R R

--- 原说明 ---
`Monoid.toMulAction` is faithful on nontrivial cancellative monoids with zero.
-/
lemma IsRightCancelMulZero.faithfulSMul [MonoidWithZero α] [IsRightCancelMulZero α] :
    FaithfulSMul α α := inferInstance
