/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Ring.Action.Basic
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Conjugation action of a ring on itself
-/

public section

assert_not_exists Field

namespace ConjAct
variable {R : Type*} [Semiring R]

/-
**ConjAct.unitsMulSemiringAction** 是 Mathlib 中的一个实例，位于命名空间 `ConjAct`。
形式化陈述：unitsMulSemiringAction : MulSemiringAction (ConjAct Rˣ) R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance unitsMulSemiringAction : MulSemiringAction (ConjAct Rˣ) R :=
  { ConjAct.unitsMulDistribMulAction with
    smul_zero := by simp [units_smul_def]
    smul_add := by simp [units_smul_def, mul_add, add_mul] }

end ConjAct

