/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.GroupWithZero.Action.ConjAct
public import Mathlib.Algebra.GroupWithZero.Action.Defs

/-!
# Conjugation action of a field on itself
-/

public section

namespace ConjAct

variable {K : Type*} [DivisionRing K]

/-
**ConjAct.distribMulAction** 是 Mathlib 中的一个实例，位于命名空间 `ConjAct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance distribMulAction₀ : DistribMulAction (ConjAct K) K :=
  { ConjAct.mulAction₀ with
    smul_zero := by simp [smul_def]
    smul_add := by simp [smul_def, mul_add, add_mul] }

end ConjAct

