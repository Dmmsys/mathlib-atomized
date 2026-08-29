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

/--
Instance `distribMulAction₀` / 实例 `distribMulAction₀`

English:
instance distribMulAction₀
  signature: : DistribMulAction (ConjAct K) K
  body: { ConjAct.mulAction₀ with
    smul_zero := by simp [smul_def]
    smul_add := by simp [smul_def, mul_add, add_mul] }

中文:
实例 distribMulAction₀
  签名: : 分配乘法作用 (ConjAct K) K
  定义体: { ConjAct.mulAction₀ with
    smul_zero := by simp [smul_def]
    smul_add := by simp [smul_def, mul_add, add_mul] }

Depends on / 依赖: ConjAct, ConjAct.mulAction, add_mul, mul_add, smul_add, smul_def, smul_zero
-/
instance distribMulAction₀ : DistribMulAction (ConjAct K) K :=
  { ConjAct.mulAction₀ with
    smul_zero := by simp [smul_def]
    smul_add := by simp [smul_def, mul_add, add_mul] }

end ConjAct
