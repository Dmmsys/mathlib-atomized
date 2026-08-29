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

/--
Instance `unitsMulSemiringAction` / 实例 `unitsMulSemiringAction`

English:
instance unitsMulSemiringAction
  signature: : MulSemiringAction (ConjAct Rˣ) R
  body: { ConjAct.unitsMulDistribMulAction with
    smul_zero := by simp [units_smul_def]
    smul_add := by simp [units_smul_def, mul_add, add_mul] }

中文:
实例 unitsMulSemiringAction
  签名: : MulSemiringAction (ConjAct Rˣ) R
  定义体: { ConjAct.unitsMulDistribMulAction with
    smul_zero := by simp [units_smul_def]
    smul_add := by simp [units_smul_def, mul_add, add_mul] }

Depends on / 依赖: ConjAct, ConjAct.unitsMulDistribMulAction, add_mul, mul_add, smul_add, smul_zero, unitsMulDistribMulAction, units_smul_def
-/
instance unitsMulSemiringAction : MulSemiringAction (ConjAct Rˣ) R :=
  { ConjAct.unitsMulDistribMulAction with
    smul_zero := by simp [units_smul_def]
    smul_add := by simp [units_smul_def, mul_add, add_mul] }

end ConjAct
