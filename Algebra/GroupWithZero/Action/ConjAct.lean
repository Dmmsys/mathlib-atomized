/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Conjugation action of a group with zero on itself
-/

public section

assert_not_exists Ring

variable {α G₀ : Type*}

namespace ConjAct
variable [GroupWithZero G₀]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: GroupWithZero (ConjAct G₀)
  body: inferInstanceAs GroupWithZero G₀

中文:
实例 :
  签名: GroupWithZero (ConjAct G₀)
  定义体: inferInstanceAs GroupWithZero G₀

Depends on / 依赖: GroupWithZero
-/
instance : GroupWithZero (ConjAct G₀) := inferInstanceAs GroupWithZero G₀

/--
lemma `ofConjAct_zero` / 引理 `ofConjAct_zero`

English:
lemma ofConjAct_zero
  statement: ofConjAct 0 = (0 : G₀)
  proof: rfl

中文:
引理 ofConjAct_zero
  结论: ofConjAct 0 = (0 : G₀)
  证明: rfl
-/
@[simp] lemma ofConjAct_zero : ofConjAct 0 = (0 : G₀) := rfl
/--
lemma `toConjAct_zero` / 引理 `toConjAct_zero`

English:
lemma toConjAct_zero
  statement: toConjAct (0 : G₀) = 0
  proof: rfl

中文:
引理 toConjAct_zero
  结论: toConjAct (0 : G₀) = 0
  证明: rfl
-/
@[simp] lemma toConjAct_zero : toConjAct (0 : G₀) = 0 := rfl

/--
Instance `mulAction₀` / 实例 `mulAction₀`

English:
instance mulAction₀
  signature: : MulAction (ConjAct G₀) G₀ where
  body: by simp [smul_def]
  mul_smul := by simp [smul_def, mul_assoc]

中文:
实例 mulAction₀
  签名: : MulAction (ConjAct G₀) G₀ where
  定义体: by simp [smul_def]
  mul_smul := by simp [smul_def, mul_assoc]

Depends on / 依赖: mul_assoc, mul_smul, smul_def
-/
instance mulAction₀ : MulAction (ConjAct G₀) G₀ where
  one_smul := by simp [smul_def]
  mul_smul := by simp [smul_def, mul_assoc]

/--
Instance `smulCommClass₀` / 实例 `smulCommClass₀`

English:
instance smulCommClass₀
  signature: [SMul α G₀] [SMulCommClass α G₀ G₀] [IsScalarTower α G₀ G₀]
  body: by rw [smul_def, smul_def, mul_smul_comm, smul_mul_assoc]

中文:
实例 smulCommClass₀
  签名: [SMul α G₀] [SMulCommClass α G₀ G₀] [IsScalarTower α G₀ G₀]
  定义体: by rw [smul_def, smul_def, mul_smul_comm, smul_mul_assoc]

Depends on / 依赖: mul_smul_comm, smul_def, smul_mul_assoc
-/
instance smulCommClass₀ [SMul α G₀] [SMulCommClass α G₀ G₀] [IsScalarTower α G₀ G₀] :
    SMulCommClass α (ConjAct G₀) G₀ where
  smul_comm a ug g := by rw [smul_def, smul_def, mul_smul_comm, smul_mul_assoc]

/--
Instance `smulCommClass₀'` / 实例 `smulCommClass₀'`

English:
instance smulCommClass₀'
  signature: [SMul α G₀] [SMulCommClass G₀ α G₀] [IsScalarTower α G₀ G₀]
  body: haveI := SMulCommClass.symm G₀ α G₀
  .symm ..

中文:
实例 smulCommClass₀'
  签名: [SMul α G₀] [SMulCommClass G₀ α G₀] [IsScalarTower α G₀ G₀]
  定义体: haveI := SMulCommClass.symm G₀ α G₀
  .symm ..

Depends on / 依赖: SMulCommClass, SMulCommClass.symm
-/
instance smulCommClass₀' [SMul α G₀] [SMulCommClass G₀ α G₀] [IsScalarTower α G₀ G₀] :
    SMulCommClass (ConjAct G₀) α G₀ :=
  haveI := SMulCommClass.symm G₀ α G₀
  .symm ..

end ConjAct
