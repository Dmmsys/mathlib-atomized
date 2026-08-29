/-
Copyright (c) 2024 David Ang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ang
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.GroupTheory.GroupAction.Defs

/-!
# The subgroup of fixed points of an action
-/

@[expose] public section

variable (M α : Type*) [Monoid M]

section AddMonoid
variable [AddMonoid α] [DistribMulAction M α]

/--
Definition of `FixedPoints.addSubmonoid` / `FixedPoints.addSubmonoid` 的定义

English:
definition FixedPoints.addSubmonoid
  signature: : AddSubmonoid α where
  body: MulAction.fixedPoints M α
  zero_mem' := smul_zero
  add_mem' ha hb _ := by rw [smul_add, ha, hb]

@[simp]

中文:
定义 FixedPoints.addSubmonoid
  签名: : AddSubmonoid α where
  定义体: MulAction.fixedPoints M α
  zero_mem' := smul_zero
  add_mem' ha hb _ := by rw [smul_add, ha, hb]

@[simp]

Depends on / 依赖: MulAction, MulAction.fixedPoints, fixedPoints
-/
def FixedPoints.addSubmonoid : AddSubmonoid α where
  carrier := MulAction.fixedPoints M α
  zero_mem' := smul_zero
  add_mem' ha hb _ := by rw [smul_add, ha, hb]

@[simp]
/--
lemma `FixedPoints.mem_addSubmonoid` / 引理 `FixedPoints.mem_addSubmonoid`

English:
lemma FixedPoints.mem_addSubmonoid
  given: (a : α)
  statement: a in addSubmonoid M α ↔ forall m : M, m • a = a
  proof: Iff.rfl

中文:
引理 FixedPoints.mem_addSubmonoid
  条件: (a : α)
  结论: a in addSubmonoid M α ↔ 对任意 m : M, m • a = a
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma FixedPoints.mem_addSubmonoid (a : α) : a in addSubmonoid M α ↔ forall m : M, m • a = a :=
  Iff.rfl

end AddMonoid

section AddGroup
variable [AddGroup α] [DistribMulAction M α]

/--
Definition of `FixedPoints.addSubgroup` / `FixedPoints.addSubgroup` 的定义

English:
definition FixedPoints.addSubgroup
  signature: : AddSubgroup α where
  body: addSubmonoid M α
  neg_mem' ha _ := by rw [smul_neg, ha]

@[simp]

中文:
定义 FixedPoints.addSubgroup
  签名: : AddSubgroup α where
  定义体: addSubmonoid M α
  neg_mem' ha _ := by rw [smul_neg, ha]

@[simp]

Depends on / 依赖: addSubmonoid
-/
def FixedPoints.addSubgroup : AddSubgroup α where
  __ := addSubmonoid M α
  neg_mem' ha _ := by rw [smul_neg, ha]

@[simp]
/--
lemma `FixedPoints.mem_addSubgroup` / 引理 `FixedPoints.mem_addSubgroup`

English:
lemma FixedPoints.mem_addSubgroup
  given: (a : α)
  statement: a in FixedPoints.addSubgroup M α ↔ forall m : M, m • a = a
  proof: Iff.rfl

@[simp]

中文:
引理 FixedPoints.mem_addSubgroup
  条件: (a : α)
  结论: a in FixedPoints.addSubgroup M α ↔ 对任意 m : M, m • a = a
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
lemma FixedPoints.mem_addSubgroup (a : α) : a in FixedPoints.addSubgroup M α ↔ forall m : M, m • a = a :=
  Iff.rfl

@[simp]
/--
lemma `FixedPoints.addSubgroup_toAddSubmonoid` / 引理 `FixedPoints.addSubgroup_toAddSubmonoid`

English:
lemma FixedPoints.addSubgroup_toAddSubmonoid
  proof: rfl

中文:
引理 FixedPoints.addSubgroup_toAddSubmonoid
  证明: rfl
-/
lemma FixedPoints.addSubgroup_toAddSubmonoid :
    (FixedPoints.addSubgroup M α).toAddSubmonoid = addSubmonoid M α :=
  rfl

end AddGroup
