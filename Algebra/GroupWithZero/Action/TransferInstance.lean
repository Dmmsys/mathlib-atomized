/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Action.TransferInstance
public import Mathlib.Algebra.GroupWithZero.Action.Defs

/-!
# Transfer algebraic structures across `Equiv`s

This continues the pattern set in `Mathlib/Algebra/Group/TransferInstance.lean`.
-/

public section

assert_not_exists Ring

variable {M M₀ A B : Type*}

namespace Equiv

variable (M) in
/--
Definition of `smulZeroClass` / `smulZeroClass` 的定义

English:
abbreviation smulZeroClass
  signature: (e : A ≃ B) [Zero B] [SMulZeroClass M B]
  body: e.zero
    SMulZeroClass M A := by
  letI := e.zero
  exact {
    e.smul M with
    smul_zero := by simp [smul_def, zero_def]
  }

中文:
缩写 smulZeroClass
  签名: (e : A ≃ B) [Zero B] [SMulZeroClass M B]
  定义体: e.zero
    SMulZeroClass M A := by
  letI := e.zero
  exact {
    e.smul M with
    smul_zero := by simp [smul_def, zero_def]
  }
-/
protected abbrev smulZeroClass (e : A ≃ B) [Zero B] [SMulZeroClass M B] :
    letI := e.zero
    SMulZeroClass M A := by
  letI := e.zero
  exact {
    e.smul M with
    smul_zero := by simp [smul_def, zero_def]
  }

variable (M₀) in
/--
Definition of `smulWithZero` / `smulWithZero` 的定义

English:
abbreviation smulWithZero
  signature: (e : A ≃ B) [Zero M₀] [Zero B] [SMulWithZero M₀ B]
  body: e.zero
    SMulWithZero M₀ A := by
  letI := e.zero
  exact {
    e.smulZeroClass M₀ with
    zero_smul := by simp [smul_def, zero_def]
  }

中文:
缩写 smulWithZero
  签名: (e : A ≃ B) [Zero M₀] [Zero B] [SMulWithZero M₀ B]
  定义体: e.zero
    SMulWithZero M₀ A := by
  letI := e.zero
  exact {
    e.smulZeroClass M₀ with
    zero_smul := by simp [smul_def, zero_def]
  }
-/
protected abbrev smulWithZero (e : A ≃ B) [Zero M₀] [Zero B] [SMulWithZero M₀ B] :
    letI := e.zero
    SMulWithZero M₀ A := by
  letI := e.zero
  exact {
    e.smulZeroClass M₀ with
    zero_smul := by simp [smul_def, zero_def]
  }

variable (M₀) in
/--
Definition of `mulActionWithZero` / `mulActionWithZero` 的定义

English:
abbreviation mulActionWithZero
  signature: (e : A ≃ B) [MonoidWithZero M₀] [Zero B]
  body: e.zero
    MulActionWithZero M₀ A := by
  letI := e.zero
  exact { e.smulWithZero M₀, e.mulAction M₀ with }

中文:
缩写 mulActionWithZero
  签名: (e : A ≃ B) [MonoidWithZero M₀] [Zero B]
  定义体: e.zero
    MulActionWithZero M₀ A := by
  letI := e.zero
  exact { e.smulWithZero M₀, e.mulAction M₀ with }
-/
protected abbrev mulActionWithZero (e : A ≃ B) [MonoidWithZero M₀] [Zero B]
    [MulActionWithZero M₀ B] :
    letI := e.zero
    MulActionWithZero M₀ A := by
  letI := e.zero
  exact { e.smulWithZero M₀, e.mulAction M₀ with }

variable (M) in
/--
Definition of `distribSMul` / `distribSMul` 的定义

English:
abbreviation distribSMul
  signature: (e : A ≃ B) [AddZeroClass B] [DistribSMul M B]
  body: e.addZeroClass
    DistribSMul M A := by
  letI := e.addZeroClass
  exact {
    e.smulZeroClass M with
    smul_add := by simp [add_def, smul_def, smul_add]
  }

中文:
缩写 distribSMul
  签名: (e : A ≃ B) [AddZeroClass B] [DistribSMul M B]
  定义体: e.addZeroClass
    DistribSMul M A := by
  letI := e.addZeroClass
  exact {
    e.smulZeroClass M with
    smul_add := by simp [add_def, smul_def, smul_add]
  }
-/
protected abbrev distribSMul (e : A ≃ B) [AddZeroClass B] [DistribSMul M B] :
    letI := e.addZeroClass
    DistribSMul M A := by
  letI := e.addZeroClass
  exact {
    e.smulZeroClass M with
    smul_add := by simp [add_def, smul_def, smul_add]
  }

variable (M) in
/--
Definition of `distribMulAction` / `distribMulAction` 的定义

English:
abbreviation distribMulAction
  signature: (e : A ≃ B) [Monoid M] [AddMonoid B] [DistribMulAction M B]
  body: e.addMonoid
    DistribMulAction M A := by
  letI := e.addMonoid
  exact { e.distribSMul M, e.mulAction M with }

中文:
缩写 distribMulAction
  签名: (e : A ≃ B) [Monoid M] [AddMonoid B] [DistribMulAction M B]
  定义体: e.addMonoid
    DistribMulAction M A := by
  letI := e.addMonoid
  exact { e.distribSMul M, e.mulAction M with }
-/
protected abbrev distribMulAction (e : A ≃ B) [Monoid M] [AddMonoid B] [DistribMulAction M B] :
    letI := e.addMonoid
    DistribMulAction M A := by
  letI := e.addMonoid
  exact { e.distribSMul M, e.mulAction M with }

end Equiv
