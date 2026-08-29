/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.Module.Pi

/-!
# Product of torsion-free modules

This file shows that the product of torsion-free modules is torsion-free.
-/

public section

open Module

variable {ι R : Type*} {M : ι -> Type*}

namespace Pi

/--
Instance `instModuleIsTorsionFree` / 实例 `instModuleIsTorsionFree`

English:
instance instModuleIsTorsionFree
  signature: [Semiring R] [forall i, AddCommMonoid (M i)] [forall i, Module R (M i)]
  body: .piMap fun _i => hr.isSMulRegular

中文:
实例 instModuleIsTorsionFree
  签名: [Semiring R] [对任意 i, AddCommMonoid (M i)] [对任意 i, Module R (M i)]
  定义体: .piMap fun _i => hr.isSMulRegular

Depends on / 依赖: hr.isSMulRegular, isSMulRegular
-/
instance instModuleIsTorsionFree [Semiring R] [forall i, AddCommMonoid (M i)] [forall i, Module R (M i)]
    [forall i, IsTorsionFree R (M i)] : Module.IsTorsionFree R (forall i, M i) where
  isSMulRegular _r hr := .piMap fun _i => hr.isSMulRegular

end Pi
