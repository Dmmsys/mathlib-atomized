/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Module.Torsion.Free

/-!
# Product of torsion-free modules

This file shows that the product of two torsion-free modules is torsion-free.
-/

public section

open Module

variable {R M N : Type*}

namespace Prod

/--
Instance `moduleIsTorsionFree` / 实例 `moduleIsTorsionFree`

English:
instance moduleIsTorsionFree
  signature: [Semiring R] [AddCommMonoid M] [AddCommMonoid N]
  body: hr.isSMulRegular.prodMap hr.isSMulRegular

中文:
实例 moduleIsTorsionFree
  签名: [Semiring R] [AddCommMonoid M] [AddCommMonoid N]
  定义体: hr.isSMulRegular.prodMap hr.isSMulRegular

Depends on / 依赖: hr.isSMulRegular, hr.isSMulRegular.prodMap, isSMulRegular, prodMap
-/
instance moduleIsTorsionFree [Semiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] [IsTorsionFree R M] [IsTorsionFree R N] :
    IsTorsionFree R (M × N) where
  isSMulRegular _r hr := hr.isSMulRegular.prodMap hr.isSMulRegular

end Prod
