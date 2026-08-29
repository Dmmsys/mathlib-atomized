/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Divisibility

/-!
# Submonoid of primal elements
-/

@[expose] public section

assert_not_exists RelIso Ring

/--
Definition of `Submonoid.isPrimal` / `Submonoid.isPrimal` 的定义

English:
definition Submonoid.isPrimal
  signature: (M₀ : Type*) [CommMonoidWithZero M₀] [IsCancelMulZero M₀]
  body: {a | IsPrimal a}
  mul_mem' := .mul
  one_mem' := isUnit_one.isPrimal

中文:
定义 Submonoid.isPrimal
  签名: (M₀ : 类型) [CommMonoidWithZero M₀] [IsCancelMulZero M₀]
  定义体: {a | IsPrimal a}
  mul_mem' := .mul
  one_mem' := isUnit_one.isPrimal

Depends on / 依赖: IsPrimal
-/
def Submonoid.isPrimal (M₀ : Type*) [CommMonoidWithZero M₀] [IsCancelMulZero M₀] :
    Submonoid M₀ where
  carrier := {a | IsPrimal a}
  mul_mem' := .mul
  one_mem' := isUnit_one.isPrimal
