/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Yaël Dillies
-/
module

public import Mathlib.Algebra.NoZeroSMulDivisors.Defs
public import Mathlib.Algebra.Group.Action.Pi

/-!
# Pi instances for NoZeroSMulDivisors

This file defines instances for NoZeroSMulDivisors on Pi types.
-/

public section


universe u v

variable {I : Type u}

-- The indexing type
variable {f : I -> Type v}

/--
Instance `Pi.noZeroSMulDivisors` / 实例 `Pi.noZeroSMulDivisors`

English:
instance Pi.noZeroSMulDivisors
  signature: (α) [Semiring α] [IsDomain α] [forall i, AddCommGroup <| f i]
  body: ⟨fun {_ _} h =>
    or_iff_not_imp_left.mpr fun hc =>
      funext fun i => (smul_eq_zero.mp (congr_fun h i)).resolve_left hc⟩

中文:
实例 Pi.noZeroSMulDivisors
  签名: (α) [Semiring α] [IsDomain α] [对任意 i, AddCommGroup <| f i]
  定义体: ⟨fun {_ _} h =>
    or_iff_not_imp_left.mpr fun hc =>
      funext fun i => (smul_eq_zero.mp (congr_fun h i)).resolve_left hc⟩

Depends on / 依赖: congr_fun, or_iff_not_imp_left, or_iff_not_imp_left.mpr, resolve_left, smul_eq_zero, smul_eq_zero.mp
-/
instance Pi.noZeroSMulDivisors (α) [Semiring α] [IsDomain α] [forall i, AddCommGroup <| f i]
    [forall i, Module α <| f i] [forall i, NoZeroSMulDivisors α <| f i] :
    NoZeroSMulDivisors α (forall i : I, f i) :=
  ⟨fun {_ _} h =>
    or_iff_not_imp_left.mpr fun hc =>
      funext fun i => (smul_eq_zero.mp (congr_fun h i)).resolve_left hc⟩

/--
Instance `_root_.Function.noZeroSMulDivisors` / 实例 `_root_.Function.noZeroSMulDivisors`

English:
instance _root_.Function.noZeroSMulDivisors
  signature: {ι α β : Type*} [Semiring α] [IsDomain α]
  body: Pi.noZeroSMulDivisors _

中文:
实例 _root_.Function.noZeroSMulDivisors
  签名: {ι α β : 类型} [Semiring α] [IsDomain α]
  定义体: Pi.noZeroSMulDivisors _

Depends on / 依赖: Pi.noZeroSMulDivisors, noZeroSMulDivisors
-/
instance _root_.Function.noZeroSMulDivisors {ι α β : Type*} [Semiring α] [IsDomain α]
    [AddCommGroup β] [Module α β] [NoZeroSMulDivisors α β] : NoZeroSMulDivisors α (ι -> β) :=
  Pi.noZeroSMulDivisors _
