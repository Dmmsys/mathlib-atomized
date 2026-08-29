/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Rings and `Fin`

This file collects some basic results involving rings and the `Fin` type

## Main results

* `RingEquiv.piFinTwo`: The product over `Fin 2` of some rings is the Cartesian product

-/

@[expose] public section


/-- The product over `Fin 2` of some rings is just the Cartesian product of these rings. -/
@[simps]
/--
Definition of `RingEquiv.piFinTwo` / `RingEquiv.piFinTwo` 的定义

English:
definition RingEquiv.piFinTwo
  signature: (R : Fin 2 -> Type*) [forall i, Semiring (R i)]
  body: { piFinTwoEquiv R with
    toFun := piFinTwoEquiv R
    map_add' := fun _ _ => rfl
    map_mul' := fun _ _ => rfl }

中文:
定义 环等价.piFinTwo
  签名: (R : 有限集 2 -> 类型) [对任意 i, 半环 (R i)]
  定义体: { piFinTwoEquiv R with
    toFun := piFinTwoEquiv R
    map_add' := fun _ _ => rfl
    map_mul' := fun _ _ => rfl }

Depends on / 依赖: map_add, map_mul, piFinTwoEquiv
-/
def RingEquiv.piFinTwo (R : Fin 2 -> Type*) [forall i, Semiring (R i)] :
    (forall i : Fin 2, R i) ≃+* R 0 × R 1 :=
  { piFinTwoEquiv R with
    toFun := piFinTwoEquiv R
    map_add' := fun _ _ => rfl
    map_mul' := fun _ _ => rfl }
