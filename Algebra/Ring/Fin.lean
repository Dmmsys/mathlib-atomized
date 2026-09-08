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
/-
**RingEquiv.piFinTwo** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：RingEquiv.piFinTwo (R : Fin 2 -> Type*) [forall i, Semiring (R i)] : (fora
ll i : Fin 2, R i) ≃+* R 0 × R 1
参数：R : Fin 2 -> Type*；R i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product over `Fin 2` of some rings is just the Cartesian product of these ri
ngs.
-/
def RingEquiv.piFinTwo (R : Fin 2 → Type*) [∀ i, Semiring (R i)] :
    (∀ i : Fin 2, R i) ≃+* R 0 × R 1 :=
  { piFinTwoEquiv R with
    toFun := piFinTwoEquiv R
    map_add' := fun _ _ => rfl
    map_mul' := fun _ _ => rfl }
