/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.UniqueFactorizationDomain.Ideal
/-!
# Noetherian domains have unique factorization

## Main results

- IsNoetherianRing.wfDvdMonoid
-/

public section

variable {R : Type*} [CommSemiring R] [IsDomain R]

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) IsNoetherianRing.wfDvdMonoid [h : IsNoetherianRing R] :
    WfDvdMonoid R :=
  WfDvdMonoid.of_setOfPred_isPrincipal_wellFoundedOn_gt h.wf.wellFoundedOn
