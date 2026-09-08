/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.Algebra.SeparationQuotient.Basic
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Separation quotient is a finite module

In this file we show that the separation quotient of a finite module is a finite module.
-/

public section

/-- The separation quotient of a finite module is a finite module. -/
/-
**SeparationQuotient.instModuleFinite** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：SeparationQuotient.instModuleFinite {R M : Type*} [Semiring R] [AddCommMon
oid M] [Module R M] [Module.Finite R M] [TopologicalSpace M] [ContinuousAdd M] [
ContinuousConstSMul R M] : Module.Finite R (SeparationQuotient M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.of_surjective`：of_surjective [hM : Module.Finite R M] (f :
 M ->ₛₗ[σ] P) (hf : Surjective f) : Module.Finite S P
· 使用定理 `Quotient.mk_surjective`：Quotient.mk_surjective {s : Setoid α} : Function
.Surjective (Quotient.mk s)

--- 原说明 ---
The separation quotient of a finite module is a finite module.
-/
instance SeparationQuotient.instModuleFinite
    {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [Module.Finite R M]
    [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul R M] :
    Module.Finite R (SeparationQuotient M) :=
  Module.Finite.of_surjective (mkCLM R M).toLinearMap Quotient.mk_surjective
