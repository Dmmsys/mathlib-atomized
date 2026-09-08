/-
Copyright (c) 2025 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# A finite direct sum of finite modules is finite

This file defines a `Module.Finite` instance for a finite direct sum of finite modules.

-/

public section

open DirectSum

variable {R ι : Type*} [Semiring R] [Finite ι] (M : ι → Type*)
  [∀ i : ι, AddCommMonoid (M i)] [∀ i : ι, Module R (M i)] [∀ (i : ι), Module.Finite R (M i)]

/-
**Module.Finite.instDFinsupp** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Module.Finite.instDFinsupp : Module.Finite R (Π₀ (i : ι), M i)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.equiv`：equiv [Module.Finite R M] (e : M ≃ₗ[R] N) : Module.
Finite R N
-/
instance Module.Finite.instDFinsupp : Module.Finite R (Π₀ (i : ι), M i) :=
  letI : Fintype ι := Fintype.ofFinite _
  Module.Finite.equiv DFinsupp.linearEquivFunOnFintype.symm
/-
**Module.Finite.instDirectSum** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Module.Finite.instDirectSum : Module.Finite R (⨁ i, M i)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Module.Finite.instDirectSum : Module.Finite R (⨁ i, M i) :=
  Module.Finite.instDFinsupp M
