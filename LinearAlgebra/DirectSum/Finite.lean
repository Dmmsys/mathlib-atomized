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

variable {R ι : Type*} [Semiring R] [Finite ι] (M : ι -> Type*)
  [forall i : ι, AddCommMonoid (M i)] [forall i : ι, Module R (M i)] [forall (i : ι), Module.Finite R (M i)]

/--
Instance `Module.Finite.instDFinsupp` / 实例 `Module.Finite.instDFinsupp`

English:
instance Module.Finite.instDFinsupp
  signature: : Module.Finite R (Π₀ (i : ι), M i)
  body: letI : Fintype ι := Fintype.ofFinite _
  Module.Finite.equiv DFinsupp.linearEquivFunOnFintype.symm

中文:
实例 Module.Finite.instDFinsupp
  签名: : Module.Finite R (Π₀ (i : ι), M i)
  定义体: letI : Fintype ι := Fintype.ofFinite _
  Module.Finite.equiv DFinsupp.linearEquivFunOnFintype.symm

Depends on / 依赖: DFinsupp, DFinsupp.linearEquivFunOnFintype.symm, Finite, Fintype, Fintype.ofFinite, Module, Module.Finite.equiv, linearEquivFunOnFintype, ofFinite
-/
instance Module.Finite.instDFinsupp : Module.Finite R (Π₀ (i : ι), M i) :=
  letI : Fintype ι := Fintype.ofFinite _
  Module.Finite.equiv DFinsupp.linearEquivFunOnFintype.symm

/--
Instance `Module.Finite.instDirectSum` / 实例 `Module.Finite.instDirectSum`

English:
instance Module.Finite.instDirectSum
  signature: : Module.Finite R (⨁ i, M i)
  body: Module.Finite.instDFinsupp M

中文:
实例 Module.Finite.instDirectSum
  签名: : Module.Finite R (⨁ i, M i)
  定义体: Module.Finite.instDFinsupp M

Depends on / 依赖: Finite, Module, Module.Finite.instDFinsupp, instDFinsupp
-/
instance Module.Finite.instDirectSum : Module.Finite R (⨁ i, M i) :=
  Module.Finite.instDFinsupp M
