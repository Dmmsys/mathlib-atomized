/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Monoid.Defs

/-!
# Topological (sub)algebras over `Rat`

## Results

This is just a minimal stub for now!

-/

public section

section DivisionRing

/--
Instance `DivisionRing.continuousConstSMul_rat` / 实例 `DivisionRing.continuousConstSMul_rat`

English:
instance DivisionRing.continuousConstSMul_rat
  signature: {A} [DivisionRing A] [TopologicalSpace A]
  body: ⟨fun r => by simpa only [Algebra.smul_def] using! continuous_id.const_mul _⟩

中文:
实例 DivisionRing.continuousConstSMul_rat
  签名: {A} [DivisionRing A] [TopologicalSpace A]
  定义体: ⟨fun r => by simpa only [Algebra.smul_def] using! continuous_id.const_mul _⟩

Depends on / 依赖: Algebra, Algebra.smul_def, const_mul, continuous_id, continuous_id.const_mul, smul_def
-/
instance DivisionRing.continuousConstSMul_rat {A} [DivisionRing A] [TopologicalSpace A]
    [SeparatelyContinuousMul A] [CharZero A] : ContinuousConstSMul Rat A :=
  ⟨fun r => by simpa only [Algebra.smul_def] using! continuous_id.const_mul _⟩

end DivisionRing
