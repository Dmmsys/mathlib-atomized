/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.UniqueProds.Basic
public import Mathlib.GroupTheory.Finiteness

import Mathlib.Algebra.AffineMonoid.Embedding
import Mathlib.Algebra.FreeAbelianGroup.UniqueSums

/-!
# Affine monoids have unique sums

In this file we show that finitely generated cancellative torsion-free commutative monoids have
unique sums. This is a direct corollary of them embedding into `ℤⁿ` for some `n`.
-/

public section

variable {M : Type*}

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) AffineAddMonoid.to_twoUniqueSums [AddCancelCommMonoid M] [AddMonoid.FG M]
    [IsAddTorsionFree M] : TwoUniqueSums M :=
  .of_injective_addHom (embedding M).toAddHom embedding_injective inferInstance

@[to_additive existing AffineAddMonoid.to_twoUniqueSums]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) AffineMonoid.to_twoUniqueProds [CancelCommMonoid M] [Monoid.FG M]
    [IsMulTorsionFree M] : TwoUniqueProds M :=
  Multiplicative.instTwoUniqueProdsOfTwoUniqueSums (M := Additive M)
