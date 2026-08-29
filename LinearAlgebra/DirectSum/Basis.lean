/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-!
# Bases for direct sum of modules

This file defines a `Module.Free` instance for the direct sum of modules.

## Implementation notes

Currently, to get a basis on `⨁ i, M i` from a basis on each `M i`, use `DFinsupp.basis`
(using that the types are defeq).
-/

public section

open DirectSum

section Semiring

variable (R : Type*) [Semiring R] {ι : Type*} (M : ι -> Type*) [forall i : ι, AddCommMonoid (M i)]
variable [forall i : ι, Module R (M i)]

/--
Instance `Module.Free.directSum` / 实例 `Module.Free.directSum`

English:
instance Module.Free.directSum
  signature: [forall i : ι, Module.Free R (M i)]
  body: Module.Free.dfinsupp R M

中文:
实例 模.自由.directSum
  签名: [对任意 i : ι, 模.自由 R (M i)]
  定义体: Module.Free.dfinsupp R M

Depends on / 依赖: Module, Module.Free.dfinsupp, dfinsupp
-/
instance Module.Free.directSum [forall i : ι, Module.Free R (M i)] : Module.Free R (⨁ i, M i) :=
  Module.Free.dfinsupp R M

end Semiring
