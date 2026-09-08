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

variable (R : Type*) [Semiring R] {ι : Type*} (M : ι → Type*) [∀ i : ι, AddCommMonoid (M i)]
variable [∀ i : ι, Module R (M i)]

/-
**Module.Free.directSum** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Module.Free.directSum [forall i : ι, Module.Free R (M i)] : Module.Free R 
(⨁ i, M i)
参数：M i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Free.dfinsupp`：∀ {ι : Type u_1} (R : Type u_2) (M : ι → Type u_3)
 [inst : Semiring R] [inst_1 : (i : ι) → AddCommMonoid (M i)]   [inst_2 : (i : ι
) → _root_…
-/
instance Module.Free.directSum [∀ i : ι, Module.Free R (M i)] : Module.Free R (⨁ i, M i) :=
  Module.Free.dfinsupp R M

end Semiring

