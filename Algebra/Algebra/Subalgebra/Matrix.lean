/-
Copyright (c) 2025 Bryan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Wang
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
# Matrix subalgebras

In this file we define the subalgebra of square matrices with entries in some subalgebra.

## Main definitions

* `Subalgebra.matrix`: the subalgebra of square matrices with entries in some subalgebra.
-/

@[expose] public section

open Matrix
open Algebra

namespace Subalgebra

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A version of `Set.matrix` for `Subalgebra`s.
Given a `Subalgebra` `S`, `S.matrix` is the `Subalgebra` of square matrices `m`
all of whose entries `m i j` belong to `S`. -/
@[simps!]
/-
**Subalgebra.matrix** 是 Mathlib 中的一个定义，位于命名空间 `Subalgebra`。
形式化陈述：matrix (S : Subalgebra R A) : Subalgebra R (Matrix n n A) where __
参数：S : Subalgebra R A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `Set.matrix` for `Subalgebra`s.
Given a `Subalgebra` `S`, `S.matrix` is the `Subalgebra` of square matrices `m`
all of whose entries `m i j` belong to `S`.
-/
def matrix (S : Subalgebra R A) : Subalgebra R (Matrix n n A) where
  __ := S.toSubsemiring.matrix
  algebraMap_mem' _ :=
    (diagonal_mem_matrix_iff (Subalgebra.zero_mem _)).mpr (fun _ => Subalgebra.algebraMap_mem _ _)

end Subalgebra

