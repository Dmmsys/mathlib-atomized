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
/--
Definition of `matrix` / `matrix` 的定义

English:
definition matrix
  signature: (S : Subalgebra R A)
  body: S.toSubsemiring.matrix
  algebraMap_mem' _ :=
    (diagonal_mem_matrix_iff (Subalgebra.zero_mem _)).mpr (fun _ => Subalgebra.algebraMap_mem _ _)

中文:
定义 matrix
  签名: (S : 子代数 R A)
  定义体: S.toSubsemiring.matrix
  algebraMap_mem' _ :=
    (diagonal_mem_matrix_iff (Subalgebra.zero_mem _)).mpr (fun _ => Subalgebra.algebraMap_mem _ _)

Depends on / 依赖: S.toSubsemiring.matrix, matrix, toSubsemiring
-/
def matrix (S : Subalgebra R A) : Subalgebra R (Matrix n n A) where
  __ := S.toSubsemiring.matrix
  algebraMap_mem' _ :=
    (diagonal_mem_matrix_iff (Subalgebra.zero_mem _)).mpr (fun _ => Subalgebra.algebraMap_mem _ _)

end Subalgebra
