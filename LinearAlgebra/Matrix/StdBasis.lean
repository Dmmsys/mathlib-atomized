/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
module

public import Mathlib.Data.Matrix.Basis
public import Mathlib.LinearAlgebra.StdBasis

/-!
# Standard basis on matrices

## Main results

* `Basis.matrix`: extend a basis on `M` to the standard basis on `Matrix n m M`
-/

@[expose] public section

open Module

namespace Module.Basis
variable {ι R M : Type*} (m n : Type*)
variable [Fintype m] [Fintype n] [Semiring R] [AddCommMonoid M] [Module R M]

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def matrix (b : Basis ι R M)
  body: Basis.reindex (Pi.basis fun _ : m => Pi.basis fun _ : n => b)
    ((Equiv.sigmaEquivProd _ _).trans <| .prodCongr (.refl _) (Equiv.sigmaEquivProd _ _))
.map (Matrix.ofLinearEquiv R)

中文:
定义 noncomputable
  签名: def matrix (b : 基 ι R M)
  定义体: Basis.reindex (Pi.basis fun _ : m => Pi.basis fun _ : n => b)
    ((Equiv.sigmaEquivProd _ _).trans <| .prodCongr (.refl _) (Equiv.sigmaEquivProd _ _))
.map (Matrix.ofLinearEquiv R)
-/
protected noncomputable def matrix (b : Basis ι R M) :
    Basis (m × n × ι) R (Matrix m n M) :=
  Basis.reindex (Pi.basis fun _ : m => Pi.basis fun _ : n => b)
    ((Equiv.sigmaEquivProd _ _).trans <| .prodCongr (.refl _) (Equiv.sigmaEquivProd _ _))
.map (Matrix.ofLinearEquiv R)

variable {n m}

@[simp]
/--
theorem `matrix_apply` / 定理 `matrix_apply`

English:
theorem matrix_apply
  given: (b : Basis ι R M) (i : m) (j : n) (k : ι) [DecidableEq m] [DecidableEq n]
  proof: by
  simp [Basis.matrix, Matrix.single_eq_of_single_single]

中文:
定理 matrix_apply
  条件: (b : 基 ι R M) (i : m) (j : n) (k : ι) [DecidableEq m] [DecidableEq n]
  证明: by
  simp [Basis.matrix, Matrix.single_eq_of_single_single]

Depends on / 依赖: Basis.matrix, Matrix, Matrix.single_eq_of_single_single, matrix, single_eq_of_single_single
-/
theorem matrix_apply (b : Basis ι R M) (i : m) (j : n) (k : ι) [DecidableEq m] [DecidableEq n] :
    b.matrix m n (i, j, k) = Matrix.single i j (b k) := by
  simp [Basis.matrix, Matrix.single_eq_of_single_single]

end Module.Basis

namespace Matrix

variable (R : Type*) (m n : Type*) [Fintype m] [Finite n] [Semiring R]

/--
Definition of `stdBasis` / `stdBasis` 的定义

English:
definition stdBasis
  signature: : Basis (m × n) R (Matrix m n R)
  body: Basis.reindex (Pi.basis fun _ : m => Pi.basisFun R n) (Equiv.sigmaEquivProd _ _)
.map (ofLinearEquiv R)

中文:
定义 stdBasis
  签名: : 基 (m × n) R (矩阵 m n R)
  定义体: Basis.reindex (Pi.basis fun _ : m => Pi.basisFun R n) (Equiv.sigmaEquivProd _ _)
.map (ofLinearEquiv R)

Depends on / 依赖: Basis.reindex, Equiv.sigmaEquivProd, Pi.basis, Pi.basisFun, basisFun, ofLinearEquiv, reindex, sigmaEquivProd
-/
noncomputable def stdBasis : Basis (m × n) R (Matrix m n R) :=
  Basis.reindex (Pi.basis fun _ : m => Pi.basisFun R n) (Equiv.sigmaEquivProd _ _)
.map (ofLinearEquiv R)

variable {n m}

/--
theorem `stdBasis_eq_single` / 定理 `stdBasis_eq_single`

English:
theorem stdBasis_eq_single
  given: (i : m) (j : n) [DecidableEq m] [DecidableEq n]
  proof: by
  simp [stdBasis, single_eq_of_single_single]

中文:
定理 stdBasis_eq_single
  条件: (i : m) (j : n) [DecidableEq m] [DecidableEq n]
  证明: by
  simp [stdBasis, single_eq_of_single_single]

Depends on / 依赖: single_eq_of_single_single, stdBasis
-/
theorem stdBasis_eq_single (i : m) (j : n) [DecidableEq m] [DecidableEq n] :
    stdBasis R m n (i, j) = single i j (1 : R) := by
  simp [stdBasis, single_eq_of_single_single]

end Matrix

namespace Module.Free

variable (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M] [Module.Free R M]

/--
Instance `matrix` / 实例 `matrix`

English:
instance matrix
  signature: {m n : Type*} [Finite m] [Finite n]
  body: Module.Free.pi R _

中文:
实例 matrix
  签名: {m n : 类型} [有限 m] [有限 n]
  定义体: Module.Free.pi R _

Depends on / 依赖: Module, Module.Free.pi
-/
instance matrix {m n : Type*} [Finite m] [Finite n] : Module.Free R (Matrix m n M) :=
  Module.Free.pi R _

end Module.Free
