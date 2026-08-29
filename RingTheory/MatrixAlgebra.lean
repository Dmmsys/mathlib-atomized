/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Eric Wieser
-/
module

public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Matrix.Composition
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Algebra isomorphisms between tensor products and matrices

## Main definitions

* `matrixEquivTensor : Matrix n n A ≃ₐ[R] (A ⊗[R] Matrix n n R)`.
* `Matrix.kroneckerTMulAlgEquiv :
    Matrix m m A ⊗[R] Matrix n n B ≃ₐ[S] Matrix (m × n) (m × n) (A ⊗[R] B)`,
  where the forward map is the (tensor-ified) Kronecker product.
-/

@[expose] public section

open TensorProduct Algebra.TensorProduct Matrix

variable {l m n p : Type*} {R S A B M N : Type*}
section Module

variable [CommSemiring R] [Semiring S] [Semiring A] [Semiring B] [AddCommMonoid M] [AddCommMonoid N]
variable [Algebra R S] [Algebra R A] [Algebra R B] [Module R M] [Module S M] [Module R N]
variable [IsScalarTower R S M]
variable [Fintype l] [Fintype m] [Fintype n] [Fintype p]
variable [DecidableEq l] [DecidableEq m] [DecidableEq n] [DecidableEq p]

open Kronecker

variable (l m n p R S A M N)

attribute [local ext] ext_linearMap

/--
Definition of `kroneckerTMulLinearEquiv` / `kroneckerTMulLinearEquiv` 的定义

English:
definition kroneckerTMulLinearEquiv
  signature: :
  body: .ofLinearMap
    (AlgebraTensorModule.lift <| kroneckerTMulBilinear R S)
    (Matrix.liftLinear R fun ii jj =>
      AlgebraTensorModule.map (singleLinearMap S ii.1 jj.1) (singleLinearMap R ii.2 jj.2))
    (by
      ext : 4
      simp [single_kroneckerTMul_single])
    (by
      ext : 5
      simp [single_kroneckerTMul_single])

@[simp]

中文:
定义 kroneckerTMulLinearEquiv
  签名: :
  定义体: .ofLinearMap
    (AlgebraTensorModule.lift <| kroneckerTMulBilinear R S)
    (Matrix.liftLinear R fun ii jj =>
      AlgebraTensorModule.map (singleLinearMap S ii.1 jj.1) (singleLinearMap R ii.2 jj.2))
    (by
      ext : 4
      simp [single_kroneckerTMul_single])
    (by
      ext : 5
      simp [single_kroneckerTMul_single])

@[simp]

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.lift, AlgebraTensorModule.map, Matrix, Matrix.liftLinear, kroneckerTMulBilinear, liftLinear, ofLinearMap, singleLinearMap, single_kroneckerTMul_single
-/
def kroneckerTMulLinearEquiv :
    Matrix l m M otimes[R] Matrix n p N ≃ₗ[S] Matrix (l × n) (m × p) (M otimes[R] N) :=
  .ofLinearMap
    (AlgebraTensorModule.lift <| kroneckerTMulBilinear R S)
    (Matrix.liftLinear R fun ii jj =>
      AlgebraTensorModule.map (singleLinearMap S ii.1 jj.1) (singleLinearMap R ii.2 jj.2))
    (by
      ext : 4
      simp [single_kroneckerTMul_single])
    (by
      ext : 5
      simp [single_kroneckerTMul_single])

@[simp]
/--
theorem `kroneckerTMulLinearEquiv_tmul` / 定理 `kroneckerTMulLinearEquiv_tmul`

English:
theorem kroneckerTMulLinearEquiv_tmul
  given: (a : Matrix l m M) (b : Matrix n p N)
  proof: rfl

@[simp]

中文:
定理 kroneckerTMulLinearEquiv_tmul
  条件: (a : 矩阵 l m M) (b : 矩阵 n p N)
  证明: rfl

@[simp]
-/
theorem kroneckerTMulLinearEquiv_tmul (a : Matrix l m M) (b : Matrix n p N) :
    kroneckerTMulLinearEquiv l m n p R S M N (a otimesₜ b) = a otimesₖₜ b := rfl

@[simp]
/--
theorem `kroneckerTMulLinearEquiv_symm_kroneckerTMul` / 定理 `kroneckerTMulLinearEquiv_symm_kroneckerTMul`

English:
theorem kroneckerTMulLinearEquiv_symm_kroneckerTMul
  given: (a : Matrix l m M) (b : Matrix n p N)
  proof: by
  simp [LinearEquiv.symm_apply_eq]

@[simp]

中文:
定理 kroneckerTMulLinearEquiv_symm_kroneckerTMul
  条件: (a : 矩阵 l m M) (b : 矩阵 n p N)
  证明: by
  simp [LinearEquiv.symm_apply_eq]

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.symm_apply_eq, symm_apply_eq
-/
theorem kroneckerTMulLinearEquiv_symm_kroneckerTMul (a : Matrix l m M) (b : Matrix n p N) :
    (kroneckerTMulLinearEquiv l m n p R S M N).symm (a otimesₖₜ b) = a otimesₜ b := by
  simp [LinearEquiv.symm_apply_eq]

@[simp]
/--
theorem `kroneckerTMulAlgEquiv_symm_single_tmul` / 定理 `kroneckerTMulAlgEquiv_symm_single_tmul`

English:
theorem kroneckerTMulAlgEquiv_symm_single_tmul
  proof: by
  rw [LinearEquiv.symm_apply_eq]; rw [kroneckerTMulLinearEquiv_tmul]; rw [single_kroneckerTMul_single]

@[simp]

中文:
定理 kroneckerTMulAlgEquiv_symm_single_tmul
  证明: by
  rw [LinearEquiv.symm_apply_eq]; rw [kroneckerTMulLinearEquiv_tmul]; rw [single_kroneckerTMul_single]

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.symm_apply_eq, kroneckerTMulLinearEquiv_tmul, single_kroneckerTMul_single, symm_apply_eq
-/
theorem kroneckerTMulAlgEquiv_symm_single_tmul
    (ia : l) (ja : m) (ib : n) (jb : p) (a : M) (b : N) :
    (kroneckerTMulLinearEquiv l m n p R S M N).symm (single (ia, ib) (ja, jb) (a otimesₜ b)) =
      single ia ja a otimesₜ single ib jb b := by
  rw [LinearEquiv.symm_apply_eq]; rw [kroneckerTMulLinearEquiv_tmul]; rw [single_kroneckerTMul_single]

@[simp]
/--
theorem `kroneckerTMulLinearEquiv_one` / 定理 `kroneckerTMulLinearEquiv_one`

English:
theorem kroneckerTMulLinearEquiv_one
  given: [Module S A] [IsScalarTower R S A]
  proof: by simp [Algebra.TensorProduct.one_def]

中文:
定理 kroneckerTMulLinearEquiv_one
  条件: [模 S A] [标量塔 R S A]
  证明: by simp [Algebra.TensorProduct.one_def]

Depends on / 依赖: Algebra, Algebra.TensorProduct.one_def, TensorProduct, one_def
-/
theorem kroneckerTMulLinearEquiv_one [Module S A] [IsScalarTower R S A] :
    kroneckerTMulLinearEquiv m m n n R S A B 1 = 1 := by simp [Algebra.TensorProduct.one_def]

/-- Note this can't be stated for rectangular matrices because there is no
`HMul (TensorProduct R _ _) (TensorProduct R _ _) (TensorProduct R _ _)` instance. -/
@[simp]
/--
theorem `kroneckerTMulLinearEquiv_mul` / 定理 `kroneckerTMulLinearEquiv_mul`

English:
theorem kroneckerTMulLinearEquiv_mul
  given: [Module S A] [IsScalarTower R S A]
  proof: .map_mul_iff.2 by (kroneckerTMulLinearEquiv m m n n R S A B).toLinearMap.restrictScalars R
    ext : 10
    simp [single_kroneckerTMul_single, mul_kroneckerTMul_mul]

中文:
定理 kroneckerTMulLinearEquiv_mul
  条件: [模 S A] [标量塔 R S A]
  证明: .map_mul_iff.2 by (kroneckerTMulLinearEquiv m m n n R S A B).toLinearMap.restrictScalars R
    ext : 10
    simp [single_kroneckerTMul_single, mul_kroneckerTMul_mul]

Depends on / 依赖: kroneckerTMulLinearEquiv, map_mul_iff, mul_kroneckerTMul_mul, restrictScalars, single_kroneckerTMul_single, toLinearMap, toLinearMap.restrictScalars
-/
theorem kroneckerTMulLinearEquiv_mul [Module S A] [IsScalarTower R S A] :
    forall x y : Matrix m m A otimes[R] Matrix n n B,
      kroneckerTMulLinearEquiv m m n n R S A B (x * y) =
        kroneckerTMulLinearEquiv m m n n R S A B x * kroneckerTMulLinearEquiv m m n n R S A B y :=
.map_mul_iff.2 by (kroneckerTMulLinearEquiv m m n n R S A B).toLinearMap.restrictScalars R
    ext : 10
    simp [single_kroneckerTMul_single, mul_kroneckerTMul_mul]

/--
Definition of `kroneckerLinearEquiv` / `kroneckerLinearEquiv` 的定义

English:
definition kroneckerLinearEquiv
  signature: : Matrix l m R otimes[R] Matrix n p R ≃ₗ[R] Matrix (l × n) (m × p) R
  body: (kroneckerTMulLinearEquiv l m n p R R R R).trans (TensorProduct.lid R R).mapMatrix

中文:
定义 kroneckerLinearEquiv
  签名: : 矩阵 l m R otimes[R] 矩阵 n p R ≃ₗ[R] 矩阵 (l × n) (m × p) R
  定义体: (kroneckerTMulLinearEquiv l m n p R R R R).trans (TensorProduct.lid R R).mapMatrix

Depends on / 依赖: TensorProduct, TensorProduct.lid, kroneckerTMulLinearEquiv, mapMatrix
-/
def kroneckerLinearEquiv : Matrix l m R otimes[R] Matrix n p R ≃ₗ[R] Matrix (l × n) (m × p) R :=
  (kroneckerTMulLinearEquiv l m n p R R R R).trans (TensorProduct.lid R R).mapMatrix

variable {l m n p R}

/--
theorem `kroneckerLinearEquiv_tmul` / 定理 `kroneckerLinearEquiv_tmul`

English:
theorem kroneckerLinearEquiv_tmul
  given: (x : Matrix l m R) (y : Matrix n p R)
  proof: rfl

中文:
定理 kroneckerLinearEquiv_tmul
  条件: (x : 矩阵 l m R) (y : 矩阵 n p R)
  证明: rfl
-/
@[simp] theorem kroneckerLinearEquiv_tmul (x : Matrix l m R) (y : Matrix n p R) :
    kroneckerLinearEquiv l m n p R (x otimesₜ y) = x otimesₖ y := rfl

/--
theorem `kroneckerLinearEquiv_symm_kronecker` / 定理 `kroneckerLinearEquiv_symm_kronecker`

English:
theorem kroneckerLinearEquiv_symm_kronecker
  given: (x : Matrix l m R) (y : Matrix n p R)
  proof: by simp [LinearEquiv.symm_apply_eq]

中文:
定理 kroneckerLinearEquiv_symm_kronecker
  条件: (x : 矩阵 l m R) (y : 矩阵 n p R)
  证明: by simp [LinearEquiv.symm_apply_eq]
-/
@[simp] theorem kroneckerLinearEquiv_symm_kronecker (x : Matrix l m R) (y : Matrix n p R) :
    (kroneckerLinearEquiv l m n p R).symm (x otimesₖ y) = x otimesₜ y := by simp [LinearEquiv.symm_apply_eq]

end Module


variable [CommSemiring R]
variable [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
variable (n R A)

namespace MatrixEquivTensor

/--
Definition of `toFunBilinear` / `toFunBilinear` 的定义

English:
definition toFunBilinear
  signature: : A ->ₗ[R] Matrix n n R ->ₗ[R] Matrix n n A
  body: (Algebra.lsmul R R (Matrix n n A)).toLinearMap.compl₂ (Algebra.linearMap R A).mapMatrix

@[simp]

中文:
定义 toFunBilinear
  签名: : A ->ₗ[R] 矩阵 n n R ->ₗ[R] 矩阵 n n A
  定义体: (Algebra.lsmul R R (Matrix n n A)).toLinearMap.compl₂ (Algebra.linearMap R A).mapMatrix

@[simp]

Depends on / 依赖: Algebra, Algebra.linearMap, Algebra.lsmul, Matrix, linearMap, mapMatrix, toLinearMap, toLinearMap.compl
-/
def toFunBilinear : A ->ₗ[R] Matrix n n R ->ₗ[R] Matrix n n A :=
  (Algebra.lsmul R R (Matrix n n A)).toLinearMap.compl₂ (Algebra.linearMap R A).mapMatrix

@[simp]
/--
theorem `toFunBilinear_apply` / 定理 `toFunBilinear_apply`

English:
theorem toFunBilinear_apply
  given: (a : A) (m : Matrix n n R)
  proof: rfl

中文:
定理 toFunBilinear_apply
  条件: (a : A) (m : 矩阵 n n R)
  证明: rfl
-/
theorem toFunBilinear_apply (a : A) (m : Matrix n n R) :
    toFunBilinear n R A a m = a • m.map (algebraMap R A) :=
  rfl

/--
Definition of `toFunLinear` / `toFunLinear` 的定义

English:
definition toFunLinear
  signature: : A otimes[R] Matrix n n R ->ₗ[R] Matrix n n A
  body: TensorProduct.lift (toFunBilinear n R A)

中文:
定义 toFunLinear
  签名: : A otimes[R] 矩阵 n n R ->ₗ[R] 矩阵 n n A
  定义体: TensorProduct.lift (toFunBilinear n R A)

Depends on / 依赖: TensorProduct, TensorProduct.lift, toFunBilinear
-/
def toFunLinear : A otimes[R] Matrix n n R ->ₗ[R] Matrix n n A :=
  TensorProduct.lift (toFunBilinear n R A)

variable [DecidableEq n] [Fintype n]

/--
Definition of `toFunAlgHom` / `toFunAlgHom` 的定义

English:
definition toFunAlgHom
  signature: : A otimes[R] Matrix n n R ->ₐ[R] Matrix n n A
  body: algHomOfLinearMapTensorProduct (toFunLinear n R A)
    (by
      intros
      simp_rw [toFunLinear, lift.tmul, toFunBilinear_apply, Matrix.map_mul]
      ext
      dsimp
      simp_rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Finset.mul_sum,
        _root_.mul_assoc, Algebra.left_comm])
    (by
      simp_rw [toFunLinear, lift.tmul, toFunBilinear_apply,
        Matrix.map_one (algebraMap R A) (map_zero _) (map_one _), one_smul])

@[simp]

中文:
定义 toFunAlgHom
  签名: : A otimes[R] 矩阵 n n R ->ₐ[R] 矩阵 n n A
  定义体: algHomOfLinearMapTensorProduct (toFunLinear n R A)
    (by
      intros
      simp_rw [toFunLinear, lift.tmul, toFunBilinear_apply, Matrix.map_mul]
      ext
      dsimp
      simp_rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Finset.mul_sum,
        _root_.mul_assoc, Algebra.left_comm])
    (by
      simp_rw [toFunLinear, lift.tmul, toFunBilinear_apply,
        Matrix.map_one (algebraMap R A) (map_zero _) (map_one _), one_smul])

@[simp]

Depends on / 依赖: Algebra, Algebra.left_comm, Finset, Finset.mul_sum, Matrix, Matrix.map_apply, Matrix.map_mul, Matrix.map_one, Matrix.mul_apply, Matrix.smul_apply, _root_, _root_.mul_assoc, algHomOfLinearMapTensorProduct, algebraMap, intros, left_comm, lift.tmul, map_apply, map_mul, map_one
-/
def toFunAlgHom : A otimes[R] Matrix n n R ->ₐ[R] Matrix n n A :=
  algHomOfLinearMapTensorProduct (toFunLinear n R A)
    (by
      intros
      simp_rw [toFunLinear, lift.tmul, toFunBilinear_apply, Matrix.map_mul]
      ext
      dsimp
      simp_rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Finset.mul_sum,
        _root_.mul_assoc, Algebra.left_comm])
    (by
      simp_rw [toFunLinear, lift.tmul, toFunBilinear_apply,
        Matrix.map_one (algebraMap R A) (map_zero _) (map_one _), one_smul])

@[simp]
/--
theorem `toFunAlgHom_apply` / 定理 `toFunAlgHom_apply`

English:
theorem toFunAlgHom_apply
  given: (a : A) (m : Matrix n n R)
  proof: rfl

中文:
定理 toFunAlgHom_apply
  条件: (a : A) (m : 矩阵 n n R)
  证明: rfl
-/
theorem toFunAlgHom_apply (a : A) (m : Matrix n n R) :
    toFunAlgHom n R A (a otimesₜ m) = a • m.map (algebraMap R A) := rfl

/--
Definition of `invFun` / `invFun` 的定义

English:
definition invFun
  signature: (M : Matrix n n A)
  body: ∑ p : n × n, M p.1 p.2 otimesₜ single p.1 p.2 1

@[simp]

中文:
定义 invFun
  签名: (M : 矩阵 n n A)
  定义体: ∑ p : n × n, M p.1 p.2 otimesₜ single p.1 p.2 1

@[simp]

Depends on / 依赖: single
-/
def invFun (M : Matrix n n A) : A otimes[R] Matrix n n R :=
  ∑ p : n × n, M p.1 p.2 otimesₜ single p.1 p.2 1

@[simp]
/--
theorem `invFun_zero` / 定理 `invFun_zero`

English:
theorem invFun_zero
  statement: invFun n R A 0 = 0
  proof: by simp [invFun]

@[simp]

中文:
定理 invFun_zero
  结论: invFun n R A 0 = 0
  证明: by simp [invFun]

@[simp]

Depends on / 依赖: invFun
-/
theorem invFun_zero : invFun n R A 0 = 0 := by simp [invFun]

@[simp]
/--
theorem `invFun_add` / 定理 `invFun_add`

English:
theorem invFun_add
  given: (M N : Matrix n n A)
  proof: by
  simp [invFun, add_tmul, Finset.sum_add_distrib]

@[simp]

中文:
定理 invFun_add
  条件: (M N : 矩阵 n n A)
  证明: by
  simp [invFun, add_tmul, Finset.sum_add_distrib]

@[simp]

Depends on / 依赖: Finset, Finset.sum_add_distrib, add_tmul, invFun, sum_add_distrib
-/
theorem invFun_add (M N : Matrix n n A) :
    invFun n R A (M + N) = invFun n R A M + invFun n R A N := by
  simp [invFun, add_tmul, Finset.sum_add_distrib]

@[simp]
/--
theorem `invFun_smul` / 定理 `invFun_smul`

English:
theorem invFun_smul
  given: (a : A) (M : Matrix n n A)
  proof: by
  simp [invFun, Finset.mul_sum]

@[simp]

中文:
定理 invFun_smul
  条件: (a : A) (M : 矩阵 n n A)
  证明: by
  simp [invFun, Finset.mul_sum]

@[simp]

Depends on / 依赖: Finset, Finset.mul_sum, invFun, mul_sum
-/
theorem invFun_smul (a : A) (M : Matrix n n A) :
    invFun n R A (a • M) = a otimesₜ 1 * invFun n R A M := by
  simp [invFun, Finset.mul_sum]

@[simp]
/--
theorem `invFun_algebraMap` / 定理 `invFun_algebraMap`

English:
theorem invFun_algebraMap
  given: (M : Matrix n n R)
  statement: invFun n R A (M.map (algebraMap R A)) = 1 otimesₜ M
  proof: by
  dsimp [invFun]
  simp only [Algebra.algebraMap_eq_smul_one, smul_tmul, ← tmul_sum]
  congr
  conv_rhs => rw [matrix_eq_sum_single M]
  convert! Finset.sum_product (β := Matrix n n R) ..; simp

中文:
定理 invFun_algebraMap
  条件: (M : 矩阵 n n R)
  结论: invFun n R A (M.map (algebraMap R A)) = 1 otimesₜ M
  证明: by
  dsimp [invFun]
  simp only [Algebra.algebraMap_eq_smul_one, smul_tmul, ← tmul_sum]
  congr
  conv_rhs => rw [matrix_eq_sum_single M]
  convert! Finset.sum_product (β := Matrix n n R) ..; simp

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, Finset, Finset.sum_product, Matrix, algebraMap_eq_smul_one, conv_rhs, convert, invFun, matrix_eq_sum_single, smul_tmul, sum_product, tmul_sum
-/
theorem invFun_algebraMap (M : Matrix n n R) : invFun n R A (M.map (algebraMap R A)) = 1 otimesₜ M := by
  dsimp [invFun]
  simp only [Algebra.algebraMap_eq_smul_one, smul_tmul, ← tmul_sum]
  congr
  conv_rhs => rw [matrix_eq_sum_single M]
  convert! Finset.sum_product (β := Matrix n n R) ..; simp

/--
theorem `right_inv` / 定理 `right_inv`

English:
theorem right_inv
  given: (M : Matrix n n A)
  statement: (toFunAlgHom n R A) (invFun n R A M) = M
  proof: by
  simp only [invFun, map_sum, toFunAlgHom_apply]
  convert! Finset.sum_product (β := Matrix n n A) ..
  conv_lhs => rw [matrix_eq_sum_single M]
  simp

中文:
定理 right_inv
  条件: (M : 矩阵 n n A)
  结论: (toFunAlgHom n R A) (invFun n R A M) = M
  证明: by
  simp only [invFun, map_sum, toFunAlgHom_apply]
  convert! Finset.sum_product (β := Matrix n n A) ..
  conv_lhs => rw [matrix_eq_sum_single M]
  simp

Depends on / 依赖: Finset, Finset.sum_product, Matrix, conv_lhs, convert, invFun, map_sum, matrix_eq_sum_single, sum_product, toFunAlgHom_apply
-/
theorem right_inv (M : Matrix n n A) : (toFunAlgHom n R A) (invFun n R A M) = M := by
  simp only [invFun, map_sum, toFunAlgHom_apply]
  convert! Finset.sum_product (β := Matrix n n A) ..
  conv_lhs => rw [matrix_eq_sum_single M]
  simp

/--
theorem `left_inv` / 定理 `left_inv`

English:
theorem left_inv
  given: (M : A otimes[R] Matrix n n R)
  statement: invFun n R A (toFunAlgHom n R A M) = M
  proof: by
  induction M with
  | zero => simp
  | tmul a m => simp
  | add x y hx hy =>
    rw [map_add]
    conv_rhs => rw [← hx, ← hy, ← invFun_add]

中文:
定理 left_inv
  条件: (M : A otimes[R] 矩阵 n n R)
  结论: invFun n R A (toFunAlgHom n R A M) = M
  证明: by
  induction M with
  | zero => simp
  | tmul a m => simp
  | add x y hx hy =>
    rw [map_add]
    conv_rhs => rw [← hx, ← hy, ← invFun_add]

Depends on / 依赖: conv_rhs, invFun_add, map_add
-/
theorem left_inv (M : A otimes[R] Matrix n n R) : invFun n R A (toFunAlgHom n R A M) = M := by
  induction M with
  | zero => simp
  | tmul a m => simp
  | add x y hx hy =>
    rw [map_add]
    conv_rhs => rw [← hx, ← hy, ← invFun_add]

/--
Definition of `equiv` / `equiv` 的定义

English:
definition equiv
  signature: : A otimes[R] Matrix n n R ≃ Matrix n n A where
  body: toFunAlgHom n R A
  invFun := invFun n R A
  left_inv := left_inv n R A
  right_inv := right_inv n R A

中文:
定义 equiv
  签名: : A otimes[R] 矩阵 n n R ≃ 矩阵 n n A where
  定义体: toFunAlgHom n R A
  invFun := invFun n R A
  left_inv := left_inv n R A
  right_inv := right_inv n R A

Depends on / 依赖: toFunAlgHom
-/
def equiv : A otimes[R] Matrix n n R ≃ Matrix n n A where
  toFun := toFunAlgHom n R A
  invFun := invFun n R A
  left_inv := left_inv n R A
  right_inv := right_inv n R A

end MatrixEquivTensor

variable [Fintype n] [DecidableEq n]

/--
Definition of `matrixEquivTensor` / `matrixEquivTensor` 的定义

English:
definition matrixEquivTensor
  signature: : Matrix n n A ≃ₐ[R] A otimes[R] Matrix n n R
  body: AlgEquiv.symm { MatrixEquivTensor.toFunAlgHom n R A, MatrixEquivTensor.equiv n R A with }

中文:
定义 matrixEquivTensor
  签名: : 矩阵 n n A ≃ₐ[R] A otimes[R] 矩阵 n n R
  定义体: AlgEquiv.symm { MatrixEquivTensor.toFunAlgHom n R A, MatrixEquivTensor.equiv n R A with }

Depends on / 依赖: AlgEquiv, AlgEquiv.symm, MatrixEquivTensor, MatrixEquivTensor.equiv, MatrixEquivTensor.toFunAlgHom, toFunAlgHom
-/
def matrixEquivTensor : Matrix n n A ≃ₐ[R] A otimes[R] Matrix n n R :=
  AlgEquiv.symm { MatrixEquivTensor.toFunAlgHom n R A, MatrixEquivTensor.equiv n R A with }

open MatrixEquivTensor

@[simp]
/--
theorem `matrixEquivTensor_apply` / 定理 `matrixEquivTensor_apply`

English:
theorem matrixEquivTensor_apply
  given: (M : Matrix n n A)
  proof: rfl

中文:
定理 matrixEquivTensor_apply
  条件: (M : 矩阵 n n A)
  证明: rfl
-/
theorem matrixEquivTensor_apply (M : Matrix n n A) :
    matrixEquivTensor n R A M = ∑ p : n × n, M p.1 p.2 otimesₜ single p.1 p.2 1 :=
  rfl

-- High priority, to go before `matrixEquivTensor_apply`
@[simp high]
/--
theorem `matrixEquivTensor_apply_single` / 定理 `matrixEquivTensor_apply_single`

English:
theorem matrixEquivTensor_apply_single
  given: (i j : n) (x : A)
  proof: by
  have t : forall p : n × n, i = p.1 ∧ j = p.2 ↔ p = (i, j) := by aesop
  simp [ite_tmul, t, single]

@[simp]

中文:
定理 matrixEquivTensor_apply_single
  条件: (i j : n) (x : A)
  证明: by
  have t : forall p : n × n, i = p.1 ∧ j = p.2 ↔ p = (i, j) := by aesop
  simp [ite_tmul, t, single]

@[simp]

Depends on / 依赖: ite_tmul, single
-/
theorem matrixEquivTensor_apply_single (i j : n) (x : A) :
    matrixEquivTensor n R A (single i j x) = x otimesₜ single i j 1 := by
  have t : forall p : n × n, i = p.1 ∧ j = p.2 ↔ p = (i, j) := by aesop
  simp [ite_tmul, t, single]

@[simp]
/--
theorem `matrixEquivTensor_apply_symm` / 定理 `matrixEquivTensor_apply_symm`

English:
theorem matrixEquivTensor_apply_symm
  given: (a : A) (M : Matrix n n R)
  proof: rfl

中文:
定理 matrixEquivTensor_apply_symm
  条件: (a : A) (M : 矩阵 n n R)
  证明: rfl
-/
theorem matrixEquivTensor_apply_symm (a : A) (M : Matrix n n R) :
    (matrixEquivTensor n R A).symm (a otimesₜ M) = a • M.map (algebraMap R A) :=
  rfl

namespace Matrix
open scoped Kronecker

variable (m) (S B)
variable [CommSemiring S] [Algebra R S] [Algebra S A] [IsScalarTower R S A]
variable [Fintype m] [DecidableEq m]

/--
Definition of `kroneckerTMulAlgEquiv` / `kroneckerTMulAlgEquiv` 的定义

English:
definition kroneckerTMulAlgEquiv
  signature: :
  body: .ofLinearEquiv (kroneckerTMulLinearEquiv m m n n R S A B)
    (kroneckerTMulLinearEquiv_one _ _ _ _ _)
    (kroneckerTMulLinearEquiv_mul _ _ _ _ _)

中文:
定义 kroneckerTMulAlgEquiv
  签名: :
  定义体: .ofLinearEquiv (kroneckerTMulLinearEquiv m m n n R S A B)
    (kroneckerTMulLinearEquiv_one _ _ _ _ _)
    (kroneckerTMulLinearEquiv_mul _ _ _ _ _)

Depends on / 依赖: kroneckerTMulLinearEquiv, kroneckerTMulLinearEquiv_mul, kroneckerTMulLinearEquiv_one, ofLinearEquiv
-/
def kroneckerTMulAlgEquiv :
    Matrix m m A otimes[R] Matrix n n B ≃ₐ[S] Matrix (m × n) (m × n) (A otimes[R] B) :=
  .ofLinearEquiv (kroneckerTMulLinearEquiv m m n n R S A B)
    (kroneckerTMulLinearEquiv_one _ _ _ _ _)
    (kroneckerTMulLinearEquiv_mul _ _ _ _ _)

variable {m n A B}

@[simp]
/--
theorem `kroneckerTMulAlgEquiv_apply` / 定理 `kroneckerTMulAlgEquiv_apply`

English:
theorem kroneckerTMulAlgEquiv_apply
  given: (x : Matrix m m A otimes[R] Matrix n n B)
  proof: rfl

@[simp]

中文:
定理 kroneckerTMulAlgEquiv_apply
  条件: (x : 矩阵 m m A otimes[R] 矩阵 n n B)
  证明: rfl

@[simp]
-/
theorem kroneckerTMulAlgEquiv_apply (x : Matrix m m A otimes[R] Matrix n n B) :
    (kroneckerTMulAlgEquiv m n R S A B) x = kroneckerTMulLinearEquiv m m n n R S A B x :=
  rfl

@[simp]
/--
theorem `kroneckerTMulAlgEquiv_symm_apply` / 定理 `kroneckerTMulAlgEquiv_symm_apply`

English:
theorem kroneckerTMulAlgEquiv_symm_apply
  given: (x : Matrix (m × n) (m × n) (A otimes[R] B))
  proof: rfl

中文:
定理 kroneckerTMulAlgEquiv_symm_apply
  条件: (x : 矩阵 (m × n) (m × n) (A otimes[R] B))
  证明: rfl
-/
theorem kroneckerTMulAlgEquiv_symm_apply (x : Matrix (m × n) (m × n) (A otimes[R] B)) :
    (kroneckerTMulAlgEquiv m n R S A B).symm x =
      (kroneckerTMulLinearEquiv m m n n R S A B).symm x :=
  rfl

section StarRing
variable [StarRing R] [StarAddMonoid A] [StarAddMonoid B] [StarModule R A] [StarModule R B]

variable (m n A B) in
/--
Definition of `kroneckerTMulStarAlgEquiv` / `kroneckerTMulStarAlgEquiv` 的定义

English:
definition kroneckerTMulStarAlgEquiv
  signature: :
  body: .ofAlgEquiv (kroneckerTMulAlgEquiv m n R S A B)
  fun x => x.induction_on (by simp)
    (by simp [star_eq_conjTranspose, conjTranspose_kroneckerTMul])
    (by simp_all)

中文:
定义 kroneckerTMulStarAlgEquiv
  签名: :
  定义体: .ofAlgEquiv (kroneckerTMulAlgEquiv m n R S A B)
  fun x => x.induction_on (by simp)
    (by simp [star_eq_conjTranspose, conjTranspose_kroneckerTMul])
    (by simp_all)

Depends on / 依赖: conjTranspose_kroneckerTMul, induction_on, kroneckerTMulAlgEquiv, ofAlgEquiv, star_eq_conjTranspose, x.induction_on
-/
def kroneckerTMulStarAlgEquiv :
    Matrix m m A otimes[R] Matrix n n B ≃⋆ₐ[S] Matrix (m × n) (m × n) (A otimes[R] B) :=
  .ofAlgEquiv (kroneckerTMulAlgEquiv m n R S A B)
  fun x => x.induction_on (by simp)
    (by simp [star_eq_conjTranspose, conjTranspose_kroneckerTMul])
    (by simp_all)

/--
theorem `toAlgEquiv_kroneckerTMulStarAlgEquiv` / 定理 `toAlgEquiv_kroneckerTMulStarAlgEquiv`

English:
theorem toAlgEquiv_kroneckerTMulStarAlgEquiv
  proof: rfl

中文:
定理 toAlgEquiv_kroneckerTMulStarAlgEquiv
  证明: rfl
-/
@[simp] theorem toAlgEquiv_kroneckerTMulStarAlgEquiv :
    (kroneckerTMulStarAlgEquiv m n R S A B).toAlgEquiv =
      kroneckerTMulAlgEquiv m n R S A B := rfl

/--
theorem `kroneckerTMulStarAlgEquiv_apply` / 定理 `kroneckerTMulStarAlgEquiv_apply`

English:
theorem kroneckerTMulStarAlgEquiv_apply
  given: (x : Matrix m m A otimes[R] Matrix n n B)
  proof: rfl

中文:
定理 kroneckerTMulStarAlgEquiv_apply
  条件: (x : 矩阵 m m A otimes[R] 矩阵 n n B)
  证明: rfl
-/
@[simp] theorem kroneckerTMulStarAlgEquiv_apply (x : Matrix m m A otimes[R] Matrix n n B) :
    (kroneckerTMulStarAlgEquiv m n R S A B) x =
      kroneckerTMulLinearEquiv m m n n R S A B x :=
  rfl

/--
theorem `kroneckerTMulStarAlgEquiv_symm_apply` / 定理 `kroneckerTMulStarAlgEquiv_symm_apply`

English:
theorem kroneckerTMulStarAlgEquiv_symm_apply
  given: (x : Matrix (m × n) (m × n) (A otimes[R] B))
  proof: rfl

中文:
定理 kroneckerTMulStarAlgEquiv_symm_apply
  条件: (x : 矩阵 (m × n) (m × n) (A otimes[R] B))
  证明: rfl
-/
@[simp] theorem kroneckerTMulStarAlgEquiv_symm_apply (x : Matrix (m × n) (m × n) (A otimes[R] B)) :
    (kroneckerTMulStarAlgEquiv m n R S A B).symm x =
      (kroneckerTMulLinearEquiv m m n n R S A B).symm x :=
  rfl

end StarRing

variable (m n) in
/--
Definition of `kroneckerAlgEquiv` / `kroneckerAlgEquiv` 的定义

English:
definition kroneckerAlgEquiv
  signature: : (Matrix m m R otimes[R] Matrix n n R) ≃ₐ[R] Matrix (m × n) (m × n) R
  body: (kroneckerTMulAlgEquiv m n R R R R).trans (Algebra.TensorProduct.lid R R).mapMatrix

中文:
定义 kroneckerAlgEquiv
  签名: : (矩阵 m m R otimes[R] 矩阵 n n R) ≃ₐ[R] 矩阵 (m × n) (m × n) R
  定义体: (kroneckerTMulAlgEquiv m n R R R R).trans (Algebra.TensorProduct.lid R R).mapMatrix

Depends on / 依赖: Algebra, Algebra.TensorProduct.lid, TensorProduct, kroneckerTMulAlgEquiv, mapMatrix
-/
def kroneckerAlgEquiv : (Matrix m m R otimes[R] Matrix n n R) ≃ₐ[R] Matrix (m × n) (m × n) R :=
  (kroneckerTMulAlgEquiv m n R R R R).trans (Algebra.TensorProduct.lid R R).mapMatrix

/--
theorem `toLinearEquiv_kroneckerAlgEquiv` / 定理 `toLinearEquiv_kroneckerAlgEquiv`

English:
theorem toLinearEquiv_kroneckerAlgEquiv
  proof: rfl

中文:
定理 toLinearEquiv_kroneckerAlgEquiv
  证明: rfl
-/
@[simp] theorem toLinearEquiv_kroneckerAlgEquiv :
    (kroneckerAlgEquiv m n R).toLinearEquiv = kroneckerLinearEquiv m m n n R := rfl

/--
theorem `kroneckerAlgEquiv_apply` / 定理 `kroneckerAlgEquiv_apply`

English:
theorem kroneckerAlgEquiv_apply
  given: (x : Matrix m m R otimes Matrix n n R)
  proof: rfl

中文:
定理 kroneckerAlgEquiv_apply
  条件: (x : 矩阵 m m R otimes 矩阵 n n R)
  证明: rfl
-/
@[simp] theorem kroneckerAlgEquiv_apply (x : Matrix m m R otimes Matrix n n R) :
    kroneckerAlgEquiv m n R x = kroneckerLinearEquiv m m n n R x := rfl

/--
theorem `kroneckerAlgEquiv_symm_apply` / 定理 `kroneckerAlgEquiv_symm_apply`

English:
theorem kroneckerAlgEquiv_symm_apply
  given: (x : Matrix (m × n) (m × n) R)
  proof: rfl

中文:
定理 kroneckerAlgEquiv_symm_apply
  条件: (x : 矩阵 (m × n) (m × n) R)
  证明: rfl
-/
@[simp] theorem kroneckerAlgEquiv_symm_apply (x : Matrix (m × n) (m × n) R) :
    (kroneckerAlgEquiv m n R).symm x = (kroneckerLinearEquiv m m n n R).symm x := rfl

variable (m n) in
/--
Definition of `kroneckerStarAlgEquiv` / `kroneckerStarAlgEquiv` 的定义

English:
definition kroneckerStarAlgEquiv
  signature: [StarRing R]
  body: .ofAlgEquiv (kroneckerAlgEquiv m n R)
  fun x => x.induction_on (by simp)
    (by simp [star_eq_conjTranspose, conjTranspose_kronecker])
    (by simp_all)

中文:
定义 kroneckerStarAlgEquiv
  签名: [对合环 R]
  定义体: .ofAlgEquiv (kroneckerAlgEquiv m n R)
  fun x => x.induction_on (by simp)
    (by simp [star_eq_conjTranspose, conjTranspose_kronecker])
    (by simp_all)

Depends on / 依赖: conjTranspose_kronecker, induction_on, kroneckerAlgEquiv, ofAlgEquiv, star_eq_conjTranspose, x.induction_on
-/
def kroneckerStarAlgEquiv [StarRing R] :
    (Matrix m m R otimes[R] Matrix n n R) ≃⋆ₐ[R] Matrix (m × n) (m × n) R :=
  .ofAlgEquiv (kroneckerAlgEquiv m n R)
  fun x => x.induction_on (by simp)
    (by simp [star_eq_conjTranspose, conjTranspose_kronecker])
    (by simp_all)

/--
theorem `toAlgEquiv_kroneckerStarAlgEquiv` / 定理 `toAlgEquiv_kroneckerStarAlgEquiv`

English:
theorem toAlgEquiv_kroneckerStarAlgEquiv
  given: [StarRing R]
  proof: rfl

中文:
定理 toAlgEquiv_kroneckerStarAlgEquiv
  条件: [对合环 R]
  证明: rfl
-/
@[simp] theorem toAlgEquiv_kroneckerStarAlgEquiv [StarRing R] :
    (kroneckerStarAlgEquiv m n R).toAlgEquiv = kroneckerAlgEquiv m n R := rfl

/--
theorem `kroneckerStarAlgEquiv_apply` / 定理 `kroneckerStarAlgEquiv_apply`

English:
theorem kroneckerStarAlgEquiv_apply
  given: [StarRing R] (x : Matrix m m R otimes Matrix n n R)
  proof: rfl

中文:
定理 kroneckerStarAlgEquiv_apply
  条件: [对合环 R] (x : 矩阵 m m R otimes 矩阵 n n R)
  证明: rfl
-/
@[simp] theorem kroneckerStarAlgEquiv_apply [StarRing R] (x : Matrix m m R otimes Matrix n n R) :
    kroneckerStarAlgEquiv m n R x = kroneckerLinearEquiv m m n n R x := rfl

/--
theorem `kroneckerStarAlgEquiv_symm_apply` / 定理 `kroneckerStarAlgEquiv_symm_apply`

English:
theorem kroneckerStarAlgEquiv_symm_apply
  given: [StarRing R] (x : Matrix (m × n) (m × n) R)
  proof: rfl

中文:
定理 kroneckerStarAlgEquiv_symm_apply
  条件: [对合环 R] (x : 矩阵 (m × n) (m × n) R)
  证明: rfl
-/
@[simp] theorem kroneckerStarAlgEquiv_symm_apply [StarRing R] (x : Matrix (m × n) (m × n) R) :
    (kroneckerStarAlgEquiv m n R).symm x = (kroneckerLinearEquiv m m n n R).symm x := rfl

end Matrix
