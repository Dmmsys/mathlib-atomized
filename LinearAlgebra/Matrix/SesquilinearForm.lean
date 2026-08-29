/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Kexing Ying, Moritz Doll
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.Opposite
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.LinearAlgebra.Basis.Bilinear

/-!
# Sesquilinear form

This file defines the conversion between sesquilinear maps and matrices.

## Main definitions

* `Matrix.toLinearMap₂` given a basis define a bilinear map
* `Matrix.toLinearMap₂'` define the bilinear map on `n → R`
* `LinearMap.toMatrix₂`: calculate the matrix coefficients of a bilinear map
* `LinearMap.toMatrix₂'`: calculate the matrix coefficients of a bilinear map on `n → R`

## TODO

At the moment this is quite a literal port from `Matrix.BilinearForm`. Everything should be
generalized to fully semi-bilinear forms.

## Tags

Sesquilinear form, Sesquilinear map, matrix, basis

-/

@[expose] public section

open Finset LinearMap Matrix Module
open scoped RightActions

variable {R R₁ S₁ R₂ S₂ M₁ M₂ M₁' M₂' N₂ n m n' m' ι : Type*}

section AuxToLinearMap

variable [Semiring R₁] [Semiring S₁] [Semiring R₂] [Semiring S₂] [AddCommMonoid N₂]
  [Module S₁ N₂] [Module S₂ N₂] [SMulCommClass S₂ S₁ N₂]
variable [Fintype n] [Fintype m]
variable (σ₁ : R₁ ->+* S₁) (σ₂ : R₂ ->+* S₂)

/--
Definition of `Matrix.toLinearMap₂'Aux` / `Matrix.toLinearMap₂'Aux` 的定义

English:
definition Matrix.toLinearMap₂'Aux
  signature: (f : Matrix n m N₂)
  body: -- porting note: we don't seem to have `∑ i j` as valid notation yet
  mk₂'ₛₗ σ₁ σ₂ (fun (v : n -> R₁) (w : m -> R₂) => ∑ i, ∑ j, σ₂ (w j) • σ₁ (v i) • f i j)
    (fun _ _ _ => by simp only [Pi.add_apply, map_add, smul_add, sum_add_distrib, add_smul])
    (fun c v w => by
      simp only [Pi.smul_apply, smul_sum, smul_eq_mul, σ₁.map_mul, ← smul_comm _ (σ₁ c), mul_smul])
    (fun _ _ _ => by simp only [Pi.add_apply, map_add, add_smul, sum_add_distrib])
    (fun _ v w => by simp only [Pi.smul_apply, smul_eq_mul, map_mul, mul_smul, smul_sum])

中文:
定义 矩阵.toLinearMap₂'Aux
  签名: (f : 矩阵 n m N₂)
  定义体: -- porting note: we don't seem to have `∑ i j` as valid notation yet
  mk₂'ₛₗ σ₁ σ₂ (fun (v : n -> R₁) (w : m -> R₂) => ∑ i, ∑ j, σ₂ (w j) • σ₁ (v i) • f i j)
    (fun _ _ _ => by simp only [Pi.add_apply, map_add, smul_add, sum_add_distrib, add_smul])
    (fun c v w => by
      simp only [Pi.smul_apply, smul_sum, smul_eq_mul, σ₁.map_mul, ← smul_comm _ (σ₁ c), mul_smul])
    (fun _ _ _ => by simp only [Pi.add_apply, map_add, add_smul, sum_add_distrib])
    (fun _ v w => by simp only [Pi.smul_apply, smul_eq_mul, map_mul, mul_smul, smul_sum])
-/
def Matrix.toLinearMap₂'Aux (f : Matrix n m N₂) : (n -> R₁) ->ₛₗ[σ₁] (m -> R₂) ->ₛₗ[σ₂] N₂ :=
  -- porting note: we don't seem to have `∑ i j` as valid notation yet
  mk₂'ₛₗ σ₁ σ₂ (fun (v : n -> R₁) (w : m -> R₂) => ∑ i, ∑ j, σ₂ (w j) • σ₁ (v i) • f i j)
    (fun _ _ _ => by simp only [Pi.add_apply, map_add, smul_add, sum_add_distrib, add_smul])
    (fun c v w => by
      simp only [Pi.smul_apply, smul_sum, smul_eq_mul, σ₁.map_mul, ← smul_comm _ (σ₁ c), mul_smul])
    (fun _ _ _ => by simp only [Pi.add_apply, map_add, add_smul, sum_add_distrib])
    (fun _ v w => by simp only [Pi.smul_apply, smul_eq_mul, map_mul, mul_smul, smul_sum])

variable [DecidableEq n] [DecidableEq m]

/--
theorem `Matrix.toLinearMap₂'Aux_single` / 定理 `Matrix.toLinearMap₂'Aux_single`

English:
theorem Matrix.toLinearMap₂'Aux_single
  given: (f : Matrix n m N₂) (i : n) (j : m)
  proof: by
  rw [Matrix.toLinearMap₂'Aux]; rw [mk₂'ₛₗ_apply]
  have : (∑ i', ∑ j', (if i = i' then (1 : S₁) else (0 : S₁)) •
        (if j = j' then (1 : S₂) else (0 : S₂)) • f i' j') =
      f i j := by
    simp_rw [← Finset.smul_sum]
    simp only [ite_smul, one_smul, zero_smul, sum_ite_eq, mem_univ, ↓reduceIte]
  rw [← this]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by aesop

中文:
定理 矩阵.toLinearMap₂'Aux_single
  条件: (f : 矩阵 n m N₂) (i : n) (j : m)
  证明: by
  rw [Matrix.toLinearMap₂'Aux]; rw [mk₂'ₛₗ_apply]
  have : (∑ i', ∑ j', (if i = i' then (1 : S₁) else (0 : S₁)) •
        (if j = j' then (1 : S₂) else (0 : S₂)) • f i' j') =
      f i j := by
    simp_rw [← Finset.smul_sum]
    simp only [ite_smul, one_smul, zero_smul, sum_ite_eq, mem_univ, ↓reduceIte]
  rw [← this]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by aesop
-/
theorem Matrix.toLinearMap₂'Aux_single (f : Matrix n m N₂) (i : n) (j : m) :
    f.toLinearMap₂'Aux σ₁ σ₂ (Pi.single i 1) (Pi.single j 1) = f i j := by
  rw [Matrix.toLinearMap₂'Aux]; rw [mk₂'ₛₗ_apply]
  have : (∑ i', ∑ j', (if i = i' then (1 : S₁) else (0 : S₁)) •
        (if j = j' then (1 : S₂) else (0 : S₂)) • f i' j') =
      f i j := by
    simp_rw [← Finset.smul_sum]
    simp only [ite_smul, one_smul, zero_smul, sum_ite_eq, mem_univ, ↓reduceIte]
  rw [← this]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by aesop

end AuxToLinearMap

section AuxToMatrix

section CommSemiring

variable [CommSemiring R] [Semiring R₁] [Semiring S₁] [Semiring R₂] [Semiring S₂]
variable [AddCommMonoid M₁] [Module R₁ M₁] [AddCommMonoid M₂] [Module R₂ M₂] [AddCommMonoid N₂]
  [Module R N₂] [Module S₁ N₂] [Module S₂ N₂] [SMulCommClass S₁ R N₂] [SMulCommClass S₂ R N₂]
  [SMulCommClass S₂ S₁ N₂]
variable {σ₁ : R₁ ->+* S₁} {σ₂ : R₂ ->+* S₂}
variable (R)

/--
Definition of `LinearMap.toMatrix₂Aux` / `LinearMap.toMatrix₂Aux` 的定义

English:
definition LinearMap.toMatrix₂Aux
  signature: (b₁ : n -> M₁) (b₂ : m -> M₂)
  body: of fun i j => f (b₁ i) (b₂ j)
  map_add' _f _g := rfl
  map_smul' _f _g := rfl

@[simp]

中文:
定义 线性映射.toMatrix₂Aux
  签名: (b₁ : n -> M₁) (b₂ : m -> M₂)
  定义体: of fun i j => f (b₁ i) (b₂ j)
  map_add' _f _g := rfl
  map_smul' _f _g := rfl

@[simp]
-/
def LinearMap.toMatrix₂Aux (b₁ : n -> M₁) (b₂ : m -> M₂) :
    (M₁ ->ₛₗ[σ₁] M₂ ->ₛₗ[σ₂] N₂) ->ₗ[R] Matrix n m N₂ where
  toFun f := of fun i j => f (b₁ i) (b₂ j)
  map_add' _f _g := rfl
  map_smul' _f _g := rfl

@[simp]
/--
theorem `LinearMap.toMatrix₂Aux_apply` / 定理 `LinearMap.toMatrix₂Aux_apply`

English:
theorem LinearMap.toMatrix₂Aux_apply
  statement: (f : M₁ ->ₛₗ[σ₁] M₂ ->ₛₗ[σ₂] N₂) (b₁ : n -> M₁) (b₂ : m -> M₂)
  proof: rfl

中文:
定理 线性映射.toMatrix₂Aux_apply
  结论: (f : M₁ ->ₛₗ[σ₁] M₂ ->ₛₗ[σ₂] N₂) (b₁ : n -> M₁) (b₂ : m -> M₂)
  证明: rfl
-/
theorem LinearMap.toMatrix₂Aux_apply (f : M₁ ->ₛₗ[σ₁] M₂ ->ₛₗ[σ₂] N₂) (b₁ : n -> M₁) (b₂ : m -> M₂)
    (i : n) (j : m) : LinearMap.toMatrix₂Aux R b₁ b₂ f i j = f (b₁ i) (b₂ j) :=
  rfl

variable [Fintype n] [Fintype m]
variable [DecidableEq n] [DecidableEq m]

/--
theorem `LinearMap.toLinearMap₂'Aux_toMatrix₂Aux` / 定理 `LinearMap.toLinearMap₂'Aux_toMatrix₂Aux`

English:
theorem LinearMap.toLinearMap₂'Aux_toMatrix₂Aux
  given: (f : (n -> R₁) ->ₛₗ[σ₁] (m -> R₂) ->ₛₗ[σ₂] N₂)
  proof: by
  refine ext_basis (Pi.basisFun R₁ n) (Pi.basisFun R₂ m) fun i j => ?_
  simp_rw [Pi.basisFun_apply, Matrix.toLinearMap₂'Aux_single, LinearMap.toMatrix₂Aux_apply]

中文:
定理 线性映射.toLinearMap₂'Aux_toMatrix₂Aux
  条件: (f : (n -> R₁) ->ₛₗ[σ₁] (m -> R₂) ->ₛₗ[σ₂] N₂)
  证明: by
  refine ext_basis (Pi.basisFun R₁ n) (Pi.basisFun R₂ m) fun i j => ?_
  simp_rw [Pi.basisFun_apply, Matrix.toLinearMap₂'Aux_single, LinearMap.toMatrix₂Aux_apply]

Depends on / 依赖: Aux_single, LinearMap, LinearMap.toMatrix, Matrix, Matrix.toLinearMap, Pi.basisFun, Pi.basisFun_apply, basisFun, basisFun_apply, ext_basis, simp_rw
-/
theorem LinearMap.toLinearMap₂'Aux_toMatrix₂Aux (f : (n -> R₁) ->ₛₗ[σ₁] (m -> R₂) ->ₛₗ[σ₂] N₂) :
    Matrix.toLinearMap₂'Aux σ₁ σ₂
        (LinearMap.toMatrix₂Aux R (fun i => Pi.single i 1) (fun j => Pi.single j 1) f) =
      f := by
  refine ext_basis (Pi.basisFun R₁ n) (Pi.basisFun R₂ m) fun i j => ?_
  simp_rw [Pi.basisFun_apply, Matrix.toLinearMap₂'Aux_single, LinearMap.toMatrix₂Aux_apply]

/--
theorem `Matrix.toMatrix₂Aux_toLinearMap₂'Aux` / 定理 `Matrix.toMatrix₂Aux_toLinearMap₂'Aux`

English:
theorem Matrix.toMatrix₂Aux_toLinearMap₂'Aux
  given: (f : Matrix n m N₂)
  proof: by
  ext i j
  simp_rw [LinearMap.toMatrix₂Aux_apply, Matrix.toLinearMap₂'Aux_single]

中文:
定理 矩阵.toMatrix₂Aux_toLinearMap₂'Aux
  条件: (f : 矩阵 n m N₂)
  证明: by
  ext i j
  simp_rw [LinearMap.toMatrix₂Aux_apply, Matrix.toLinearMap₂'Aux_single]

Depends on / 依赖: Aux_single, LinearMap, LinearMap.toMatrix, Matrix, Matrix.toLinearMap, simp_rw
-/
theorem Matrix.toMatrix₂Aux_toLinearMap₂'Aux (f : Matrix n m N₂) :
    LinearMap.toMatrix₂Aux R (fun i => Pi.single i 1)
        (fun j => Pi.single j 1) (f.toLinearMap₂'Aux σ₁ σ₂) =
      f := by
  ext i j
  simp_rw [LinearMap.toMatrix₂Aux_apply, Matrix.toLinearMap₂'Aux_single]

end CommSemiring

end AuxToMatrix

section ToMatrix'

/-! ### Bilinear maps over `n → R`

This section deals with the conversion between matrices and sesquilinear maps on `n → R`.
-/

variable [CommSemiring R] [AddCommMonoid N₂] [Module R N₂] [Semiring R₁] [Semiring R₂]
  [Semiring S₁] [Semiring S₂] [Module S₁ N₂] [Module S₂ N₂]
  [SMulCommClass S₁ R N₂] [SMulCommClass S₂ R N₂] [SMulCommClass S₂ S₁ N₂]
variable {σ₁ : R₁ ->+* S₁} {σ₂ : R₂ ->+* S₂}
variable [Fintype n] [Fintype m]
variable [DecidableEq n] [DecidableEq m]

variable (R)

/--
Definition of `LinearMap.toMatrixₛₗ₂'` / `LinearMap.toMatrixₛₗ₂'` 的定义

English:
definition LinearMap.toMatrixₛₗ₂'
  signature: : ((n -> R₁) ->ₛₗ[σ₁] (m -> R₂) ->ₛₗ[σ₂] N₂) ≃ₗ[R] Matrix n m N₂
  body: { LinearMap.toMatrix₂Aux R (fun i => Pi.single i 1) (fun j => Pi.single j 1) with
    toFun := LinearMap.toMatrix₂Aux R _ _
    invFun := Matrix.toLinearMap₂'Aux σ₁ σ₂
    left_inv := LinearMap.toLinearMap₂'Aux_toMatrix₂Aux R
    right_inv := Matrix.toMatrix₂Aux_toLinearMap₂'Aux R }

中文:
定义 线性映射.toMatrixₛₗ₂'
  签名: : ((n -> R₁) ->ₛₗ[σ₁] (m -> R₂) ->ₛₗ[σ₂] N₂) ≃ₗ[R] 矩阵 n m N₂
  定义体: { LinearMap.toMatrix₂Aux R (fun i => Pi.single i 1) (fun j => Pi.single j 1) with
    toFun := LinearMap.toMatrix₂Aux R _ _
    invFun := Matrix.toLinearMap₂'Aux σ₁ σ₂
    left_inv := LinearMap.toLinearMap₂'Aux_toMatrix₂Aux R
    right_inv := Matrix.toMatrix₂Aux_toLinearMap₂'Aux R }

Depends on / 依赖: LinearMap, LinearMap.toLinearMap, LinearMap.toMatrix, Matrix, Matrix.toLinearMap, Matrix.toMatrix, Pi.single, invFun, left_inv, right_inv, single
-/
def LinearMap.toMatrixₛₗ₂' : ((n -> R₁) ->ₛₗ[σ₁] (m -> R₂) ->ₛₗ[σ₂] N₂) ≃ₗ[R] Matrix n m N₂ :=
  { LinearMap.toMatrix₂Aux R (fun i => Pi.single i 1) (fun j => Pi.single j 1) with
    toFun := LinearMap.toMatrix₂Aux R _ _
    invFun := Matrix.toLinearMap₂'Aux σ₁ σ₂
    left_inv := LinearMap.toLinearMap₂'Aux_toMatrix₂Aux R
    right_inv := Matrix.toMatrix₂Aux_toLinearMap₂'Aux R }

/--
Definition of `LinearMap.toMatrix₂'` / `LinearMap.toMatrix₂'` 的定义

English:
definition LinearMap.toMatrix₂'
  signature: : ((n -> S₁) ->ₗ[S₁] (m -> S₂) ->ₗ[S₂] N₂) ≃ₗ[R] Matrix n m N₂
  body: LinearMap.toMatrixₛₗ₂' R

中文:
定义 线性映射.toMatrix₂'
  签名: : ((n -> S₁) ->ₗ[S₁] (m -> S₂) ->ₗ[S₂] N₂) ≃ₗ[R] 矩阵 n m N₂
  定义体: LinearMap.toMatrixₛₗ₂' R

Depends on / 依赖: LinearMap, LinearMap.toMatrix
-/
def LinearMap.toMatrix₂' : ((n -> S₁) ->ₗ[S₁] (m -> S₂) ->ₗ[S₂] N₂) ≃ₗ[R] Matrix n m N₂ :=
  LinearMap.toMatrixₛₗ₂' R

variable (σ₁ σ₂)

/--
Definition of `Matrix.toLinearMapₛₗ₂'` / `Matrix.toLinearMapₛₗ₂'` 的定义

English:
definition Matrix.toLinearMapₛₗ₂'
  signature: : Matrix n m N₂ ≃ₗ[R] (n -> R₁) ->ₛₗ[σ₁] (m -> R₂) ->ₛₗ[σ₂] N₂
  body: (LinearMap.toMatrixₛₗ₂' R).symm

中文:
定义 矩阵.toLinearMapₛₗ₂'
  签名: : 矩阵 n m N₂ ≃ₗ[R] (n -> R₁) ->ₛₗ[σ₁] (m -> R₂) ->ₛₗ[σ₂] N₂
  定义体: (LinearMap.toMatrixₛₗ₂' R).symm

Depends on / 依赖: LinearMap, LinearMap.toMatrix
-/
def Matrix.toLinearMapₛₗ₂' : Matrix n m N₂ ≃ₗ[R] (n -> R₁) ->ₛₗ[σ₁] (m -> R₂) ->ₛₗ[σ₂] N₂ :=
  (LinearMap.toMatrixₛₗ₂' R).symm

/--
Definition of `Matrix.toLinearMap₂'` / `Matrix.toLinearMap₂'` 的定义

English:
definition Matrix.toLinearMap₂'
  signature: : Matrix n m N₂ ≃ₗ[R] (n -> S₁) ->ₗ[S₁] (m -> S₂) ->ₗ[S₂] N₂
  body: (LinearMap.toMatrix₂' R).symm

中文:
定义 矩阵.toLinearMap₂'
  签名: : 矩阵 n m N₂ ≃ₗ[R] (n -> S₁) ->ₗ[S₁] (m -> S₂) ->ₗ[S₂] N₂
  定义体: (LinearMap.toMatrix₂' R).symm
-/
def Matrix.toLinearMap₂' : Matrix n m N₂ ≃ₗ[R] (n -> S₁) ->ₗ[S₁] (m -> S₂) ->ₗ[S₂] N₂ :=
  (LinearMap.toMatrix₂' R).symm

variable {R}

/--
theorem `Matrix.toLinearMapₛₗ₂'_aux_eq` / 定理 `Matrix.toLinearMapₛₗ₂'_aux_eq`

English:
theorem Matrix.toLinearMapₛₗ₂'_aux_eq
  given: (M : Matrix n m N₂)
  proof: rfl

中文:
定理 矩阵.toLinearMapₛₗ₂'_aux_eq
  条件: (M : 矩阵 n m N₂)
  证明: rfl
-/
theorem Matrix.toLinearMapₛₗ₂'_aux_eq (M : Matrix n m N₂) :
    Matrix.toLinearMap₂'Aux σ₁ σ₂ M = Matrix.toLinearMapₛₗ₂' R σ₁ σ₂ M :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Matrix.toLinearMapₛₗ₂'_apply` / 定理 `Matrix.toLinearMapₛₗ₂'_apply`

English:
theorem Matrix.toLinearMapₛₗ₂'_apply
  given: (M : Matrix n m N₂) (x : n -> R₁) (y : m -> R₂)
  proof: by
  rw [toLinearMapₛₗ₂']; rw [toMatrixₛₗ₂']; rw [LinearEquiv.coe_symm_mk]; rw [toLinearMap₂'Aux]; rw [mk₂'ₛₗ_apply]
  apply Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by
    rw [smul_comm]

中文:
定理 矩阵.toLinearMapₛₗ₂'_apply
  条件: (M : 矩阵 n m N₂) (x : n -> R₁) (y : m -> R₂)
  证明: by
  rw [toLinearMapₛₗ₂']; rw [toMatrixₛₗ₂']; rw [LinearEquiv.coe_symm_mk]; rw [toLinearMap₂'Aux]; rw [mk₂'ₛₗ_apply]
  apply Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by
    rw [smul_comm]
-/
theorem Matrix.toLinearMapₛₗ₂'_apply (M : Matrix n m N₂) (x : n -> R₁) (y : m -> R₂) :
    -- porting note: we don't seem to have `∑ i j` as valid notation yet
    Matrix.toLinearMapₛₗ₂' R σ₁ σ₂ M x y = ∑ i, ∑ j, σ₁ (x i) • σ₂ (y j) • M i j := by
  rw [toLinearMapₛₗ₂']; rw [toMatrixₛₗ₂']; rw [LinearEquiv.coe_symm_mk]; rw [toLinearMap₂'Aux]; rw [mk₂'ₛₗ_apply]
  apply Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by
    rw [smul_comm]

/--
theorem `Matrix.toLinearMap₂'_apply` / 定理 `Matrix.toLinearMap₂'_apply`

English:
theorem Matrix.toLinearMap₂'_apply
  given: (M : Matrix n m N₂) (x : n -> S₁) (y : m -> S₂)
  proof: Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by
    rw [RingHom.id_apply]; rw [RingHom.id_apply]; rw [smul_comm]

中文:
定理 矩阵.toLinearMap₂'_apply
  条件: (M : 矩阵 n m N₂) (x : n -> S₁) (y : m -> S₂)
  证明: Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by
    rw [RingHom.id_apply]; rw [RingHom.id_apply]; rw [smul_comm]
-/
theorem Matrix.toLinearMap₂'_apply (M : Matrix n m N₂) (x : n -> S₁) (y : m -> S₂) :
    -- porting note: we don't seem to have `∑ i j` as valid notation yet
    Matrix.toLinearMap₂' R M x y = ∑ i, ∑ j, x i • y j • M i j :=
  Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by
    rw [RingHom.id_apply]; rw [RingHom.id_apply]; rw [smul_comm]

/--
theorem `Matrix.toLinearMap₂'_apply'` / 定理 `Matrix.toLinearMap₂'_apply'`

English:
theorem Matrix.toLinearMap₂'_apply'
  statement: {T : Type*} [CommSemiring T] (M : Matrix n m T) (v : n -> T)
  proof: by
  simp_rw [Matrix.toLinearMap₂'_apply, dotProduct, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [smul_eq_mul]; rw [smul_eq_mul]; rw [mul_comm (w _)]; rw [← mul_assoc]

@[simp]

中文:
定理 矩阵.toLinearMap₂'_apply'
  结论: {T : 类型} [交换半环 T] (M : 矩阵 n m T) (v : n -> T)
  证明: by
  simp_rw [Matrix.toLinearMap₂'_apply, dotProduct, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [smul_eq_mul]; rw [smul_eq_mul]; rw [mul_comm (w _)]; rw [← mul_assoc]

@[simp]
-/
theorem Matrix.toLinearMap₂'_apply' {T : Type*} [CommSemiring T] (M : Matrix n m T) (v : n -> T)
    (w : m -> T) : Matrix.toLinearMap₂' T M v w = v ⬝ᵥ (M *ᵥ w) := by
  simp_rw [Matrix.toLinearMap₂'_apply, dotProduct, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [smul_eq_mul]; rw [smul_eq_mul]; rw [mul_comm (w _)]; rw [← mul_assoc]

@[simp]
/--
theorem `Matrix.toLinearMapₛₗ₂'_single` / 定理 `Matrix.toLinearMapₛₗ₂'_single`

English:
theorem Matrix.toLinearMapₛₗ₂'_single
  given: (M : Matrix n m N₂) (i : n) (j : m)
  proof: Matrix.toLinearMap₂'Aux_single σ₁ σ₂ M i j

@[simp]

中文:
定理 矩阵.toLinearMapₛₗ₂'_single
  条件: (M : 矩阵 n m N₂) (i : n) (j : m)
  证明: Matrix.toLinearMap₂'Aux_single σ₁ σ₂ M i j

@[simp]
-/
theorem Matrix.toLinearMapₛₗ₂'_single (M : Matrix n m N₂) (i : n) (j : m) :
    Matrix.toLinearMapₛₗ₂' R σ₁ σ₂ M (Pi.single i 1) (Pi.single j 1) = M i j :=
  Matrix.toLinearMap₂'Aux_single σ₁ σ₂ M i j

@[simp]
/--
theorem `Matrix.toLinearMap₂'_single` / 定理 `Matrix.toLinearMap₂'_single`

English:
theorem Matrix.toLinearMap₂'_single
  given: (M : Matrix n m N₂) (i : n) (j : m)
  proof: Matrix.toLinearMap₂'Aux_single _ _ M i j

@[simp]

中文:
定理 矩阵.toLinearMap₂'_single
  条件: (M : 矩阵 n m N₂) (i : n) (j : m)
  证明: Matrix.toLinearMap₂'Aux_single _ _ M i j

@[simp]
-/
theorem Matrix.toLinearMap₂'_single (M : Matrix n m N₂) (i : n) (j : m) :
    Matrix.toLinearMap₂' R M (Pi.single i 1) (Pi.single j 1) = M i j :=
  Matrix.toLinearMap₂'Aux_single _ _ M i j

@[simp]
/--
theorem `LinearMap.toMatrixₛₗ₂'_symm` / 定理 `LinearMap.toMatrixₛₗ₂'_symm`

English:
theorem LinearMap.toMatrixₛₗ₂'_symm
  proof: rfl

@[simp]

中文:
定理 线性映射.toMatrixₛₗ₂'_symm
  证明: rfl

@[simp]
-/
theorem LinearMap.toMatrixₛₗ₂'_symm :
    ((LinearMap.toMatrixₛₗ₂' R).symm : Matrix n m N₂ ≃ₗ[R] _) = Matrix.toLinearMapₛₗ₂' R σ₁ σ₂ :=
  rfl

@[simp]
/--
theorem `Matrix.toLinearMapₛₗ₂'_symm` / 定理 `Matrix.toLinearMapₛₗ₂'_symm`

English:
theorem Matrix.toLinearMapₛₗ₂'_symm
  proof: (LinearMap.toMatrixₛₗ₂' R).symm_symm

@[simp]

中文:
定理 矩阵.toLinearMapₛₗ₂'_symm
  证明: (LinearMap.toMatrixₛₗ₂' R).symm_symm

@[simp]
-/
theorem Matrix.toLinearMapₛₗ₂'_symm :
    ((Matrix.toLinearMapₛₗ₂' R σ₁ σ₂).symm : _ ≃ₗ[R] Matrix n m N₂) = LinearMap.toMatrixₛₗ₂' R :=
  (LinearMap.toMatrixₛₗ₂' R).symm_symm

@[simp]
/--
theorem `Matrix.toLinearMapₛₗ₂'_toMatrix'` / 定理 `Matrix.toLinearMapₛₗ₂'_toMatrix'`

English:
theorem Matrix.toLinearMapₛₗ₂'_toMatrix'
  given: (B : (n -> R₁) ->ₛₗ[σ₁] (m -> R₂) ->ₛₗ[σ₂] N₂)
  proof: (Matrix.toLinearMapₛₗ₂' R σ₁ σ₂).apply_symm_apply B

@[simp]

中文:
定理 矩阵.toLinearMapₛₗ₂'_toMatrix'
  条件: (B : (n -> R₁) ->ₛₗ[σ₁] (m -> R₂) ->ₛₗ[σ₂] N₂)
  证明: (Matrix.toLinearMapₛₗ₂' R σ₁ σ₂).apply_symm_apply B

@[simp]
-/
theorem Matrix.toLinearMapₛₗ₂'_toMatrix' (B : (n -> R₁) ->ₛₗ[σ₁] (m -> R₂) ->ₛₗ[σ₂] N₂) :
    Matrix.toLinearMapₛₗ₂' R σ₁ σ₂ (LinearMap.toMatrixₛₗ₂' R B) = B :=
  (Matrix.toLinearMapₛₗ₂' R σ₁ σ₂).apply_symm_apply B

@[simp]
/--
theorem `Matrix.toLinearMap₂'_toMatrix'` / 定理 `Matrix.toLinearMap₂'_toMatrix'`

English:
theorem Matrix.toLinearMap₂'_toMatrix'
  given: (B : (n -> S₁) ->ₗ[S₁] (m -> S₂) ->ₗ[S₂] N₂)
  proof: (Matrix.toLinearMap₂' R).apply_symm_apply B

@[simp]

中文:
定理 矩阵.toLinearMap₂'_toMatrix'
  条件: (B : (n -> S₁) ->ₗ[S₁] (m -> S₂) ->ₗ[S₂] N₂)
  证明: (Matrix.toLinearMap₂' R).apply_symm_apply B

@[simp]
-/
theorem Matrix.toLinearMap₂'_toMatrix' (B : (n -> S₁) ->ₗ[S₁] (m -> S₂) ->ₗ[S₂] N₂) :
    Matrix.toLinearMap₂' R (LinearMap.toMatrix₂' R B) = B :=
  (Matrix.toLinearMap₂' R).apply_symm_apply B

@[simp]
/--
theorem `LinearMap.toMatrix'_toLinearMapₛₗ₂'` / 定理 `LinearMap.toMatrix'_toLinearMapₛₗ₂'`

English:
theorem LinearMap.toMatrix'_toLinearMapₛₗ₂'
  given: (M : Matrix n m N₂)
  proof: (LinearMap.toMatrixₛₗ₂' R).apply_symm_apply M

@[simp]

中文:
定理 线性映射.toMatrix'_toLinearMapₛₗ₂'
  条件: (M : 矩阵 n m N₂)
  证明: (LinearMap.toMatrixₛₗ₂' R).apply_symm_apply M

@[simp]
-/
theorem LinearMap.toMatrix'_toLinearMapₛₗ₂' (M : Matrix n m N₂) :
    LinearMap.toMatrixₛₗ₂' R (Matrix.toLinearMapₛₗ₂' R σ₁ σ₂ M) = M :=
  (LinearMap.toMatrixₛₗ₂' R).apply_symm_apply M

@[simp]
/--
theorem `LinearMap.toMatrix'_toLinearMap₂'` / 定理 `LinearMap.toMatrix'_toLinearMap₂'`

English:
theorem LinearMap.toMatrix'_toLinearMap₂'
  given: (M : Matrix n m N₂)
  proof: (LinearMap.toMatrixₛₗ₂' R).apply_symm_apply M

@[simp]

中文:
定理 线性映射.toMatrix'_toLinearMap₂'
  条件: (M : 矩阵 n m N₂)
  证明: (LinearMap.toMatrixₛₗ₂' R).apply_symm_apply M

@[simp]
-/
theorem LinearMap.toMatrix'_toLinearMap₂' (M : Matrix n m N₂) :
    LinearMap.toMatrix₂' R (Matrix.toLinearMap₂' R (S₁ := S₁) (S₂ := S₂) M) = M :=
  (LinearMap.toMatrixₛₗ₂' R).apply_symm_apply M

@[simp]
/--
theorem `LinearMap.toMatrixₛₗ₂'_apply` / 定理 `LinearMap.toMatrixₛₗ₂'_apply`

English:
theorem LinearMap.toMatrixₛₗ₂'_apply
  given: (B : (n -> R₁) ->ₛₗ[σ₁] (m -> R₂) ->ₛₗ[σ₂] N₂) (i : n) (j : m)
  proof: rfl

@[simp]

中文:
定理 线性映射.toMatrixₛₗ₂'_apply
  条件: (B : (n -> R₁) ->ₛₗ[σ₁] (m -> R₂) ->ₛₗ[σ₂] N₂) (i : n) (j : m)
  证明: rfl

@[simp]
-/
theorem LinearMap.toMatrixₛₗ₂'_apply (B : (n -> R₁) ->ₛₗ[σ₁] (m -> R₂) ->ₛₗ[σ₂] N₂) (i : n) (j : m) :
    LinearMap.toMatrixₛₗ₂' R B i j = B (Pi.single i 1) (Pi.single j 1) :=
  rfl

@[simp]
/--
theorem `LinearMap.toMatrix₂'_apply` / 定理 `LinearMap.toMatrix₂'_apply`

English:
theorem LinearMap.toMatrix₂'_apply
  given: (B : (n -> S₁) ->ₗ[S₁] (m -> S₂) ->ₗ[S₂] N₂) (i : n) (j : m)
  proof: rfl

中文:
定理 线性映射.toMatrix₂'_apply
  条件: (B : (n -> S₁) ->ₗ[S₁] (m -> S₂) ->ₗ[S₂] N₂) (i : n) (j : m)
  证明: rfl
-/
theorem LinearMap.toMatrix₂'_apply (B : (n -> S₁) ->ₗ[S₁] (m -> S₂) ->ₗ[S₂] N₂) (i : n) (j : m) :
    LinearMap.toMatrix₂' R B i j = B (Pi.single i 1) (Pi.single j 1) :=
  rfl

end ToMatrix'

section CommToMatrix'

-- TODO: Introduce matrix multiplication by matrices of scalars

variable {R : Type*} [CommSemiring R]
variable [Fintype n] [Fintype m]
variable [DecidableEq n] [DecidableEq m]
variable [Fintype n'] [Fintype m']
variable [DecidableEq n'] [DecidableEq m']

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `LinearMap.toMatrix₂'_compl₁₂` / 定理 `LinearMap.toMatrix₂'_compl₁₂`

English:
theorem LinearMap.toMatrix₂'_compl₁₂
  statement: (B : (n -> R) ->ₗ[R] (m -> R) ->ₗ[R] R) (l : (n' -> R) ->ₗ[R] n -> R)
  proof: by
  ext i j
  simp only [LinearMap.toMatrix₂'_apply, LinearMap.compl₁₂_apply, transpose_apply, Matrix.mul_apply,
    LinearMap.toMatrix', LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, sum_mul]
  rw [sum_comm]
  conv_lhs => rw [← LinearMap.sum_repr_mul_repr_mul (Pi.basisFun R n) (Pi.basisFun R m) (l _) (r _)]
  rw [Finsupp.sum_fintype]
  · apply sum_congr rfl
    rintro i' -
    rw [Finsupp.sum_fintype]
    · apply sum_congr rfl
      rintro j' -
      simp only [smul_eq_mul, Pi.basisFun_repr, mul_assoc, mul_comm, mul_left_comm,
        Pi.basisFun_apply, of_apply]
    · intros
      simp only [zero_smul, smul_zero]
  · intros
    simp

中文:
定理 线性映射.toMatrix₂'_compl₁₂
  结论: (B : (n -> R) ->ₗ[R] (m -> R) ->ₗ[R] R) (l : (n' -> R) ->ₗ[R] n -> R)
  证明: by
  ext i j
  simp only [LinearMap.toMatrix₂'_apply, LinearMap.compl₁₂_apply, transpose_apply, Matrix.mul_apply,
    LinearMap.toMatrix', LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, sum_mul]
  rw [sum_comm]
  conv_lhs => rw [← LinearMap.sum_repr_mul_repr_mul (Pi.basisFun R n) (Pi.basisFun R m) (l _) (r _)]
  rw [Finsupp.sum_fintype]
  · apply sum_congr rfl
    rintro i' -
    rw [Finsupp.sum_fintype]
    · apply sum_congr rfl
      rintro j' -
      simp only [smul_eq_mul, Pi.basisFun_repr, mul_assoc, mul_comm, mul_left_comm,
        Pi.basisFun_apply, of_apply]
    · intros
      simp only [zero_smul, smul_zero]
  · intros
    simp
-/
theorem LinearMap.toMatrix₂'_compl₁₂ (B : (n -> R) ->ₗ[R] (m -> R) ->ₗ[R] R) (l : (n' -> R) ->ₗ[R] n -> R)
    (r : (m' -> R) ->ₗ[R] m -> R) :
    toMatrix₂' R (B.compl₁₂ l r) = (toMatrix' l)ᵀ * toMatrix₂' R B * toMatrix' r := by
  ext i j
  simp only [LinearMap.toMatrix₂'_apply, LinearMap.compl₁₂_apply, transpose_apply, Matrix.mul_apply,
    LinearMap.toMatrix', LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, sum_mul]
  rw [sum_comm]
  conv_lhs => rw [← LinearMap.sum_repr_mul_repr_mul (Pi.basisFun R n) (Pi.basisFun R m) (l _) (r _)]
  rw [Finsupp.sum_fintype]
  · apply sum_congr rfl
    rintro i' -
    rw [Finsupp.sum_fintype]
    · apply sum_congr rfl
      rintro j' -
      simp only [smul_eq_mul, Pi.basisFun_repr, mul_assoc, mul_comm, mul_left_comm,
        Pi.basisFun_apply, of_apply]
    · intros
      simp only [zero_smul, smul_zero]
  · intros
    simp

/--
theorem `LinearMap.toMatrix₂'_comp` / 定理 `LinearMap.toMatrix₂'_comp`

English:
theorem LinearMap.toMatrix₂'_comp
  given: (B : (n -> R) ->ₗ[R] (m -> R) ->ₗ[R] R) (f : (n' -> R) ->ₗ[R] n -> R)
  proof: by
  rw [← LinearMap.compl₂_id (B.comp f)]; rw [← LinearMap.compl₁₂]
  simp

中文:
定理 线性映射.toMatrix₂'_comp
  条件: (B : (n -> R) ->ₗ[R] (m -> R) ->ₗ[R] R) (f : (n' -> R) ->ₗ[R] n -> R)
  证明: by
  rw [← LinearMap.compl₂_id (B.comp f)]; rw [← LinearMap.compl₁₂]
  simp
-/
theorem LinearMap.toMatrix₂'_comp (B : (n -> R) ->ₗ[R] (m -> R) ->ₗ[R] R) (f : (n' -> R) ->ₗ[R] n -> R) :
    toMatrix₂' R (B.comp f) = (toMatrix' f)ᵀ * toMatrix₂' R B := by
  rw [← LinearMap.compl₂_id (B.comp f)]; rw [← LinearMap.compl₁₂]
  simp

/--
theorem `LinearMap.toMatrix₂'_compl₂` / 定理 `LinearMap.toMatrix₂'_compl₂`

English:
theorem LinearMap.toMatrix₂'_compl₂
  given: (B : (n -> R) ->ₗ[R] (m -> R) ->ₗ[R] R) (f : (m' -> R) ->ₗ[R] m -> R)
  proof: by
  rw [← LinearMap.comp_id B]; rw [← LinearMap.compl₁₂]
  simp

中文:
定理 线性映射.toMatrix₂'_compl₂
  条件: (B : (n -> R) ->ₗ[R] (m -> R) ->ₗ[R] R) (f : (m' -> R) ->ₗ[R] m -> R)
  证明: by
  rw [← LinearMap.comp_id B]; rw [← LinearMap.compl₁₂]
  simp
-/
theorem LinearMap.toMatrix₂'_compl₂ (B : (n -> R) ->ₗ[R] (m -> R) ->ₗ[R] R) (f : (m' -> R) ->ₗ[R] m -> R) :
    toMatrix₂' R (B.compl₂ f) = toMatrix₂' R B * toMatrix' f := by
  rw [← LinearMap.comp_id B]; rw [← LinearMap.compl₁₂]
  simp

/--
theorem `LinearMap.mul_toMatrix₂'_mul` / 定理 `LinearMap.mul_toMatrix₂'_mul`

English:
theorem LinearMap.mul_toMatrix₂'_mul
  statement: (B : (n -> R) ->ₗ[R] (m -> R) ->ₗ[R] R) (M : Matrix n' n R)
  proof: by
  simp

中文:
定理 线性映射.mul_toMatrix₂'_mul
  结论: (B : (n -> R) ->ₗ[R] (m -> R) ->ₗ[R] R) (M : 矩阵 n' n R)
  证明: by
  simp
-/
theorem LinearMap.mul_toMatrix₂'_mul (B : (n -> R) ->ₗ[R] (m -> R) ->ₗ[R] R) (M : Matrix n' n R)
    (N : Matrix m m' R) :
    M * toMatrix₂' R B * N = toMatrix₂' R (B.compl₁₂ (toLin' Mᵀ) (toLin' N)) := by
  simp

/--
theorem `LinearMap.mul_toMatrix'` / 定理 `LinearMap.mul_toMatrix'`

English:
theorem LinearMap.mul_toMatrix'
  given: (B : (n -> R) ->ₗ[R] (m -> R) ->ₗ[R] R) (M : Matrix n' n R)
  proof: by
  simp only [B.toMatrix₂'_comp, transpose_transpose, toMatrix'_toLin']

中文:
定理 线性映射.mul_toMatrix'
  条件: (B : (n -> R) ->ₗ[R] (m -> R) ->ₗ[R] R) (M : 矩阵 n' n R)
  证明: by
  simp only [B.toMatrix₂'_comp, transpose_transpose, toMatrix'_toLin']

Depends on / 依赖: B.toMatrix, _comp, _toLin, toMatrix, transpose_transpose
-/
theorem LinearMap.mul_toMatrix' (B : (n -> R) ->ₗ[R] (m -> R) ->ₗ[R] R) (M : Matrix n' n R) :
    M * toMatrix₂' R B = toMatrix₂' R (B.comp <| toLin' Mᵀ) := by
  simp only [B.toMatrix₂'_comp, transpose_transpose, toMatrix'_toLin']

/--
theorem `LinearMap.toMatrix₂'_mul` / 定理 `LinearMap.toMatrix₂'_mul`

English:
theorem LinearMap.toMatrix₂'_mul
  given: (B : (n -> R) ->ₗ[R] (m -> R) ->ₗ[R] R) (M : Matrix m m' R)
  proof: by
  simp only [B.toMatrix₂'_compl₂, toMatrix'_toLin']

中文:
定理 线性映射.toMatrix₂'_mul
  条件: (B : (n -> R) ->ₗ[R] (m -> R) ->ₗ[R] R) (M : 矩阵 m m' R)
  证明: by
  simp only [B.toMatrix₂'_compl₂, toMatrix'_toLin']
-/
theorem LinearMap.toMatrix₂'_mul (B : (n -> R) ->ₗ[R] (m -> R) ->ₗ[R] R) (M : Matrix m m' R) :
    toMatrix₂' R B * M = toMatrix₂' R (B.compl₂ <| toLin' M) := by
  simp only [B.toMatrix₂'_compl₂, toMatrix'_toLin']

/--
theorem `Matrix.toLinearMap₂'_comp` / 定理 `Matrix.toLinearMap₂'_comp`

English:
theorem Matrix.toLinearMap₂'_comp
  given: (M : Matrix n m R) (P : Matrix n n' R) (Q : Matrix m m' R)
  proof: (LinearMap.toMatrix₂' R).injective (by simp)

中文:
定理 矩阵.toLinearMap₂'_comp
  条件: (M : 矩阵 n m R) (P : 矩阵 n n' R) (Q : 矩阵 m m' R)
  证明: (LinearMap.toMatrix₂' R).injective (by simp)
-/
theorem Matrix.toLinearMap₂'_comp (M : Matrix n m R) (P : Matrix n n' R) (Q : Matrix m m' R) :
    LinearMap.compl₁₂ (Matrix.toLinearMap₂' R M) (toLin' P) (toLin' Q) =
      toLinearMap₂' R (Pᵀ * M * Q) :=
  (LinearMap.toMatrix₂' R).injective (by simp)

end CommToMatrix'

section ToMatrix

/-! ### Bilinear maps over arbitrary vector spaces

This section deals with the conversion between matrices and bilinear maps on
a module with a fixed basis.
-/


variable [CommSemiring R]
variable [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂] [AddCommMonoid N₂]
  [Module R N₂]
variable {σ₁ : R ->+* R} {σ₂ : R ->+* R} [Fintype n] [Fintype m] [DecidableEq m] [DecidableEq n]

section

variable (b₁ : Basis n R M₁) (b₂ : Basis m R M₂)

/--
Definition of `LinearMap.toMatrix₂` / `LinearMap.toMatrix₂` 的定义

English:
definition LinearMap.toMatrix₂
  signature: : (M₁ ->ₛₗ[σ₁] M₂ ->ₛₗ[σ₂] N₂) ≃ₗ[R] Matrix n m N₂
  body: (b₁.equivFun.arrowCongr (b₂.equivFun.arrowCongr (LinearEquiv.refl R N₂))).trans
    (LinearMap.toMatrixₛₗ₂' R)

中文:
定义 线性映射.toMatrix₂
  签名: : (M₁ ->ₛₗ[σ₁] M₂ ->ₛₗ[σ₂] N₂) ≃ₗ[R] 矩阵 n m N₂
  定义体: (b₁.equivFun.arrowCongr (b₂.equivFun.arrowCongr (LinearEquiv.refl R N₂))).trans
    (LinearMap.toMatrixₛₗ₂' R)

Depends on / 依赖: LinearEquiv, LinearEquiv.refl, LinearMap, LinearMap.toMatrix, arrowCongr, equivFun, equivFun.arrowCongr
-/
noncomputable def LinearMap.toMatrix₂ : (M₁ ->ₛₗ[σ₁] M₂ ->ₛₗ[σ₂] N₂) ≃ₗ[R] Matrix n m N₂ :=
  (b₁.equivFun.arrowCongr (b₂.equivFun.arrowCongr (LinearEquiv.refl R N₂))).trans
    (LinearMap.toMatrixₛₗ₂' R)

variable (σ₁) in
/--
Definition of `Matrix.toLinearMapₛₗ₂` / `Matrix.toLinearMapₛₗ₂` 的定义

English:
definition Matrix.toLinearMapₛₗ₂
  signature: : Matrix n m N₂ ≃ₗ[R] M₁ ->ₛₗ[σ₁] M₂ ->ₗ[R] N₂
  body: (LinearMap.toMatrix₂ b₁ b₂).symm

中文:
定义 矩阵.toLinearMapₛₗ₂
  签名: : 矩阵 n m N₂ ≃ₗ[R] M₁ ->ₛₗ[σ₁] M₂ ->ₗ[R] N₂
  定义体: (LinearMap.toMatrix₂ b₁ b₂).symm

Depends on / 依赖: LinearMap, LinearMap.toMatrix
-/
noncomputable def Matrix.toLinearMapₛₗ₂ : Matrix n m N₂ ≃ₗ[R] M₁ ->ₛₗ[σ₁] M₂ ->ₗ[R] N₂ :=
  (LinearMap.toMatrix₂ b₁ b₂).symm

/--
Definition of `Matrix.toLinearMap₂` / `Matrix.toLinearMap₂` 的定义

English:
definition Matrix.toLinearMap₂
  signature: : Matrix n m N₂ ≃ₗ[R] M₁ ->ₗ[R] M₂ ->ₗ[R] N₂
  body: toLinearMapₛₗ₂ (.id R) b₁ b₂

中文:
定义 矩阵.toLinearMap₂
  签名: : 矩阵 n m N₂ ≃ₗ[R] M₁ ->ₗ[R] M₂ ->ₗ[R] N₂
  定义体: toLinearMapₛₗ₂ (.id R) b₁ b₂

Depends on / 依赖: AEMeasurable, infer_instance, map_of_not_aemeasurable, map_sum, sum_sfiniteSeq
-/
noncomputable def Matrix.toLinearMap₂ : Matrix n m N₂ ≃ₗ[R] M₁ ->ₗ[R] M₂ ->ₗ[R] N₂ :=
  toLinearMapₛₗ₂ (.id R) b₁ b₂

-- We make this and not `LinearMap.toMatrix₂` a `simp` lemma to avoid timeouts
@[simp]
/--
theorem `LinearMap.toMatrix₂_apply` / 定理 `LinearMap.toMatrix₂_apply`

English:
theorem LinearMap.toMatrix₂_apply
  given: (B : M₁ ->ₛₗ[σ₁] M₂ ->ₛₗ[σ₂] N₂) (i : n) (j : m)
  proof: by
  simp only [toMatrix₂, LinearEquiv.trans_apply, toMatrixₛₗ₂'_apply, LinearEquiv.arrowCongr_apply,
    Basis.equivFun_symm_apply, Pi.single_apply, ite_smul, one_smul, zero_smul, sum_ite_eq',
    mem_univ, ↓reduceIte, LinearEquiv.refl_apply]

@[simp]

中文:
定理 线性映射.toMatrix₂_apply
  条件: (B : M₁ ->ₛₗ[σ₁] M₂ ->ₛₗ[σ₂] N₂) (i : n) (j : m)
  证明: by
  simp only [toMatrix₂, LinearEquiv.trans_apply, toMatrixₛₗ₂'_apply, LinearEquiv.arrowCongr_apply,
    Basis.equivFun_symm_apply, Pi.single_apply, ite_smul, one_smul, zero_smul, sum_ite_eq',
    mem_univ, ↓reduceIte, LinearEquiv.refl_apply]

@[simp]

Depends on / 依赖: Basis.equivFun_symm_apply, LinearEquiv, LinearEquiv.arrowCongr_apply, LinearEquiv.refl_apply, LinearEquiv.trans_apply, Pi.single_apply, _apply, arrowCongr_apply, equivFun_symm_apply, ite_smul, mem_univ, one_smul, reduceIte, refl_apply, single_apply, sum_ite_eq, trans_apply, zero_smul
-/
theorem LinearMap.toMatrix₂_apply (B : M₁ ->ₛₗ[σ₁] M₂ ->ₛₗ[σ₂] N₂) (i : n) (j : m) :
    LinearMap.toMatrix₂ b₁ b₂ B i j = B (b₁ i) (b₂ j) := by
  simp only [toMatrix₂, LinearEquiv.trans_apply, toMatrixₛₗ₂'_apply, LinearEquiv.arrowCongr_apply,
    Basis.equivFun_symm_apply, Pi.single_apply, ite_smul, one_smul, zero_smul, sum_ite_eq',
    mem_univ, ↓reduceIte, LinearEquiv.refl_apply]

@[simp]
/--
theorem `Matrix.toLinearMapₛₗ₂_apply` / 定理 `Matrix.toLinearMapₛₗ₂_apply`

English:
theorem Matrix.toLinearMapₛₗ₂_apply
  given: (M : Matrix n m N₂) (x : M₁) (y : M₂)
  proof: Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    smul_algebra_smul_comm (σ₁ ((Basis.equivFun b₁) x _))
    ((RingHom.id R) ((Basis.equivFun b₂) y _)) (M _ _)

@[simp]

中文:
定理 矩阵.toLinearMapₛₗ₂_apply
  条件: (M : 矩阵 n m N₂) (x : M₁) (y : M₂)
  证明: Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    smul_algebra_smul_comm (σ₁ ((Basis.equivFun b₁) x _))
    ((RingHom.id R) ((Basis.equivFun b₂) y _)) (M _ _)

@[simp]

Depends on / 依赖: Basis.equivFun, Finset, Finset.sum_congr, RingHom, RingHom.id, equivFun, smul_algebra_smul_comm, sum_congr
-/
theorem Matrix.toLinearMapₛₗ₂_apply (M : Matrix n m N₂) (x : M₁) (y : M₂) :
    Matrix.toLinearMapₛₗ₂ σ₁ b₁ b₂ M x y =
      ∑ i, ∑ j, σ₁ (b₁.repr x i) • b₂.repr y j • M i j :=
  Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    smul_algebra_smul_comm (σ₁ ((Basis.equivFun b₁) x _))
    ((RingHom.id R) ((Basis.equivFun b₂) y _)) (M _ _)

@[simp]
/--
theorem `Matrix.toLinearMap₂_apply` / 定理 `Matrix.toLinearMap₂_apply`

English:
theorem Matrix.toLinearMap₂_apply
  given: (M : Matrix n m N₂) (x : M₁) (y : M₂)
  proof: Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    smul_algebra_smul_comm ((RingHom.id R) ((Basis.equivFun b₁) x _))
    ((RingHom.id R) ((Basis.equivFun b₂) y _)) (M _ _)

中文:
定理 矩阵.toLinearMap₂_apply
  条件: (M : 矩阵 n m N₂) (x : M₁) (y : M₂)
  证明: Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    smul_algebra_smul_comm ((RingHom.id R) ((Basis.equivFun b₁) x _))
    ((RingHom.id R) ((Basis.equivFun b₂) y _)) (M _ _)

Depends on / 依赖: Basis.equivFun, Finset, Finset.sum_congr, RingHom, RingHom.id, equivFun, smul_algebra_smul_comm, sum_congr
-/
theorem Matrix.toLinearMap₂_apply (M : Matrix n m N₂) (x : M₁) (y : M₂) :
    Matrix.toLinearMap₂ b₁ b₂ M x y =
      ∑ i, ∑ j, b₁.repr x i • b₂.repr y j • M i j :=
  Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    smul_algebra_smul_comm ((RingHom.id R) ((Basis.equivFun b₁) x _))
    ((RingHom.id R) ((Basis.equivFun b₂) y _)) (M _ _)

/--
theorem `Matrix.toLinearMapₛₗ₂_apply_basis` / 定理 `Matrix.toLinearMapₛₗ₂_apply_basis`

English:
theorem Matrix.toLinearMapₛₗ₂_apply_basis
  given: (M : Matrix n m N₂) (i : n) (j : m)
  proof: by
  simp only [toLinearMapₛₗ₂_apply, Basis.repr_self]
  rw [Finset.sum_eq_single_of_mem i (by simp) fun k _ hk => by simp [hk],
    Finset.sum_eq_single_of_mem j (by simp) fun k _ hk => by simp [hk]]
  simp

中文:
定理 矩阵.toLinearMapₛₗ₂_apply_basis
  条件: (M : 矩阵 n m N₂) (i : n) (j : m)
  证明: by
  simp only [toLinearMapₛₗ₂_apply, Basis.repr_self]
  rw [Finset.sum_eq_single_of_mem i (by simp) fun k _ hk => by simp [hk],
    Finset.sum_eq_single_of_mem j (by simp) fun k _ hk => by simp [hk]]
  simp

Depends on / 依赖: Basis.repr_self, Finset, Finset.sum_eq_single_of_mem, repr_self, sum_eq_single_of_mem
-/
theorem Matrix.toLinearMapₛₗ₂_apply_basis (M : Matrix n m N₂) (i : n) (j : m) :
    Matrix.toLinearMapₛₗ₂ σ₁ b₁ b₂ M (b₁ i) (b₂ j) = M i j := by
  simp only [toLinearMapₛₗ₂_apply, Basis.repr_self]
  rw [Finset.sum_eq_single_of_mem i (by simp) fun k _ hk => by simp [hk],
    Finset.sum_eq_single_of_mem j (by simp) fun k _ hk => by simp [hk]]
  simp

/--
theorem `Matrix.toLinearMap₂_apply_basis` / 定理 `Matrix.toLinearMap₂_apply_basis`

English:
theorem Matrix.toLinearMap₂_apply_basis
  given: (M : Matrix n m N₂) (i : n) (j : m)
  proof: toLinearMapₛₗ₂_apply_basis ..

中文:
定理 矩阵.toLinearMap₂_apply_basis
  条件: (M : 矩阵 n m N₂) (i : n) (j : m)
  证明: toLinearMapₛₗ₂_apply_basis ..
-/
theorem Matrix.toLinearMap₂_apply_basis (M : Matrix n m N₂) (i : n) (j : m) :
    Matrix.toLinearMap₂ b₁ b₂ M (b₁ i) (b₂ j) = M i j :=
  toLinearMapₛₗ₂_apply_basis ..

/--
theorem `dotProduct_toMatrix₂_mulVec` / 定理 `dotProduct_toMatrix₂_mulVec`

English:
theorem dotProduct_toMatrix₂_mulVec
  given: (B : M₁ ->ₛₗ[σ₁] M₂ ->ₛₗ[σ₂] R) (x : n -> R) (y : m -> R)
  proof: by
  simp only [dotProduct, Function.comp_apply, Function.comp_def, mulVec_eq_sum, op_smul_eq_smul,
    Finset.sum_apply, Pi.smul_apply, transpose_apply, toMatrix₂_apply, smul_eq_mul, mul_sum,
    Basis.equivFun_symm_apply, map_sum, map_smulₛₗ, coe_sum, LinearMap.smul_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl fun j _ => ?_)
  ring

中文:
定理 dotProduct_toMatrix₂_mulVec
  条件: (B : M₁ ->ₛₗ[σ₁] M₂ ->ₛₗ[σ₂] R) (x : n -> R) (y : m -> R)
  证明: by
  simp only [dotProduct, Function.comp_apply, Function.comp_def, mulVec_eq_sum, op_smul_eq_smul,
    Finset.sum_apply, Pi.smul_apply, transpose_apply, toMatrix₂_apply, smul_eq_mul, mul_sum,
    Basis.equivFun_symm_apply, map_sum, map_smulₛₗ, coe_sum, LinearMap.smul_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl fun j _ => ?_)
  ring

Depends on / 依赖: Basis.equivFun_symm_apply, Finset, Finset.sum_apply, Finset.sum_comm, Finset.sum_congr, Function, Function.comp_apply, Function.comp_def, LinearMap, LinearMap.smul_apply, Pi.smul_apply, coe_sum, comp_apply, comp_def, dotProduct, equivFun_symm_apply, map_sum, mulVec_eq_sum, mul_sum, op_smul_eq_smul
-/
theorem dotProduct_toMatrix₂_mulVec (B : M₁ ->ₛₗ[σ₁] M₂ ->ₛₗ[σ₂] R) (x : n -> R) (y : m -> R) :
    (σ₁ ∘ x) ⬝ᵥ (toMatrix₂ b₁ b₂ B) *ᵥ (σ₂ ∘ y) =
      B (b₁.equivFun.symm x) (b₂.equivFun.symm y) := by
  simp only [dotProduct, Function.comp_apply, Function.comp_def, mulVec_eq_sum, op_smul_eq_smul,
    Finset.sum_apply, Pi.smul_apply, transpose_apply, toMatrix₂_apply, smul_eq_mul, mul_sum,
    Basis.equivFun_symm_apply, map_sum, map_smulₛₗ, coe_sum, LinearMap.smul_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl fun j _ => ?_)
  ring

/--
lemma `apply_eq_dotProduct_toMatrix₂_mulVec` / 引理 `apply_eq_dotProduct_toMatrix₂_mulVec`

English:
lemma apply_eq_dotProduct_toMatrix₂_mulVec
  given: (B : M₁ ->ₛₗ[σ₁] M₂ ->ₛₗ[σ₂] R) (x : M₁) (y : M₂)
  proof: by
  nth_rw 1 [← b₁.sum_repr x, ← b₂.sum_repr y]
  suffices ∑ j, ∑ i, σ₂ (b₂.repr y j) * σ₁ (b₁.repr x i) * B (b₁ i) (b₂ j) =
           ∑ i, ∑ j, σ₁ (b₁.repr x i) * σ₂ (b₂.repr y j) * B (b₁ i) (b₂ j) by
    simpa [dotProduct, Matrix.mulVec_eq_sum, Finset.mul_sum, -Basis.sum_repr, ← mul_assoc]
  simp_rw [mul_comm (σ₂ _)]
  exact Finset.sum_comm

中文:
引理 apply_eq_dotProduct_toMatrix₂_mulVec
  条件: (B : M₁ ->ₛₗ[σ₁] M₂ ->ₛₗ[σ₂] R) (x : M₁) (y : M₂)
  证明: by
  nth_rw 1 [← b₁.sum_repr x, ← b₂.sum_repr y]
  suffices ∑ j, ∑ i, σ₂ (b₂.repr y j) * σ₁ (b₁.repr x i) * B (b₁ i) (b₂ j) =
           ∑ i, ∑ j, σ₁ (b₁.repr x i) * σ₂ (b₂.repr y j) * B (b₁ i) (b₂ j) by
    simpa [dotProduct, Matrix.mulVec_eq_sum, Finset.mul_sum, -Basis.sum_repr, ← mul_assoc]
  simp_rw [mul_comm (σ₂ _)]
  exact Finset.sum_comm

Depends on / 依赖: Basis.sum_repr, Finset, Finset.mul_sum, Finset.sum_comm, Matrix, Matrix.mulVec_eq_sum, dotProduct, mulVec_eq_sum, mul_assoc, mul_comm, mul_sum, nth_rw, simp_rw, sum_comm, sum_repr
-/
lemma apply_eq_dotProduct_toMatrix₂_mulVec (B : M₁ ->ₛₗ[σ₁] M₂ ->ₛₗ[σ₂] R) (x : M₁) (y : M₂) :
    B x y = (σ₁ ∘ b₁.repr x) ⬝ᵥ (toMatrix₂ b₁ b₂ B) *ᵥ (σ₂ ∘ b₂.repr y) := by
  nth_rw 1 [← b₁.sum_repr x, ← b₂.sum_repr y]
  suffices ∑ j, ∑ i, σ₂ (b₂.repr y j) * σ₁ (b₁.repr x i) * B (b₁ i) (b₂ j) =
           ∑ i, ∑ j, σ₁ (b₁.repr x i) * σ₂ (b₂.repr y j) * B (b₁ i) (b₂ j) by
    simpa [dotProduct, Matrix.mulVec_eq_sum, Finset.mul_sum, -Basis.sum_repr, ← mul_assoc]
  simp_rw [mul_comm (σ₂ _)]
  exact Finset.sum_comm

-- Not a `simp` lemma since `LinearMap.toMatrix₂` needs an extra argument
/--
theorem `LinearMap.toMatrix₂Aux_eq` / 定理 `LinearMap.toMatrix₂Aux_eq`

English:
theorem LinearMap.toMatrix₂Aux_eq
  given: (B : M₁ ->ₛₗ[σ₁] M₂ ->ₛₗ[σ₂] N₂)
  proof: Matrix.ext fun i j => by rw [LinearMap.toMatrix₂_apply, LinearMap.toMatrix₂Aux_apply]

@[simp]

中文:
定理 线性映射.toMatrix₂Aux_eq
  条件: (B : M₁ ->ₛₗ[σ₁] M₂ ->ₛₗ[σ₂] N₂)
  证明: Matrix.ext fun i j => by rw [LinearMap.toMatrix₂_apply, LinearMap.toMatrix₂Aux_apply]

@[simp]

Depends on / 依赖: LinearMap, LinearMap.toMatrix, Matrix, Matrix.ext
-/
theorem LinearMap.toMatrix₂Aux_eq (B : M₁ ->ₛₗ[σ₁] M₂ ->ₛₗ[σ₂] N₂) :
    LinearMap.toMatrix₂Aux R b₁ b₂ B = LinearMap.toMatrix₂ b₁ b₂ B :=
  Matrix.ext fun i j => by rw [LinearMap.toMatrix₂_apply, LinearMap.toMatrix₂Aux_apply]

@[simp]
/--
theorem `LinearMap.toMatrix₂_symm'` / 定理 `LinearMap.toMatrix₂_symm'`

English:
theorem LinearMap.toMatrix₂_symm'
  proof: rfl

中文:
定理 线性映射.toMatrix₂_symm'
  证明: rfl
-/
theorem LinearMap.toMatrix₂_symm' :
    (LinearMap.toMatrix₂ b₁ b₂).symm = Matrix.toLinearMapₛₗ₂ σ₁ (N₂ := N₂) b₁ b₂ :=
  rfl

/--
theorem `LinearMap.toMatrix₂_symm` / 定理 `LinearMap.toMatrix₂_symm`

English:
theorem LinearMap.toMatrix₂_symm
  proof: rfl

@[simp]

中文:
定理 线性映射.toMatrix₂_symm
  证明: rfl

@[simp]
-/
theorem LinearMap.toMatrix₂_symm :
    (LinearMap.toMatrix₂ b₁ b₂).symm = Matrix.toLinearMap₂ (N₂ := N₂) b₁ b₂ :=
  rfl

@[simp]
/--
theorem `Matrix.toLinearMapₛₗ₂_symm` / 定理 `Matrix.toLinearMapₛₗ₂_symm`

English:
theorem Matrix.toLinearMapₛₗ₂_symm
  proof: (LinearMap.toMatrix₂ b₁ b₂).symm_symm

中文:
定理 矩阵.toLinearMapₛₗ₂_symm
  证明: (LinearMap.toMatrix₂ b₁ b₂).symm_symm
-/
theorem Matrix.toLinearMapₛₗ₂_symm :
    (Matrix.toLinearMapₛₗ₂ σ₁ b₁ b₂).symm = LinearMap.toMatrix₂ (N₂ := N₂) b₁ b₂ :=
  (LinearMap.toMatrix₂ b₁ b₂).symm_symm

/--
theorem `Matrix.toLinearMap₂_symm` / 定理 `Matrix.toLinearMap₂_symm`

English:
theorem Matrix.toLinearMap₂_symm
  proof: (LinearMap.toMatrix₂ b₁ b₂).symm_symm

中文:
定理 矩阵.toLinearMap₂_symm
  证明: (LinearMap.toMatrix₂ b₁ b₂).symm_symm
-/
theorem Matrix.toLinearMap₂_symm :
    (Matrix.toLinearMap₂ b₁ b₂).symm = LinearMap.toMatrix₂ (N₂ := N₂) b₁ b₂ :=
  (LinearMap.toMatrix₂ b₁ b₂).symm_symm

/--
theorem `Matrix.toLinearMap₂_basisFun` / 定理 `Matrix.toLinearMap₂_basisFun`

English:
theorem Matrix.toLinearMap₂_basisFun
  proof: by
  ext M
  simp only [coe_comp, coe_single, Function.comp_apply, toLinearMap₂_apply, Pi.basisFun_repr,
    toLinearMap₂'_apply]

中文:
定理 矩阵.toLinearMap₂_basisFun
  证明: by
  ext M
  simp only [coe_comp, coe_single, Function.comp_apply, toLinearMap₂_apply, Pi.basisFun_repr,
    toLinearMap₂'_apply]

Depends on / 依赖: Function, Function.comp_apply, Pi.basisFun_repr, _apply, basisFun_repr, coe_comp, coe_single, comp_apply
-/
theorem Matrix.toLinearMap₂_basisFun :
    Matrix.toLinearMap₂ (Pi.basisFun R n) (Pi.basisFun R m) =
      Matrix.toLinearMap₂' R (N₂ := N₂) := by
  ext M
  simp only [coe_comp, coe_single, Function.comp_apply, toLinearMap₂_apply, Pi.basisFun_repr,
    toLinearMap₂'_apply]

/--
theorem `LinearMap.toMatrix₂_basisFun` / 定理 `LinearMap.toMatrix₂_basisFun`

English:
theorem LinearMap.toMatrix₂_basisFun
  proof: by
  ext B
  rw [LinearMap.toMatrix₂_apply]; rw [LinearMap.toMatrix₂'_apply]; rw [Pi.basisFun_apply]; rw [Pi.basisFun_apply]

@[simp]

中文:
定理 线性映射.toMatrix₂_basisFun
  证明: by
  ext B
  rw [LinearMap.toMatrix₂_apply]; rw [LinearMap.toMatrix₂'_apply]; rw [Pi.basisFun_apply]; rw [Pi.basisFun_apply]

@[simp]

Depends on / 依赖: LinearMap, LinearMap.toMatrix, Pi.basisFun_apply, _apply, basisFun_apply
-/
theorem LinearMap.toMatrix₂_basisFun :
    LinearMap.toMatrix₂ (Pi.basisFun R n) (Pi.basisFun R m) =
    LinearMap.toMatrix₂' R (N₂ := N₂) := by
  ext B
  rw [LinearMap.toMatrix₂_apply]; rw [LinearMap.toMatrix₂'_apply]; rw [Pi.basisFun_apply]; rw [Pi.basisFun_apply]

@[simp]
/--
theorem `Matrix.toLinearMapₛₗ₂_toMatrix₂` / 定理 `Matrix.toLinearMapₛₗ₂_toMatrix₂`

English:
theorem Matrix.toLinearMapₛₗ₂_toMatrix₂
  given: (B : M₁ ->ₛₗ[σ₁] M₂ ->ₗ[R] N₂)
  proof: (Matrix.toLinearMapₛₗ₂ σ₁ b₁ b₂).apply_symm_apply B

中文:
定理 矩阵.toLinearMapₛₗ₂_toMatrix₂
  条件: (B : M₁ ->ₛₗ[σ₁] M₂ ->ₗ[R] N₂)
  证明: (Matrix.toLinearMapₛₗ₂ σ₁ b₁ b₂).apply_symm_apply B

Depends on / 依赖: Matrix, Matrix.toLinearMap, apply_symm_apply
-/
theorem Matrix.toLinearMapₛₗ₂_toMatrix₂ (B : M₁ ->ₛₗ[σ₁] M₂ ->ₗ[R] N₂) :
    Matrix.toLinearMapₛₗ₂ σ₁ b₁ b₂ (LinearMap.toMatrix₂ b₁ b₂ B) = B :=
  (Matrix.toLinearMapₛₗ₂ σ₁ b₁ b₂).apply_symm_apply B

/--
theorem `Matrix.toLinearMap₂_toMatrix₂` / 定理 `Matrix.toLinearMap₂_toMatrix₂`

English:
theorem Matrix.toLinearMap₂_toMatrix₂
  given: (B : M₁ ->ₗ[R] M₂ ->ₗ[R] N₂)
  proof: (Matrix.toLinearMap₂ b₁ b₂).apply_symm_apply B

@[simp]

中文:
定理 矩阵.toLinearMap₂_toMatrix₂
  条件: (B : M₁ ->ₗ[R] M₂ ->ₗ[R] N₂)
  证明: (Matrix.toLinearMap₂ b₁ b₂).apply_symm_apply B

@[simp]

Depends on / 依赖: Matrix, Matrix.toLinearMap, apply_symm_apply
-/
theorem Matrix.toLinearMap₂_toMatrix₂ (B : M₁ ->ₗ[R] M₂ ->ₗ[R] N₂) :
    Matrix.toLinearMap₂ b₁ b₂ (LinearMap.toMatrix₂ b₁ b₂ B) = B :=
  (Matrix.toLinearMap₂ b₁ b₂).apply_symm_apply B

@[simp]
/--
theorem `LinearMap.toMatrix₂_toLinearMapₛₗ₂` / 定理 `LinearMap.toMatrix₂_toLinearMapₛₗ₂`

English:
theorem LinearMap.toMatrix₂_toLinearMapₛₗ₂
  given: (M : Matrix n m N₂)
  proof: (LinearMap.toMatrix₂ b₁ b₂).apply_symm_apply M

中文:
定理 线性映射.toMatrix₂_toLinearMapₛₗ₂
  条件: (M : 矩阵 n m N₂)
  证明: (LinearMap.toMatrix₂ b₁ b₂).apply_symm_apply M

Depends on / 依赖: LinearMap, LinearMap.toMatrix, apply_symm_apply
-/
theorem LinearMap.toMatrix₂_toLinearMapₛₗ₂ (M : Matrix n m N₂) :
    LinearMap.toMatrix₂ b₁ b₂ (Matrix.toLinearMapₛₗ₂ σ₁ b₁ b₂ M) = M :=
  (LinearMap.toMatrix₂ b₁ b₂).apply_symm_apply M

/--
theorem `LinearMap.toMatrix₂_toLinearMap₂` / 定理 `LinearMap.toMatrix₂_toLinearMap₂`

English:
theorem LinearMap.toMatrix₂_toLinearMap₂
  given: (M : Matrix n m N₂)
  proof: (LinearMap.toMatrix₂ b₁ b₂).apply_symm_apply M

中文:
定理 线性映射.toMatrix₂_toLinearMap₂
  条件: (M : 矩阵 n m N₂)
  证明: (LinearMap.toMatrix₂ b₁ b₂).apply_symm_apply M

Depends on / 依赖: LinearMap, LinearMap.toMatrix, apply_symm_apply
-/
theorem LinearMap.toMatrix₂_toLinearMap₂ (M : Matrix n m N₂) :
    LinearMap.toMatrix₂ b₁ b₂ (Matrix.toLinearMap₂ b₁ b₂ M) = M :=
  (LinearMap.toMatrix₂ b₁ b₂).apply_symm_apply M

variable (b₁ : Basis n R M₁) (b₂ : Basis m R M₂)
variable [AddCommMonoid M₁'] [Module R M₁']
variable [AddCommMonoid M₂'] [Module R M₂']
variable (b₁' : Basis n' R M₁')
variable (b₂' : Basis m' R M₂')
variable [Fintype n'] [Fintype m']
variable [DecidableEq n'] [DecidableEq m']

-- Cannot be a `simp` lemma because `b₁` and `b₂` must be inferred.
/--
theorem `LinearMap.toMatrix₂_compl₁₂` / 定理 `LinearMap.toMatrix₂_compl₁₂`

English:
theorem LinearMap.toMatrix₂_compl₁₂
  statement: (B : M₁ ->ₗ[R] M₂ ->ₗ[R] R) (l : M₁' ->ₗ[R] M₁)
  proof: by
  ext i j
  simp only [LinearMap.toMatrix₂_apply, compl₁₂_apply, transpose_apply, Matrix.mul_apply,
    LinearMap.toMatrix_apply, sum_mul]
  rw [sum_comm]
  conv_lhs => rw [← LinearMap.sum_repr_mul_repr_mul b₁ b₂]
  rw [Finsupp.sum_fintype]
  · apply sum_congr rfl
    rintro i' -
    rw [Finsupp.sum_fintype]
    · apply sum_congr rfl
      rintro j' -
      simp only [smul_eq_mul, mul_assoc, mul_comm,
        mul_left_comm]
    · intros
      simp only [zero_smul, smul_zero]
  · intros
    simp

中文:
定理 线性映射.toMatrix₂_compl₁₂
  结论: (B : M₁ ->ₗ[R] M₂ ->ₗ[R] R) (l : M₁' ->ₗ[R] M₁)
  证明: by
  ext i j
  simp only [LinearMap.toMatrix₂_apply, compl₁₂_apply, transpose_apply, Matrix.mul_apply,
    LinearMap.toMatrix_apply, sum_mul]
  rw [sum_comm]
  conv_lhs => rw [← LinearMap.sum_repr_mul_repr_mul b₁ b₂]
  rw [Finsupp.sum_fintype]
  · apply sum_congr rfl
    rintro i' -
    rw [Finsupp.sum_fintype]
    · apply sum_congr rfl
      rintro j' -
      simp only [smul_eq_mul, mul_assoc, mul_comm,
        mul_left_comm]
    · intros
      simp only [zero_smul, smul_zero]
  · intros
    simp

Depends on / 依赖: Finsupp, Finsupp.sum_fintype, LinearMap, LinearMap.sum_repr_mul_repr_mul, LinearMap.toMatrix, LinearMap.toMatrix_apply, Matrix, Matrix.mul_apply, conv_lhs, intros, mul_apply, mul_assoc, mul_comm, mul_left_comm, smul_eq_mul, smul_zero, sum_comm, sum_congr, sum_fintype, sum_mul
-/
theorem LinearMap.toMatrix₂_compl₁₂ (B : M₁ ->ₗ[R] M₂ ->ₗ[R] R) (l : M₁' ->ₗ[R] M₁)
    (r : M₂' ->ₗ[R] M₂) :
    LinearMap.toMatrix₂ b₁' b₂' (B.compl₁₂ l r) =
      (toMatrix b₁' b₁ l)ᵀ * LinearMap.toMatrix₂ b₁ b₂ B * toMatrix b₂' b₂ r := by
  ext i j
  simp only [LinearMap.toMatrix₂_apply, compl₁₂_apply, transpose_apply, Matrix.mul_apply,
    LinearMap.toMatrix_apply, sum_mul]
  rw [sum_comm]
  conv_lhs => rw [← LinearMap.sum_repr_mul_repr_mul b₁ b₂]
  rw [Finsupp.sum_fintype]
  · apply sum_congr rfl
    rintro i' -
    rw [Finsupp.sum_fintype]
    · apply sum_congr rfl
      rintro j' -
      simp only [smul_eq_mul, mul_assoc, mul_comm,
        mul_left_comm]
    · intros
      simp only [zero_smul, smul_zero]
  · intros
    simp

/--
theorem `LinearMap.toMatrix₂_comp` / 定理 `LinearMap.toMatrix₂_comp`

English:
theorem LinearMap.toMatrix₂_comp
  given: (B : M₁ ->ₗ[R] M₂ ->ₗ[R] R) (f : M₁' ->ₗ[R] M₁)
  proof: by
  rw [← LinearMap.compl₂_id (B.comp f)]; rw [← LinearMap.compl₁₂]; rw [LinearMap.toMatrix₂_compl₁₂ b₁ b₂]
  simp

中文:
定理 线性映射.toMatrix₂_comp
  条件: (B : M₁ ->ₗ[R] M₂ ->ₗ[R] R) (f : M₁' ->ₗ[R] M₁)
  证明: by
  rw [← LinearMap.compl₂_id (B.comp f)]; rw [← LinearMap.compl₁₂]; rw [LinearMap.toMatrix₂_compl₁₂ b₁ b₂]
  simp

Depends on / 依赖: B.comp, LinearMap, LinearMap.compl, LinearMap.toMatrix
-/
theorem LinearMap.toMatrix₂_comp (B : M₁ ->ₗ[R] M₂ ->ₗ[R] R) (f : M₁' ->ₗ[R] M₁) :
    LinearMap.toMatrix₂ b₁' b₂ (B.comp f) =
      (toMatrix b₁' b₁ f)ᵀ * LinearMap.toMatrix₂ b₁ b₂ B := by
  rw [← LinearMap.compl₂_id (B.comp f)]; rw [← LinearMap.compl₁₂]; rw [LinearMap.toMatrix₂_compl₁₂ b₁ b₂]
  simp

/--
theorem `LinearMap.toMatrix₂_compl₂` / 定理 `LinearMap.toMatrix₂_compl₂`

English:
theorem LinearMap.toMatrix₂_compl₂
  given: (B : M₁ ->ₗ[R] M₂ ->ₗ[R] R) (f : M₂' ->ₗ[R] M₂)
  proof: by
  rw [← LinearMap.comp_id B]; rw [← LinearMap.compl₁₂]; rw [LinearMap.toMatrix₂_compl₁₂ b₁ b₂]
  simp

@[simp]

中文:
定理 线性映射.toMatrix₂_compl₂
  条件: (B : M₁ ->ₗ[R] M₂ ->ₗ[R] R) (f : M₂' ->ₗ[R] M₂)
  证明: by
  rw [← LinearMap.comp_id B]; rw [← LinearMap.compl₁₂]; rw [LinearMap.toMatrix₂_compl₁₂ b₁ b₂]
  simp

@[simp]

Depends on / 依赖: LinearMap, LinearMap.comp_id, LinearMap.compl, LinearMap.toMatrix, comp_id
-/
theorem LinearMap.toMatrix₂_compl₂ (B : M₁ ->ₗ[R] M₂ ->ₗ[R] R) (f : M₂' ->ₗ[R] M₂) :
    LinearMap.toMatrix₂ b₁ b₂' (B.compl₂ f) =
      LinearMap.toMatrix₂ b₁ b₂ B * toMatrix b₂' b₂ f := by
  rw [← LinearMap.comp_id B]; rw [← LinearMap.compl₁₂]; rw [LinearMap.toMatrix₂_compl₁₂ b₁ b₂]
  simp

@[simp]
/--
theorem `LinearMap.toMatrix₂_mul_basis_toMatrix` / 定理 `LinearMap.toMatrix₂_mul_basis_toMatrix`

English:
theorem LinearMap.toMatrix₂_mul_basis_toMatrix
  statement: (c₁ : Basis n' R M₁) (c₂ : Basis m' R M₂)
  proof: by
  simp_rw [← LinearMap.toMatrix_id_eq_basis_toMatrix]
  rw [← LinearMap.toMatrix₂_compl₁₂]; rw [LinearMap.compl₁₂_id_id]

中文:
定理 线性映射.toMatrix₂_mul_basis_toMatrix
  结论: (c₁ : 基 n' R M₁) (c₂ : 基 m' R M₂)
  证明: by
  simp_rw [← LinearMap.toMatrix_id_eq_basis_toMatrix]
  rw [← LinearMap.toMatrix₂_compl₁₂]; rw [LinearMap.compl₁₂_id_id]

Depends on / 依赖: LinearMap, LinearMap.compl, LinearMap.toMatrix, LinearMap.toMatrix_id_eq_basis_toMatrix, simp_rw, toMatrix_id_eq_basis_toMatrix
-/
theorem LinearMap.toMatrix₂_mul_basis_toMatrix (c₁ : Basis n' R M₁) (c₂ : Basis m' R M₂)
    (B : M₁ ->ₗ[R] M₂ ->ₗ[R] R) :
    (b₁.toMatrix c₁)ᵀ * LinearMap.toMatrix₂ b₁ b₂ B * b₂.toMatrix c₂ =
      LinearMap.toMatrix₂ c₁ c₂ B := by
  simp_rw [← LinearMap.toMatrix_id_eq_basis_toMatrix]
  rw [← LinearMap.toMatrix₂_compl₁₂]; rw [LinearMap.compl₁₂_id_id]

/--
theorem `LinearMap.mul_toMatrix₂_mul` / 定理 `LinearMap.mul_toMatrix₂_mul`

English:
theorem LinearMap.mul_toMatrix₂_mul
  statement: (B : M₁ ->ₗ[R] M₂ ->ₗ[R] R) (M : Matrix n' n R)
  proof: by
  simp_rw [LinearMap.toMatrix₂_compl₁₂ b₁ b₂, toMatrix_toLin, transpose_transpose]

中文:
定理 线性映射.mul_toMatrix₂_mul
  结论: (B : M₁ ->ₗ[R] M₂ ->ₗ[R] R) (M : 矩阵 n' n R)
  证明: by
  simp_rw [LinearMap.toMatrix₂_compl₁₂ b₁ b₂, toMatrix_toLin, transpose_transpose]

Depends on / 依赖: LinearMap, LinearMap.toMatrix, simp_rw, toMatrix_toLin, transpose_transpose
-/
theorem LinearMap.mul_toMatrix₂_mul (B : M₁ ->ₗ[R] M₂ ->ₗ[R] R) (M : Matrix n' n R)
    (N : Matrix m m' R) :
    M * LinearMap.toMatrix₂ b₁ b₂ B * N =
      LinearMap.toMatrix₂ b₁' b₂' (B.compl₁₂ (toLin b₁' b₁ Mᵀ) (toLin b₂' b₂ N)) := by
  simp_rw [LinearMap.toMatrix₂_compl₁₂ b₁ b₂, toMatrix_toLin, transpose_transpose]

/--
theorem `LinearMap.mul_toMatrix₂` / 定理 `LinearMap.mul_toMatrix₂`

English:
theorem LinearMap.mul_toMatrix₂
  given: (B : M₁ ->ₗ[R] M₂ ->ₗ[R] R) (M : Matrix n' n R)
  proof: by
  rw [LinearMap.toMatrix₂_comp b₁]; rw [toMatrix_toLin]; rw [transpose_transpose]

中文:
定理 线性映射.mul_toMatrix₂
  条件: (B : M₁ ->ₗ[R] M₂ ->ₗ[R] R) (M : 矩阵 n' n R)
  证明: by
  rw [LinearMap.toMatrix₂_comp b₁]; rw [toMatrix_toLin]; rw [transpose_transpose]

Depends on / 依赖: LinearMap, LinearMap.toMatrix, toMatrix_toLin, transpose_transpose
-/
theorem LinearMap.mul_toMatrix₂ (B : M₁ ->ₗ[R] M₂ ->ₗ[R] R) (M : Matrix n' n R) :
    M * LinearMap.toMatrix₂ b₁ b₂ B =
      LinearMap.toMatrix₂ b₁' b₂ (B.comp (toLin b₁' b₁ Mᵀ)) := by
  rw [LinearMap.toMatrix₂_comp b₁]; rw [toMatrix_toLin]; rw [transpose_transpose]

/--
theorem `LinearMap.toMatrix₂_mul` / 定理 `LinearMap.toMatrix₂_mul`

English:
theorem LinearMap.toMatrix₂_mul
  given: (B : M₁ ->ₗ[R] M₂ ->ₗ[R] R) (M : Matrix m m' R)
  proof: by
  rw [LinearMap.toMatrix₂_compl₂ b₁ b₂]; rw [toMatrix_toLin]

中文:
定理 线性映射.toMatrix₂_mul
  条件: (B : M₁ ->ₗ[R] M₂ ->ₗ[R] R) (M : 矩阵 m m' R)
  证明: by
  rw [LinearMap.toMatrix₂_compl₂ b₁ b₂]; rw [toMatrix_toLin]

Depends on / 依赖: LinearMap, LinearMap.toMatrix, toMatrix_toLin
-/
theorem LinearMap.toMatrix₂_mul (B : M₁ ->ₗ[R] M₂ ->ₗ[R] R) (M : Matrix m m' R) :
    LinearMap.toMatrix₂ b₁ b₂ B * M =
      LinearMap.toMatrix₂ b₁ b₂' (B.compl₂ (toLin b₂' b₂ M)) := by
  rw [LinearMap.toMatrix₂_compl₂ b₁ b₂]; rw [toMatrix_toLin]

/--
theorem `Matrix.toLinearMap₂_compl₁₂` / 定理 `Matrix.toLinearMap₂_compl₁₂`

English:
theorem Matrix.toLinearMap₂_compl₁₂
  given: (M : Matrix n m R) (P : Matrix n n' R) (Q : Matrix m m' R)
  proof: (LinearMap.toMatrix₂ b₁' b₂').injective
    (by
      simp only [LinearMap.toMatrix₂_compl₁₂ b₁ b₂, LinearMap.toMatrix₂_toLinearMap₂,
        toMatrix_toLin])

中文:
定理 矩阵.toLinearMap₂_compl₁₂
  条件: (M : 矩阵 n m R) (P : 矩阵 n n' R) (Q : 矩阵 m m' R)
  证明: (LinearMap.toMatrix₂ b₁' b₂').injective
    (by
      simp only [LinearMap.toMatrix₂_compl₁₂ b₁ b₂, LinearMap.toMatrix₂_toLinearMap₂,
        toMatrix_toLin])

Depends on / 依赖: LinearMap, LinearMap.toMatrix, injective, toMatrix_toLin
-/
theorem Matrix.toLinearMap₂_compl₁₂ (M : Matrix n m R) (P : Matrix n n' R) (Q : Matrix m m' R) :
    (Matrix.toLinearMap₂ b₁ b₂ M).compl₁₂ (toLin b₁' b₁ P) (toLin b₂' b₂ Q) =
      Matrix.toLinearMap₂ b₁' b₂' (Pᵀ * M * Q) :=
  (LinearMap.toMatrix₂ b₁' b₂').injective
    (by
      simp only [LinearMap.toMatrix₂_compl₁₂ b₁ b₂, LinearMap.toMatrix₂_toLinearMap₂,
        toMatrix_toLin])

end

end ToMatrix

/-! ### Adjoint pairs -/


section MatrixAdjoints

open Matrix

variable [CommRing R]
variable [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂]
variable [Fintype n] [Fintype n']
variable (b₁ : Basis n R M₁) (b₂ : Basis n' R M₂)
variable (J J₂ : Matrix n n R) (J' : Matrix n' n' R)
variable (A : Matrix n' n R) (A' : Matrix n n' R)
variable (A₁ A₂ : Matrix n n R)

/--
Definition of `Matrix.IsAdjointPair` / `Matrix.IsAdjointPair` 的定义

English:
definition Matrix.IsAdjointPair
  body: Aᵀ * J' = J * A'

中文:
定义 矩阵.IsAdjointPair
  定义体: Aᵀ * J' = J * A'
-/
def Matrix.IsAdjointPair :=
  Aᵀ * J' = J * A'

/--
Definition of `Matrix.IsSelfAdjoint` / `Matrix.IsSelfAdjoint` 的定义

English:
definition Matrix.IsSelfAdjoint
  body: Matrix.IsAdjointPair J J A₁ A₁

中文:
定义 矩阵.IsSelfAdjoint
  定义体: Matrix.IsAdjointPair J J A₁ A₁
-/
protected def Matrix.IsSelfAdjoint :=
  Matrix.IsAdjointPair J J A₁ A₁

/--
Definition of `Matrix.IsSkewAdjoint` / `Matrix.IsSkewAdjoint` 的定义

English:
definition Matrix.IsSkewAdjoint
  body: Matrix.IsAdjointPair J J A₁ (-A₁)

中文:
定义 矩阵.IsSkewAdjoint
  定义体: Matrix.IsAdjointPair J J A₁ (-A₁)
-/
protected def Matrix.IsSkewAdjoint :=
  Matrix.IsAdjointPair J J A₁ (-A₁)

variable [DecidableEq n] [DecidableEq n']

@[simp]
/--
theorem `isAdjointPair_toLinearMap₂'` / 定理 `isAdjointPair_toLinearMap₂'`

English:
theorem isAdjointPair_toLinearMap₂'
  proof: by
  rw [isAdjointPair_iff_comp_eq_compl₂]
  have h :
    forall B B' : (n -> R) ->ₗ[R] (n' -> R) ->ₗ[R] R,
      B = B' ↔ LinearMap.toMatrix₂' R B = LinearMap.toMatrix₂' R B' := by
    intro B B'
    constructor <;> intro h
    · rw [h]
    · exact (LinearMap.toMatrix₂' R).injective h
  simp_rw [h, LinearMap.toMatrix₂'_comp, LinearMap.toMatrix₂'_compl₂,
    LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_toLinearMap₂']
  rfl

@[simp]

中文:
定理 isAdjointPair_toLinearMap₂'
  证明: by
  rw [isAdjointPair_iff_comp_eq_compl₂]
  have h :
    forall B B' : (n -> R) ->ₗ[R] (n' -> R) ->ₗ[R] R,
      B = B' ↔ LinearMap.toMatrix₂' R B = LinearMap.toMatrix₂' R B' := by
    intro B B'
    constructor <;> intro h
    · rw [h]
    · exact (LinearMap.toMatrix₂' R).injective h
  simp_rw [h, LinearMap.toMatrix₂'_comp, LinearMap.toMatrix₂'_compl₂,
    LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_toLinearMap₂']
  rfl

@[simp]

Depends on / 依赖: LinearMap, LinearMap.toMatrix, _comp, _toLin, injective, simp_rw, toMatrix
-/
theorem isAdjointPair_toLinearMap₂' :
    LinearMap.IsAdjointPair (Matrix.toLinearMap₂' R J) (Matrix.toLinearMap₂' R J')
        (Matrix.toLin' A) (Matrix.toLin' A') ↔
      Matrix.IsAdjointPair J J' A A' := by
  rw [isAdjointPair_iff_comp_eq_compl₂]
  have h :
    forall B B' : (n -> R) ->ₗ[R] (n' -> R) ->ₗ[R] R,
      B = B' ↔ LinearMap.toMatrix₂' R B = LinearMap.toMatrix₂' R B' := by
    intro B B'
    constructor <;> intro h
    · rw [h]
    · exact (LinearMap.toMatrix₂' R).injective h
  simp_rw [h, LinearMap.toMatrix₂'_comp, LinearMap.toMatrix₂'_compl₂,
    LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_toLinearMap₂']
  rfl

@[simp]
/--
theorem `isAdjointPair_toLinearMap₂` / 定理 `isAdjointPair_toLinearMap₂`

English:
theorem isAdjointPair_toLinearMap₂
  proof: by
  rw [isAdjointPair_iff_comp_eq_compl₂]
  have h :
    forall B B' : M₁ ->ₗ[R] M₂ ->ₗ[R] R,
      B = B' ↔ LinearMap.toMatrix₂ b₁ b₂ B = LinearMap.toMatrix₂ b₁ b₂ B' := by
    intro B B'
    constructor <;> intro h
    · rw [h]
    · exact (LinearMap.toMatrix₂ b₁ b₂).injective h
  simp_rw [h, LinearMap.toMatrix₂_comp b₂ b₂, LinearMap.toMatrix₂_compl₂ b₁ b₁,
    LinearMap.toMatrix_toLin, LinearMap.toMatrix₂_toLinearMap₂]
  rfl

中文:
定理 isAdjointPair_toLinearMap₂
  证明: by
  rw [isAdjointPair_iff_comp_eq_compl₂]
  have h :
    forall B B' : M₁ ->ₗ[R] M₂ ->ₗ[R] R,
      B = B' ↔ LinearMap.toMatrix₂ b₁ b₂ B = LinearMap.toMatrix₂ b₁ b₂ B' := by
    intro B B'
    constructor <;> intro h
    · rw [h]
    · exact (LinearMap.toMatrix₂ b₁ b₂).injective h
  simp_rw [h, LinearMap.toMatrix₂_comp b₂ b₂, LinearMap.toMatrix₂_compl₂ b₁ b₁,
    LinearMap.toMatrix_toLin, LinearMap.toMatrix₂_toLinearMap₂]
  rfl

Depends on / 依赖: LinearMap, LinearMap.toMatrix, LinearMap.toMatrix_toLin, injective, simp_rw, toMatrix_toLin
-/
theorem isAdjointPair_toLinearMap₂ :
    LinearMap.IsAdjointPair (Matrix.toLinearMap₂ b₁ b₁ J)
      (Matrix.toLinearMap₂ b₂ b₂ J') (Matrix.toLin b₁ b₂ A) (Matrix.toLin b₂ b₁ A') ↔
      Matrix.IsAdjointPair J J' A A' := by
  rw [isAdjointPair_iff_comp_eq_compl₂]
  have h :
    forall B B' : M₁ ->ₗ[R] M₂ ->ₗ[R] R,
      B = B' ↔ LinearMap.toMatrix₂ b₁ b₂ B = LinearMap.toMatrix₂ b₁ b₂ B' := by
    intro B B'
    constructor <;> intro h
    · rw [h]
    · exact (LinearMap.toMatrix₂ b₁ b₂).injective h
  simp_rw [h, LinearMap.toMatrix₂_comp b₂ b₂, LinearMap.toMatrix₂_compl₂ b₁ b₁,
    LinearMap.toMatrix_toLin, LinearMap.toMatrix₂_toLinearMap₂]
  rfl

/--
theorem `Matrix.isAdjointPair_equiv` / 定理 `Matrix.isAdjointPair_equiv`

English:
theorem Matrix.isAdjointPair_equiv
  given: (P : Matrix n n R) (h : IsUnit P)
  proof: by
  have h' : IsUnit P.det := P.isUnit_iff_isUnit_det.mp h
  let u := P.nonsingInvUnit h'
  let v := Pᵀ.nonsingInvUnit (P.isUnit_det_transpose h')
  let x := A₁ᵀ * Pᵀ * J
  let y := J * P * A₂
  suffices x * u = v * y ↔ v⁻¹ * x = y * u⁻¹ by
    dsimp only [Matrix.IsAdjointPair]
    simp only [Matrix.transpose_mul]
    simp only [← mul_assoc, P.transpose_nonsing_inv]
    convert! this using 2
    · rw [mul_assoc, mul_assoc, ← mul_assoc J]
      rfl
    · rw [mul_assoc, mul_assoc, ← mul_assoc _ _ J]
      rfl
  rw [Units.eq_mul_inv_iff_mul_eq]
  conv_rhs => rw [mul_assoc]
  rw [v.inv_mul_eq_iff_eq_mul]

中文:
定理 矩阵.isAdjointPair_equiv
  条件: (P : 矩阵 n n R) (h : 是单位 P)
  证明: by
  have h' : IsUnit P.det := P.isUnit_iff_isUnit_det.mp h
  let u := P.nonsingInvUnit h'
  let v := Pᵀ.nonsingInvUnit (P.isUnit_det_transpose h')
  let x := A₁ᵀ * Pᵀ * J
  let y := J * P * A₂
  suffices x * u = v * y ↔ v⁻¹ * x = y * u⁻¹ by
    dsimp only [Matrix.IsAdjointPair]
    simp only [Matrix.transpose_mul]
    simp only [← mul_assoc, P.transpose_nonsing_inv]
    convert! this using 2
    · rw [mul_assoc, mul_assoc, ← mul_assoc J]
      rfl
    · rw [mul_assoc, mul_assoc, ← mul_assoc _ _ J]
      rfl
  rw [Units.eq_mul_inv_iff_mul_eq]
  conv_rhs => rw [mul_assoc]
  rw [v.inv_mul_eq_iff_eq_mul]

Depends on / 依赖: IsAdjointPair, IsUnit, Matrix, Matrix.IsAdjointPair, Matrix.transpose_mul, P.det, P.isUnit_det_transpose, P.isUnit_iff_isUnit_det.mp, P.nonsingInvUnit, P.transpose_nonsing_inv, Units.eq_mul_inv_iff_mul_eq, convert, eq_mul_inv_iff_mul_eq, isUnit_det_transpose, isUnit_iff_isUnit_det, mul_assoc, nonsingInvUnit, transpose_mul, transpose_nonsing_inv
-/
theorem Matrix.isAdjointPair_equiv (P : Matrix n n R) (h : IsUnit P) :
    (Pᵀ * J * P).IsAdjointPair (Pᵀ * J * P) A₁ A₂ ↔
      J.IsAdjointPair J (P * A₁ * P⁻¹) (P * A₂ * P⁻¹) := by
  have h' : IsUnit P.det := P.isUnit_iff_isUnit_det.mp h
  let u := P.nonsingInvUnit h'
  let v := Pᵀ.nonsingInvUnit (P.isUnit_det_transpose h')
  let x := A₁ᵀ * Pᵀ * J
  let y := J * P * A₂
  suffices x * u = v * y ↔ v⁻¹ * x = y * u⁻¹ by
    dsimp only [Matrix.IsAdjointPair]
    simp only [Matrix.transpose_mul]
    simp only [← mul_assoc, P.transpose_nonsing_inv]
    convert! this using 2
    · rw [mul_assoc, mul_assoc, ← mul_assoc J]
      rfl
    · rw [mul_assoc, mul_assoc, ← mul_assoc _ _ J]
      rfl
  rw [Units.eq_mul_inv_iff_mul_eq]
  conv_rhs => rw [mul_assoc]
  rw [v.inv_mul_eq_iff_eq_mul]

/--
Definition of `pairSelfAdjointMatricesSubmodule` / `pairSelfAdjointMatricesSubmodule` 的定义

English:
definition pairSelfAdjointMatricesSubmodule
  signature: : Submodule R (Matrix n n R)
  body: (isPairSelfAdjointSubmodule (Matrix.toLinearMap₂' R J)
    (Matrix.toLinearMap₂' R J₂)).map
    ((LinearMap.toMatrix' : ((n -> R) ->ₗ[R] n -> R) ≃ₗ[R] Matrix n n R) :
      ((n -> R) ->ₗ[R] n -> R) ->ₗ[R] Matrix n n R)

@[simp]

中文:
定义 pairSelfAdjointMatricesSubmodule
  签名: : 子模 R (矩阵 n n R)
  定义体: (isPairSelfAdjointSubmodule (Matrix.toLinearMap₂' R J)
    (Matrix.toLinearMap₂' R J₂)).map
    ((LinearMap.toMatrix' : ((n -> R) ->ₗ[R] n -> R) ≃ₗ[R] Matrix n n R) :
      ((n -> R) ->ₗ[R] n -> R) ->ₗ[R] Matrix n n R)

@[simp]

Depends on / 依赖: LinearMap, LinearMap.toMatrix, Matrix, Matrix.toLinearMap, isPairSelfAdjointSubmodule, toMatrix
-/
def pairSelfAdjointMatricesSubmodule : Submodule R (Matrix n n R) :=
  (isPairSelfAdjointSubmodule (Matrix.toLinearMap₂' R J)
    (Matrix.toLinearMap₂' R J₂)).map
    ((LinearMap.toMatrix' : ((n -> R) ->ₗ[R] n -> R) ≃ₗ[R] Matrix n n R) :
      ((n -> R) ->ₗ[R] n -> R) ->ₗ[R] Matrix n n R)

@[simp]
/--
theorem `mem_pairSelfAdjointMatricesSubmodule` / 定理 `mem_pairSelfAdjointMatricesSubmodule`

English:
theorem mem_pairSelfAdjointMatricesSubmodule
  proof: by
  simp only [pairSelfAdjointMatricesSubmodule, Submodule.mem_map_equiv,
    mem_isPairSelfAdjointSubmodule, toMatrix'_symm, ← isAdjointPair_toLinearMap₂',
    IsPairSelfAdjoint, toLin'_apply']

中文:
定理 mem_pairSelfAdjointMatricesSubmodule
  证明: by
  simp only [pairSelfAdjointMatricesSubmodule, Submodule.mem_map_equiv,
    mem_isPairSelfAdjointSubmodule, toMatrix'_symm, ← isAdjointPair_toLinearMap₂',
    IsPairSelfAdjoint, toLin'_apply']

Depends on / 依赖: IsPairSelfAdjoint, Submodule, Submodule.mem_map_equiv, _apply, _symm, mem_isPairSelfAdjointSubmodule, mem_map_equiv, pairSelfAdjointMatricesSubmodule, toMatrix
-/
theorem mem_pairSelfAdjointMatricesSubmodule :
    A₁ in pairSelfAdjointMatricesSubmodule J J₂ ↔ Matrix.IsAdjointPair J J₂ A₁ A₁ := by
  simp only [pairSelfAdjointMatricesSubmodule, Submodule.mem_map_equiv,
    mem_isPairSelfAdjointSubmodule, toMatrix'_symm, ← isAdjointPair_toLinearMap₂',
    IsPairSelfAdjoint, toLin'_apply']

/--
Definition of `selfAdjointMatricesSubmodule` / `selfAdjointMatricesSubmodule` 的定义

English:
definition selfAdjointMatricesSubmodule
  signature: : Submodule R (Matrix n n R)
  body: pairSelfAdjointMatricesSubmodule J J

@[simp]

中文:
定义 selfAdjointMatricesSubmodule
  签名: : 子模 R (矩阵 n n R)
  定义体: pairSelfAdjointMatricesSubmodule J J

@[simp]

Depends on / 依赖: pairSelfAdjointMatricesSubmodule
-/
def selfAdjointMatricesSubmodule : Submodule R (Matrix n n R) :=
  pairSelfAdjointMatricesSubmodule J J

@[simp]
/--
theorem `mem_selfAdjointMatricesSubmodule` / 定理 `mem_selfAdjointMatricesSubmodule`

English:
theorem mem_selfAdjointMatricesSubmodule
  proof: by
  rw [selfAdjointMatricesSubmodule]; rw [mem_pairSelfAdjointMatricesSubmodule]; rw [Matrix.IsSelfAdjoint]

中文:
定理 mem_selfAdjointMatricesSubmodule
  证明: by
  rw [selfAdjointMatricesSubmodule]; rw [mem_pairSelfAdjointMatricesSubmodule]; rw [Matrix.IsSelfAdjoint]

Depends on / 依赖: IsSelfAdjoint, Matrix, Matrix.IsSelfAdjoint, mem_pairSelfAdjointMatricesSubmodule, selfAdjointMatricesSubmodule
-/
theorem mem_selfAdjointMatricesSubmodule :
    A₁ in selfAdjointMatricesSubmodule J ↔ J.IsSelfAdjoint A₁ := by
  rw [selfAdjointMatricesSubmodule]; rw [mem_pairSelfAdjointMatricesSubmodule]; rw [Matrix.IsSelfAdjoint]

/--
Definition of `skewAdjointMatricesSubmodule` / `skewAdjointMatricesSubmodule` 的定义

English:
definition skewAdjointMatricesSubmodule
  signature: : Submodule R (Matrix n n R)
  body: pairSelfAdjointMatricesSubmodule (-J) J

@[simp]

中文:
定义 skewAdjointMatricesSubmodule
  签名: : 子模 R (矩阵 n n R)
  定义体: pairSelfAdjointMatricesSubmodule (-J) J

@[simp]

Depends on / 依赖: pairSelfAdjointMatricesSubmodule
-/
def skewAdjointMatricesSubmodule : Submodule R (Matrix n n R) :=
  pairSelfAdjointMatricesSubmodule (-J) J

@[simp]
/--
theorem `mem_skewAdjointMatricesSubmodule` / 定理 `mem_skewAdjointMatricesSubmodule`

English:
theorem mem_skewAdjointMatricesSubmodule
  proof: by
  rw [skewAdjointMatricesSubmodule]; rw [mem_pairSelfAdjointMatricesSubmodule]
  simp [Matrix.IsSkewAdjoint, Matrix.IsAdjointPair]

中文:
定理 mem_skewAdjointMatricesSubmodule
  证明: by
  rw [skewAdjointMatricesSubmodule]; rw [mem_pairSelfAdjointMatricesSubmodule]
  simp [Matrix.IsSkewAdjoint, Matrix.IsAdjointPair]

Depends on / 依赖: IsAdjointPair, IsSkewAdjoint, Matrix, Matrix.IsAdjointPair, Matrix.IsSkewAdjoint, mem_pairSelfAdjointMatricesSubmodule, skewAdjointMatricesSubmodule
-/
theorem mem_skewAdjointMatricesSubmodule :
    A₁ in skewAdjointMatricesSubmodule J ↔ J.IsSkewAdjoint A₁ := by
  rw [skewAdjointMatricesSubmodule]; rw [mem_pairSelfAdjointMatricesSubmodule]
  simp [Matrix.IsSkewAdjoint, Matrix.IsAdjointPair]

end MatrixAdjoints

namespace LinearMap

/-! ### Nondegenerate bilinear forms -/

open Matrix

variable [CommRing R] [DecidableEq m] [Fintype m] [DecidableEq n] [Fintype n]
  {M : Matrix m n R}

section StandardBasis

variable {B : (m -> R) ->ₗ[R] (n -> R) ->ₗ[R] R}


/--
theorem `_root_.Matrix.SeparatingLeft.toLinearMap₂'` / 定理 `_root_.Matrix.SeparatingLeft.toLinearMap₂'`

English:
theorem _root_.Matrix.SeparatingLeft.toLinearMap₂'
  given: (h : M.SeparatingLeft)
  proof: by
  simpa [SeparatingLeft, toLinearMap₂'_apply', separatingLeft_def] using h

中文:
定理 _root_.矩阵.SeparatingLeft.toLinearMap₂'
  条件: (h : M.SeparatingLeft)
  证明: by
  simpa [SeparatingLeft, toLinearMap₂'_apply', separatingLeft_def] using h

Depends on / 依赖: SeparatingLeft, _apply, separatingLeft_def
-/
theorem _root_.Matrix.SeparatingLeft.toLinearMap₂' (h : M.SeparatingLeft) :
    (toLinearMap₂' R M).SeparatingLeft (R := R) := by
  simpa [SeparatingLeft, toLinearMap₂'_apply', separatingLeft_def] using h

/--
theorem `_root_.Matrix.SeparatingRight.toLinearMap₂'` / 定理 `_root_.Matrix.SeparatingRight.toLinearMap₂'`

English:
theorem _root_.Matrix.SeparatingRight.toLinearMap₂'
  given: (h : M.SeparatingRight)
  proof: by
  simpa [SeparatingRight, toLinearMap₂'_apply', separatingRight_def] using h

中文:
定理 _root_.矩阵.SeparatingRight.toLinearMap₂'
  条件: (h : M.SeparatingRight)
  证明: by
  simpa [SeparatingRight, toLinearMap₂'_apply', separatingRight_def] using h

Depends on / 依赖: SeparatingRight, _apply, separatingRight_def
-/
theorem _root_.Matrix.SeparatingRight.toLinearMap₂' (h : M.SeparatingRight) :
    (toLinearMap₂' R M).SeparatingRight (R := R) := by
  simpa [SeparatingRight, toLinearMap₂'_apply', separatingRight_def] using h

/--
theorem `_root_.Matrix.Nondegenerate.toLinearMap₂'` / 定理 `_root_.Matrix.Nondegenerate.toLinearMap₂'`

English:
theorem _root_.Matrix.Nondegenerate.toLinearMap₂'
  given: (h : M.Nondegenerate)
  proof: ⟨h.1.toLinearMap₂', h.2.toLinearMap₂'⟩

@[simp]

中文:
定理 _root_.矩阵.非退化.toLinearMap₂'
  条件: (h : M.非退化)
  证明: ⟨h.1.toLinearMap₂', h.2.toLinearMap₂'⟩

@[simp]
-/
theorem _root_.Matrix.Nondegenerate.toLinearMap₂' (h : M.Nondegenerate) :
    (toLinearMap₂' R M).Nondegenerate (R := R) :=
  ⟨h.1.toLinearMap₂', h.2.toLinearMap₂'⟩

@[simp]
/--
theorem `_root_.Matrix.separatingLeft_toLinearMap₂'_iff` / 定理 `_root_.Matrix.separatingLeft_toLinearMap₂'_iff`

English:
theorem _root_.Matrix.separatingLeft_toLinearMap₂'_iff
  proof: by
  refine ⟨fun h => separatingLeft_def.mpr ?_, SeparatingLeft.toLinearMap₂'⟩
exact fun v hv => h v fun w => (M.toLinearMap₂'_apply' _ _).trans hv w

@[simp]

中文:
定理 _root_.矩阵.separatingLeft_toLinearMap₂'_iff
  证明: by
  refine ⟨fun h => separatingLeft_def.mpr ?_, SeparatingLeft.toLinearMap₂'⟩
exact fun v hv => h v fun w => (M.toLinearMap₂'_apply' _ _).trans hv w

@[simp]

Depends on / 依赖: M.SeparatingLeft, M.toLinearMap, SeparatingLeft, SeparatingLeft.toLinearMap, _apply, separatingLeft_def, separatingLeft_def.mpr
-/
theorem _root_.Matrix.separatingLeft_toLinearMap₂'_iff :
    (toLinearMap₂' R M).SeparatingLeft (R := R) ↔ M.SeparatingLeft := by
  refine ⟨fun h => separatingLeft_def.mpr ?_, SeparatingLeft.toLinearMap₂'⟩
exact fun v hv => h v fun w => (M.toLinearMap₂'_apply' _ _).trans hv w

@[simp]
/--
theorem `_root_.Matrix.separatingRight_toLinearMap₂'_iff` / 定理 `_root_.Matrix.separatingRight_toLinearMap₂'_iff`

English:
theorem _root_.Matrix.separatingRight_toLinearMap₂'_iff
  proof: by
  refine ⟨fun h => separatingRight_def.mpr ?_, SeparatingRight.toLinearMap₂'⟩
exact fun v hv => h v fun w => (M.toLinearMap₂'_apply' _ _).trans hv w

@[simp]

中文:
定理 _root_.矩阵.separatingRight_toLinearMap₂'_iff
  证明: by
  refine ⟨fun h => separatingRight_def.mpr ?_, SeparatingRight.toLinearMap₂'⟩
exact fun v hv => h v fun w => (M.toLinearMap₂'_apply' _ _).trans hv w

@[simp]

Depends on / 依赖: M.SeparatingRight, M.toLinearMap, SeparatingRight, SeparatingRight.toLinearMap, _apply, separatingRight_def, separatingRight_def.mpr
-/
theorem _root_.Matrix.separatingRight_toLinearMap₂'_iff :
    (toLinearMap₂' R M).SeparatingRight (R := R) ↔ M.SeparatingRight := by
  refine ⟨fun h => separatingRight_def.mpr ?_, SeparatingRight.toLinearMap₂'⟩
exact fun v hv => h v fun w => (M.toLinearMap₂'_apply' _ _).trans hv w

@[simp]
/--
theorem `_root_.Matrix.nondegenerate_toLinearMap₂'_iff` / 定理 `_root_.Matrix.nondegenerate_toLinearMap₂'_iff`

English:
theorem _root_.Matrix.nondegenerate_toLinearMap₂'_iff
  proof: ⟨fun h => ⟨separatingLeft_toLinearMap₂'_iff.mp h.1, separatingRight_toLinearMap₂'_iff.mp h.2⟩,
   fun h => ⟨separatingLeft_toLinearMap₂'_iff.mpr h.1, separatingRight_toLinearMap₂'_iff.mpr h.2⟩⟩

@[simp]

中文:
定理 _root_.矩阵.nondegenerate_toLinearMap₂'_iff
  证明: ⟨fun h => ⟨separatingLeft_toLinearMap₂'_iff.mp h.1, separatingRight_toLinearMap₂'_iff.mp h.2⟩,
   fun h => ⟨separatingLeft_toLinearMap₂'_iff.mpr h.1, separatingRight_toLinearMap₂'_iff.mpr h.2⟩⟩

@[simp]

Depends on / 依赖: M.Nondegenerate, Nondegenerate
-/
theorem _root_.Matrix.nondegenerate_toLinearMap₂'_iff :
    (toLinearMap₂' R M).Nondegenerate (R := R) ↔ M.Nondegenerate :=
  ⟨fun h => ⟨separatingLeft_toLinearMap₂'_iff.mp h.1, separatingRight_toLinearMap₂'_iff.mp h.2⟩,
   fun h => ⟨separatingLeft_toLinearMap₂'_iff.mpr h.1, separatingRight_toLinearMap₂'_iff.mpr h.2⟩⟩

@[simp]
/--
theorem `separatingLeft_toMatrix₂'_iff` / 定理 `separatingLeft_toMatrix₂'_iff`

English:
theorem separatingLeft_toMatrix₂'_iff
  proof: separatingLeft_toLinearMap₂'_iff.symm.trans (toLinearMap₂'_toMatrix' (R := R) B).symm ▸ Iff.rfl

@[simp]

中文:
定理 separatingLeft_toMatrix₂'_iff
  证明: separatingLeft_toLinearMap₂'_iff.symm.trans (toLinearMap₂'_toMatrix' (R := R) B).symm ▸ Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl, _iff, _iff.symm.trans, _toMatrix
-/
theorem separatingLeft_toMatrix₂'_iff :
    (toMatrix₂' R B).SeparatingLeft ↔ B.SeparatingLeft :=
separatingLeft_toLinearMap₂'_iff.symm.trans (toLinearMap₂'_toMatrix' (R := R) B).symm ▸ Iff.rfl

@[simp]
/--
theorem `separatingRight_toMatrix₂'_iff` / 定理 `separatingRight_toMatrix₂'_iff`

English:
theorem separatingRight_toMatrix₂'_iff
  proof: separatingRight_toLinearMap₂'_iff.symm.trans
 (toLinearMap₂'_toMatrix' (R := R) B).symm ▸ Iff.rfl

@[simp]

中文:
定理 separatingRight_toMatrix₂'_iff
  证明: separatingRight_toLinearMap₂'_iff.symm.trans
 (toLinearMap₂'_toMatrix' (R := R) B).symm ▸ Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl, _iff, _iff.symm.trans, _toMatrix
-/
theorem separatingRight_toMatrix₂'_iff :
    (toMatrix₂' R B).SeparatingRight ↔ B.SeparatingRight :=
  separatingRight_toLinearMap₂'_iff.symm.trans
 (toLinearMap₂'_toMatrix' (R := R) B).symm ▸ Iff.rfl

@[simp]
/--
theorem `nondegenerate_toMatrix₂'_iff` / 定理 `nondegenerate_toMatrix₂'_iff`

English:
theorem nondegenerate_toMatrix₂'_iff
  proof: nondegenerate_toLinearMap₂'_iff.symm.trans (toLinearMap₂'_toMatrix' (R := R) B).symm ▸ Iff.rfl

中文:
定理 nondegenerate_toMatrix₂'_iff
  证明: nondegenerate_toLinearMap₂'_iff.symm.trans (toLinearMap₂'_toMatrix' (R := R) B).symm ▸ Iff.rfl

Depends on / 依赖: Iff.rfl, _iff, _iff.symm.trans, _toMatrix
-/
theorem nondegenerate_toMatrix₂'_iff :
    (toMatrix₂' R B).Nondegenerate ↔ B.Nondegenerate :=
nondegenerate_toLinearMap₂'_iff.symm.trans (toLinearMap₂'_toMatrix' (R := R) B).symm ▸ Iff.rfl

/--
theorem `SeparatingLeft.toMatrix₂'` / 定理 `SeparatingLeft.toMatrix₂'`

English:
theorem SeparatingLeft.toMatrix₂'
  given: (h : B.SeparatingLeft)
  statement: (toMatrix₂' R B).SeparatingLeft
  proof: separatingLeft_toMatrix₂'_iff.mpr h

中文:
定理 SeparatingLeft.toMatrix₂'
  条件: (h : B.SeparatingLeft)
  结论: (toMatrix₂' R B).SeparatingLeft
  证明: separatingLeft_toMatrix₂'_iff.mpr h

Depends on / 依赖: _iff, _iff.mpr
-/
theorem SeparatingLeft.toMatrix₂' (h : B.SeparatingLeft) : (toMatrix₂' R B).SeparatingLeft :=
  separatingLeft_toMatrix₂'_iff.mpr h

/--
theorem `SeparatingRight.toMatrix₂'` / 定理 `SeparatingRight.toMatrix₂'`

English:
theorem SeparatingRight.toMatrix₂'
  given: (h : B.SeparatingRight)
  statement: (toMatrix₂' R B).SeparatingRight
  proof: separatingRight_toMatrix₂'_iff.mpr h

中文:
定理 SeparatingRight.toMatrix₂'
  条件: (h : B.SeparatingRight)
  结论: (toMatrix₂' R B).SeparatingRight
  证明: separatingRight_toMatrix₂'_iff.mpr h

Depends on / 依赖: _iff, _iff.mpr
-/
theorem SeparatingRight.toMatrix₂' (h : B.SeparatingRight) : (toMatrix₂' R B).SeparatingRight :=
  separatingRight_toMatrix₂'_iff.mpr h

/--
theorem `Nondegenerate.toMatrix₂'` / 定理 `Nondegenerate.toMatrix₂'`

English:
theorem Nondegenerate.toMatrix₂'
  given: (h : B.Nondegenerate)
  statement: (toMatrix₂' R B).Nondegenerate
  proof: nondegenerate_toMatrix₂'_iff.mpr h

中文:
定理 非退化.toMatrix₂'
  条件: (h : B.非退化)
  结论: (toMatrix₂' R B).非退化
  证明: nondegenerate_toMatrix₂'_iff.mpr h

Depends on / 依赖: _iff, _iff.mpr
-/
theorem Nondegenerate.toMatrix₂' (h : B.Nondegenerate) : (toMatrix₂' R B).Nondegenerate :=
  nondegenerate_toMatrix₂'_iff.mpr h

end StandardBasis

section GeneralBasis

/-!
Lemmas transferring nondegeneracy (or left/right separating) between a matrix and its associated
bilinear form (for an arbitrary basis of a free module)
-/

variable [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂]
  (b₁ : Basis m R M₁) (b₂ : Basis n R M₂) {B : M₁ ->ₗ[R] M₂ ->ₗ[R] R}

/--
theorem `_root_.Matrix.separatingLeft_toLinearMap₂'_iff_separatingLeft_toLinearMap₂` / 定理 `_root_.Matrix.separatingLeft_toLinearMap₂'_iff_separatingLeft_toLinearMap₂`

English:
theorem _root_.Matrix.separatingLeft_toLinearMap₂'_iff_separatingLeft_toLinearMap₂
  proof: (separatingLeft_congr_iff b₁.equivFun.symm b₂.equivFun.symm).symm

中文:
定理 _root_.矩阵.separatingLeft_toLinearMap₂'_iff_separatingLeft_toLinearMap₂
  证明: (separatingLeft_congr_iff b₁.equivFun.symm b₂.equivFun.symm).symm
-/
theorem _root_.Matrix.separatingLeft_toLinearMap₂'_iff_separatingLeft_toLinearMap₂ :
    (toLinearMap₂' R M).SeparatingLeft (R := R) ↔ (toLinearMap₂ b₁ b₂ M).SeparatingLeft :=
  (separatingLeft_congr_iff b₁.equivFun.symm b₂.equivFun.symm).symm

/--
theorem `_root_.Matrix.separatingRight_toLinearMap₂'_iff_separatingRight_toLinearMap₂` / 定理 `_root_.Matrix.separatingRight_toLinearMap₂'_iff_separatingRight_toLinearMap₂`

English:
theorem _root_.Matrix.separatingRight_toLinearMap₂'_iff_separatingRight_toLinearMap₂
  proof: (separatingRight_congr_iff b₁.equivFun.symm b₂.equivFun.symm).symm

中文:
定理 _root_.矩阵.separatingRight_toLinearMap₂'_iff_separatingRight_toLinearMap₂
  证明: (separatingRight_congr_iff b₁.equivFun.symm b₂.equivFun.symm).symm
-/
theorem _root_.Matrix.separatingRight_toLinearMap₂'_iff_separatingRight_toLinearMap₂ :
    (toLinearMap₂' R M).SeparatingRight (R := R) ↔ (toLinearMap₂ b₁ b₂ M).SeparatingRight :=
  (separatingRight_congr_iff b₁.equivFun.symm b₂.equivFun.symm).symm

/--
theorem `_root_.Matrix.nondegenerate_toLinearMap₂'_iff_nondegenerate_toLinearMap₂` / 定理 `_root_.Matrix.nondegenerate_toLinearMap₂'_iff_nondegenerate_toLinearMap₂`

English:
theorem _root_.Matrix.nondegenerate_toLinearMap₂'_iff_nondegenerate_toLinearMap₂
  proof: (nondegenerate_congr_iff b₁.equivFun.symm b₂.equivFun.symm).symm

@[simp]

中文:
定理 _root_.矩阵.nondegenerate_toLinearMap₂'_iff_nondegenerate_toLinearMap₂
  证明: (nondegenerate_congr_iff b₁.equivFun.symm b₂.equivFun.symm).symm

@[simp]
-/
theorem _root_.Matrix.nondegenerate_toLinearMap₂'_iff_nondegenerate_toLinearMap₂ :
    (toLinearMap₂' R M).Nondegenerate (R := R) ↔ (toLinearMap₂ b₁ b₂ M).Nondegenerate :=
  (nondegenerate_congr_iff b₁.equivFun.symm b₂.equivFun.symm).symm

@[simp]
/--
theorem `_root_.Matrix.separatingLeft_toLinearMap₂_iff` / 定理 `_root_.Matrix.separatingLeft_toLinearMap₂_iff`

English:
theorem _root_.Matrix.separatingLeft_toLinearMap₂_iff
  proof: by
  rw [← separatingLeft_toLinearMap₂'_iff_separatingLeft_toLinearMap₂]; rw [separatingLeft_toLinearMap₂'_iff]

@[simp]

中文:
定理 _root_.矩阵.separatingLeft_toLinearMap₂_iff
  证明: by
  rw [← separatingLeft_toLinearMap₂'_iff_separatingLeft_toLinearMap₂]; rw [separatingLeft_toLinearMap₂'_iff]

@[simp]

Depends on / 依赖: _iff
-/
theorem _root_.Matrix.separatingLeft_toLinearMap₂_iff :
    (toLinearMap₂ b₁ b₂ M).SeparatingLeft ↔ M.SeparatingLeft := by
  rw [← separatingLeft_toLinearMap₂'_iff_separatingLeft_toLinearMap₂]; rw [separatingLeft_toLinearMap₂'_iff]

@[simp]
/--
theorem `_root_.Matrix.separatingRight_toLinearMap₂_iff` / 定理 `_root_.Matrix.separatingRight_toLinearMap₂_iff`

English:
theorem _root_.Matrix.separatingRight_toLinearMap₂_iff
  proof: by
  rw [← separatingRight_toLinearMap₂'_iff_separatingRight_toLinearMap₂]; rw [separatingRight_toLinearMap₂'_iff]

@[simp]

中文:
定理 _root_.矩阵.separatingRight_toLinearMap₂_iff
  证明: by
  rw [← separatingRight_toLinearMap₂'_iff_separatingRight_toLinearMap₂]; rw [separatingRight_toLinearMap₂'_iff]

@[simp]

Depends on / 依赖: _iff
-/
theorem _root_.Matrix.separatingRight_toLinearMap₂_iff :
    (toLinearMap₂ b₁ b₂ M).SeparatingRight ↔ M.SeparatingRight := by
  rw [← separatingRight_toLinearMap₂'_iff_separatingRight_toLinearMap₂]; rw [separatingRight_toLinearMap₂'_iff]

@[simp]
/--
theorem `_root_.Matrix.nondegenerate_toLinearMap₂_iff` / 定理 `_root_.Matrix.nondegenerate_toLinearMap₂_iff`

English:
theorem _root_.Matrix.nondegenerate_toLinearMap₂_iff
  proof: by
  rw [← nondegenerate_toLinearMap₂'_iff_nondegenerate_toLinearMap₂]; rw [nondegenerate_toLinearMap₂'_iff]

中文:
定理 _root_.矩阵.nondegenerate_toLinearMap₂_iff
  证明: by
  rw [← nondegenerate_toLinearMap₂'_iff_nondegenerate_toLinearMap₂]; rw [nondegenerate_toLinearMap₂'_iff]

Depends on / 依赖: _iff
-/
theorem _root_.Matrix.nondegenerate_toLinearMap₂_iff :
    (toLinearMap₂ b₁ b₂ M).Nondegenerate ↔ M.Nondegenerate := by
  rw [← nondegenerate_toLinearMap₂'_iff_nondegenerate_toLinearMap₂]; rw [nondegenerate_toLinearMap₂'_iff]

/--
theorem `_root_.Matrix.SeparatingLeft.toLinearMap₂` / 定理 `_root_.Matrix.SeparatingLeft.toLinearMap₂`

English:
theorem _root_.Matrix.SeparatingLeft.toLinearMap₂
  given: (h : M.SeparatingLeft)
  proof: (separatingLeft_toLinearMap₂_iff b₁ b₂).mpr h

中文:
定理 _root_.矩阵.SeparatingLeft.toLinearMap₂
  条件: (h : M.SeparatingLeft)
  证明: (separatingLeft_toLinearMap₂_iff b₁ b₂).mpr h
-/
theorem _root_.Matrix.SeparatingLeft.toLinearMap₂ (h : M.SeparatingLeft) :
    (toLinearMap₂ b₁ b₂ M).SeparatingLeft :=
  (separatingLeft_toLinearMap₂_iff b₁ b₂).mpr h

/--
theorem `_root_.Matrix.SeparatingRight.toLinearMap₂` / 定理 `_root_.Matrix.SeparatingRight.toLinearMap₂`

English:
theorem _root_.Matrix.SeparatingRight.toLinearMap₂
  given: (h : M.SeparatingRight)
  proof: (separatingRight_toLinearMap₂_iff b₁ b₂).mpr h

中文:
定理 _root_.矩阵.SeparatingRight.toLinearMap₂
  条件: (h : M.SeparatingRight)
  证明: (separatingRight_toLinearMap₂_iff b₁ b₂).mpr h
-/
theorem _root_.Matrix.SeparatingRight.toLinearMap₂ (h : M.SeparatingRight) :
    (toLinearMap₂ b₁ b₂ M).SeparatingRight :=
  (separatingRight_toLinearMap₂_iff b₁ b₂).mpr h

/--
theorem `_root_.Matrix.Nondegenerate.toLinearMap₂` / 定理 `_root_.Matrix.Nondegenerate.toLinearMap₂`

English:
theorem _root_.Matrix.Nondegenerate.toLinearMap₂
  given: (h : M.Nondegenerate)
  proof: (nondegenerate_toLinearMap₂_iff b₁ b₂).mpr h

@[simp]

中文:
定理 _root_.矩阵.非退化.toLinearMap₂
  条件: (h : M.非退化)
  证明: (nondegenerate_toLinearMap₂_iff b₁ b₂).mpr h

@[simp]
-/
theorem _root_.Matrix.Nondegenerate.toLinearMap₂ (h : M.Nondegenerate) :
    (toLinearMap₂ b₁ b₂ M).Nondegenerate :=
  (nondegenerate_toLinearMap₂_iff b₁ b₂).mpr h

@[simp]
/--
theorem `separatingLeft_toMatrix₂_iff` / 定理 `separatingLeft_toMatrix₂_iff`

English:
theorem separatingLeft_toMatrix₂_iff
  proof: (Matrix.separatingLeft_toLinearMap₂_iff b₁ b₂).symm.trans
    (Matrix.toLinearMap₂_toMatrix₂ b₁ b₂ B).symm ▸ Iff.rfl

@[simp]

中文:
定理 separatingLeft_toMatrix₂_iff
  证明: (Matrix.separatingLeft_toLinearMap₂_iff b₁ b₂).symm.trans
    (Matrix.toLinearMap₂_toMatrix₂ b₁ b₂ B).symm ▸ Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl, Matrix, Matrix.separatingLeft_toLinearMap, Matrix.toLinearMap, symm.trans
-/
theorem separatingLeft_toMatrix₂_iff :
    (toMatrix₂ b₁ b₂ B).SeparatingLeft ↔ B.SeparatingLeft :=
(Matrix.separatingLeft_toLinearMap₂_iff b₁ b₂).symm.trans
    (Matrix.toLinearMap₂_toMatrix₂ b₁ b₂ B).symm ▸ Iff.rfl

@[simp]
/--
theorem `separatingRight_toMatrix₂_iff` / 定理 `separatingRight_toMatrix₂_iff`

English:
theorem separatingRight_toMatrix₂_iff
  proof: (Matrix.separatingRight_toLinearMap₂_iff b₁ b₂).symm.trans
    (Matrix.toLinearMap₂_toMatrix₂ b₁ b₂ B).symm ▸ Iff.rfl

@[simp]

中文:
定理 separatingRight_toMatrix₂_iff
  证明: (Matrix.separatingRight_toLinearMap₂_iff b₁ b₂).symm.trans
    (Matrix.toLinearMap₂_toMatrix₂ b₁ b₂ B).symm ▸ Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl, Matrix, Matrix.separatingRight_toLinearMap, Matrix.toLinearMap, symm.trans
-/
theorem separatingRight_toMatrix₂_iff :
    (toMatrix₂ b₁ b₂ B).SeparatingRight ↔ B.SeparatingRight :=
(Matrix.separatingRight_toLinearMap₂_iff b₁ b₂).symm.trans
    (Matrix.toLinearMap₂_toMatrix₂ b₁ b₂ B).symm ▸ Iff.rfl

@[simp]
/--
theorem `nondegenerate_toMatrix₂_iff` / 定理 `nondegenerate_toMatrix₂_iff`

English:
theorem nondegenerate_toMatrix₂_iff
  proof: (Matrix.nondegenerate_toLinearMap₂_iff b₁ b₂).symm.trans
    (Matrix.toLinearMap₂_toMatrix₂ b₁ b₂ B).symm ▸ Iff.rfl

中文:
定理 nondegenerate_toMatrix₂_iff
  证明: (Matrix.nondegenerate_toLinearMap₂_iff b₁ b₂).symm.trans
    (Matrix.toLinearMap₂_toMatrix₂ b₁ b₂ B).symm ▸ Iff.rfl

Depends on / 依赖: Iff.rfl, Matrix, Matrix.nondegenerate_toLinearMap, Matrix.toLinearMap, symm.trans
-/
theorem nondegenerate_toMatrix₂_iff :
    (toMatrix₂ b₁ b₂ B).Nondegenerate ↔ B.Nondegenerate :=
(Matrix.nondegenerate_toLinearMap₂_iff b₁ b₂).symm.trans
    (Matrix.toLinearMap₂_toMatrix₂ b₁ b₂ B).symm ▸ Iff.rfl

/--
theorem `SeparatingLeft.toMatrix₂` / 定理 `SeparatingLeft.toMatrix₂`

English:
theorem SeparatingLeft.toMatrix₂
  given: (h : B.SeparatingLeft)
  proof: (separatingLeft_toMatrix₂_iff b₁ b₂).mpr h

中文:
定理 SeparatingLeft.toMatrix₂
  条件: (h : B.SeparatingLeft)
  证明: (separatingLeft_toMatrix₂_iff b₁ b₂).mpr h
-/
theorem SeparatingLeft.toMatrix₂ (h : B.SeparatingLeft) :
    (toMatrix₂ b₁ b₂ B).SeparatingLeft :=
  (separatingLeft_toMatrix₂_iff b₁ b₂).mpr h

/--
theorem `SeparatingRight.toMatrix₂` / 定理 `SeparatingRight.toMatrix₂`

English:
theorem SeparatingRight.toMatrix₂
  given: (h : B.SeparatingRight)
  proof: (separatingRight_toMatrix₂_iff b₁ b₂).mpr h

中文:
定理 SeparatingRight.toMatrix₂
  条件: (h : B.SeparatingRight)
  证明: (separatingRight_toMatrix₂_iff b₁ b₂).mpr h
-/
theorem SeparatingRight.toMatrix₂ (h : B.SeparatingRight) :
    (toMatrix₂ b₁ b₂ B).SeparatingRight :=
  (separatingRight_toMatrix₂_iff b₁ b₂).mpr h

/--
theorem `Nondegenerate.toMatrix₂` / 定理 `Nondegenerate.toMatrix₂`

English:
theorem Nondegenerate.toMatrix₂
  given: (h : B.Nondegenerate)
  proof: (nondegenerate_toMatrix₂_iff b₁ b₂).mpr h

中文:
定理 非退化.toMatrix₂
  条件: (h : B.非退化)
  证明: (nondegenerate_toMatrix₂_iff b₁ b₂).mpr h
-/
theorem Nondegenerate.toMatrix₂ (h : B.Nondegenerate) :
    (toMatrix₂ b₁ b₂ B).Nondegenerate :=
  (nondegenerate_toMatrix₂_iff b₁ b₂).mpr h

end GeneralBasis

section Det
/-!
Some shorthands for combining the above with `Matrix.nondegenerate_of_det_ne_zero` in the
case of a domain
-/


variable [IsDomain R] {M : Matrix n n R}

section DecidableEq
variable [DecidableEq m]

/--
theorem `nondegenerate_toLinearMap₂'_iff_det_ne_zero` / 定理 `nondegenerate_toLinearMap₂'_iff_det_ne_zero`

English:
theorem nondegenerate_toLinearMap₂'_iff_det_ne_zero
  proof: by
  rw [nondegenerate_toLinearMap₂'_iff]; rw [Matrix.nondegenerate_iff_det_ne_zero]

中文:
定理 nondegenerate_toLinearMap₂'_iff_det_ne_zero
  证明: by
  rw [nondegenerate_toLinearMap₂'_iff]; rw [Matrix.nondegenerate_iff_det_ne_zero]

Depends on / 依赖: M.det, Matrix, Matrix.nondegenerate_iff_det_ne_zero, _iff, nondegenerate_iff_det_ne_zero
-/
theorem nondegenerate_toLinearMap₂'_iff_det_ne_zero :
    (Matrix.toLinearMap₂' R M).Nondegenerate (R := R) ↔ M.det != 0 := by
  rw [nondegenerate_toLinearMap₂'_iff]; rw [Matrix.nondegenerate_iff_det_ne_zero]

/--
theorem `separatingLeft_toLinearMap₂'_iff_det_ne_zero` / 定理 `separatingLeft_toLinearMap₂'_iff_det_ne_zero`

English:
theorem separatingLeft_toLinearMap₂'_iff_det_ne_zero
  proof: by
  simpa using separatingLeft_iff_det_ne_zero

中文:
定理 separatingLeft_toLinearMap₂'_iff_det_ne_zero
  证明: by
  simpa using separatingLeft_iff_det_ne_zero

Depends on / 依赖: M.det, separatingLeft_iff_det_ne_zero
-/
theorem separatingLeft_toLinearMap₂'_iff_det_ne_zero :
    (Matrix.toLinearMap₂' R M).SeparatingLeft (R := R) ↔ M.det != 0 := by
  simpa using separatingLeft_iff_det_ne_zero

/--
theorem `separatingRight_toLinearMap₂'_iff_det_ne_zero` / 定理 `separatingRight_toLinearMap₂'_iff_det_ne_zero`

English:
theorem separatingRight_toLinearMap₂'_iff_det_ne_zero
  proof: by
  simpa using separatingRight_iff_det_ne_zero

中文:
定理 separatingRight_toLinearMap₂'_iff_det_ne_zero
  证明: by
  simpa using separatingRight_iff_det_ne_zero

Depends on / 依赖: M.det, separatingRight_iff_det_ne_zero
-/
theorem separatingRight_toLinearMap₂'_iff_det_ne_zero :
    (Matrix.toLinearMap₂' R M).SeparatingRight (R := R) ↔ M.det != 0 := by
  simpa using separatingRight_iff_det_ne_zero

/--
theorem `separatingLeft_toLinearMap₂'_of_det_ne_zero'` / 定理 `separatingLeft_toLinearMap₂'_of_det_ne_zero'`

English:
theorem separatingLeft_toLinearMap₂'_of_det_ne_zero'
  given: (h : M.det != 0)
  proof: separatingLeft_toLinearMap₂'_iff_det_ne_zero.mpr h

中文:
定理 separatingLeft_toLinearMap₂'_of_det_ne_zero'
  条件: (h : M.det != 0)
  证明: separatingLeft_toLinearMap₂'_iff_det_ne_zero.mpr h
-/
theorem separatingLeft_toLinearMap₂'_of_det_ne_zero' (h : M.det != 0) :
    (Matrix.toLinearMap₂' R M).SeparatingLeft (R := R) :=
  separatingLeft_toLinearMap₂'_iff_det_ne_zero.mpr h

/--
theorem `separatingRight_toLinearMap₂'_of_det_ne_zero'` / 定理 `separatingRight_toLinearMap₂'_of_det_ne_zero'`

English:
theorem separatingRight_toLinearMap₂'_of_det_ne_zero'
  given: (h : M.det != 0)
  proof: separatingRight_toLinearMap₂'_iff_det_ne_zero.mpr h

中文:
定理 separatingRight_toLinearMap₂'_of_det_ne_zero'
  条件: (h : M.det != 0)
  证明: separatingRight_toLinearMap₂'_iff_det_ne_zero.mpr h
-/
theorem separatingRight_toLinearMap₂'_of_det_ne_zero' (h : M.det != 0) :
    (Matrix.toLinearMap₂' R M).SeparatingRight (R := R) :=
  separatingRight_toLinearMap₂'_iff_det_ne_zero.mpr h

/--
theorem `nondegenerate_toLinearMap₂'_of_det_ne_zero'` / 定理 `nondegenerate_toLinearMap₂'_of_det_ne_zero'`

English:
theorem nondegenerate_toLinearMap₂'_of_det_ne_zero'
  given: (h : M.det != 0)
  proof: nondegenerate_toLinearMap₂'_iff_det_ne_zero.mpr h

中文:
定理 nondegenerate_toLinearMap₂'_of_det_ne_zero'
  条件: (h : M.det != 0)
  证明: nondegenerate_toLinearMap₂'_iff_det_ne_zero.mpr h
-/
theorem nondegenerate_toLinearMap₂'_of_det_ne_zero' (h : M.det != 0) :
    (Matrix.toLinearMap₂' R M).Nondegenerate (R := R) :=
  nondegenerate_toLinearMap₂'_iff_det_ne_zero.mpr h

end DecidableEq

variable [AddCommMonoid M₁] [Module R M₁]
  (b : Basis m R M₁) {B : M₁ ->ₗ[R] M₁ ->ₗ[R] R}

/--
theorem `separatingLeft_iff_det_ne_zero` / 定理 `separatingLeft_iff_det_ne_zero`

English:
theorem separatingLeft_iff_det_ne_zero
  proof: by
  rw [← Matrix.separatingLeft_iff_det_ne_zero]; rw [separatingLeft_toMatrix₂_iff]

中文:
定理 separatingLeft_iff_det_ne_zero
  证明: by
  rw [← Matrix.separatingLeft_iff_det_ne_zero]; rw [separatingLeft_toMatrix₂_iff]

Depends on / 依赖: Matrix, Matrix.separatingLeft_iff_det_ne_zero, separatingLeft_iff_det_ne_zero
-/
theorem separatingLeft_iff_det_ne_zero :
    B.SeparatingLeft ↔ (toMatrix₂ b b B).det != 0 := by
  rw [← Matrix.separatingLeft_iff_det_ne_zero]; rw [separatingLeft_toMatrix₂_iff]

/--
theorem `separatingLeft_of_det_ne_zero` / 定理 `separatingLeft_of_det_ne_zero`

English:
theorem separatingLeft_of_det_ne_zero
  given: (h : (toMatrix₂ b b B).det != 0)
  statement: B.SeparatingLeft
  proof: (separatingLeft_iff_det_ne_zero b).mpr h

中文:
定理 separatingLeft_of_det_ne_zero
  条件: (h : (toMatrix₂ b b B).det != 0)
  结论: B.SeparatingLeft
  证明: (separatingLeft_iff_det_ne_zero b).mpr h

Depends on / 依赖: separatingLeft_iff_det_ne_zero
-/
theorem separatingLeft_of_det_ne_zero (h : (toMatrix₂ b b B).det != 0) : B.SeparatingLeft :=
  (separatingLeft_iff_det_ne_zero b).mpr h

/--
theorem `separatingRight_iff_det_ne_zero` / 定理 `separatingRight_iff_det_ne_zero`

English:
theorem separatingRight_iff_det_ne_zero
  proof: by
  rw [← Matrix.separatingRight_iff_det_ne_zero]; rw [separatingRight_toMatrix₂_iff]

中文:
定理 separatingRight_iff_det_ne_zero
  证明: by
  rw [← Matrix.separatingRight_iff_det_ne_zero]; rw [separatingRight_toMatrix₂_iff]

Depends on / 依赖: Matrix, Matrix.separatingRight_iff_det_ne_zero, separatingRight_iff_det_ne_zero
-/
theorem separatingRight_iff_det_ne_zero :
    B.SeparatingRight ↔ (toMatrix₂ b b B).det != 0 := by
  rw [← Matrix.separatingRight_iff_det_ne_zero]; rw [separatingRight_toMatrix₂_iff]

/--
theorem `separatingRight_of_det_ne_zero` / 定理 `separatingRight_of_det_ne_zero`

English:
theorem separatingRight_of_det_ne_zero
  given: (h : (toMatrix₂ b b B).det != 0)
  statement: B.SeparatingRight
  proof: (separatingRight_iff_det_ne_zero b).mpr h

中文:
定理 separatingRight_of_det_ne_zero
  条件: (h : (toMatrix₂ b b B).det != 0)
  结论: B.SeparatingRight
  证明: (separatingRight_iff_det_ne_zero b).mpr h

Depends on / 依赖: separatingRight_iff_det_ne_zero
-/
theorem separatingRight_of_det_ne_zero (h : (toMatrix₂ b b B).det != 0) : B.SeparatingRight :=
  (separatingRight_iff_det_ne_zero b).mpr h

/--
theorem `nondegenerate_iff_det_ne_zero` / 定理 `nondegenerate_iff_det_ne_zero`

English:
theorem nondegenerate_iff_det_ne_zero
  proof: by
  rw [← Matrix.nondegenerate_iff_det_ne_zero]; rw [nondegenerate_toMatrix₂_iff]

中文:
定理 nondegenerate_iff_det_ne_zero
  证明: by
  rw [← Matrix.nondegenerate_iff_det_ne_zero]; rw [nondegenerate_toMatrix₂_iff]

Depends on / 依赖: Matrix, Matrix.nondegenerate_iff_det_ne_zero, nondegenerate_iff_det_ne_zero
-/
theorem nondegenerate_iff_det_ne_zero :
    B.Nondegenerate ↔ (toMatrix₂ b b B).det != 0 := by
  rw [← Matrix.nondegenerate_iff_det_ne_zero]; rw [nondegenerate_toMatrix₂_iff]

/--
theorem `nondegenerate_of_det_ne_zero` / 定理 `nondegenerate_of_det_ne_zero`

English:
theorem nondegenerate_of_det_ne_zero
  given: (h : (toMatrix₂ b b B).det != 0)
  statement: B.Nondegenerate
  proof: (nondegenerate_iff_det_ne_zero b).mpr h

中文:
定理 nondegenerate_of_det_ne_zero
  条件: (h : (toMatrix₂ b b B).det != 0)
  结论: B.非退化
  证明: (nondegenerate_iff_det_ne_zero b).mpr h

Depends on / 依赖: nondegenerate_iff_det_ne_zero
-/
theorem nondegenerate_of_det_ne_zero (h : (toMatrix₂ b b B).det != 0) : B.Nondegenerate :=
  (nondegenerate_iff_det_ne_zero b).mpr h

end Det

end LinearMap
