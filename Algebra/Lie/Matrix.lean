/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Lie algebras of matrices

An important class of Lie algebras are those arising from the associative algebra structure on
square matrices over a commutative ring. This file provides some very basic definitions whose
primary value stems from their utility when constructing the classical Lie algebras using matrices.

## Main definitions

  * `lieEquivMatrix'`
  * `Matrix.lieConj`
  * `Matrix.reindexLieEquiv`

## Tags

lie algebra, matrix
-/

@[expose] public section


universe u v w w₁ w₂

section Matrices

open scoped Matrix

variable {R : Type u} [CommRing R]
variable {n : Type w} [DecidableEq n] [Fintype n]

attribute [local instance 100] LieRing.ofAssociativeRing

/--
Definition of `lieEquivMatrix'` / `lieEquivMatrix'` 的定义

English:
definition lieEquivMatrix'
  signature: : Module.End R (n -> R) ≃ₗ⁅R⁆ Matrix n n R
  body: { LinearMap.toMatrix' with
    map_lie' := fun {T S} => by
      let f := @LinearMap.toMatrix' R _ n n _ _
      change f (T.comp S - S.comp T) = f T * f S - f S * f T
      have h : forall T S : Module.End R _, f (T.comp S) = f T * f S := LinearMap.toMatrix'_comp
      rw [map_sub]; rw [h]; rw [h] 

中文:
定义 lieEquivMatrix'
  签名: : 模.End R (n -> R) ≃ₗ⁅R⁆ 矩阵 n n R
  定义体: { LinearMap.toMatrix' with
    map_lie' := fun {T S} => by
      let f := @LinearMap.toMatrix' R _ n n _ _
      change f (T.comp S - S.comp T) = f T * f S - f S * f T
      have h : forall T S : Module.End R _, f (T.comp S) = f T * f S := LinearMap.toMatrix'_comp
      rw [map_sub]; rw [h]; rw [h] 

Depends on / 依赖: LinearMap, LinearMap.toMatrix, Module, Module.End, S.comp, T.comp, _comp, map_lie, map_sub, toMatrix
-/
def lieEquivMatrix' : Module.End R (n -> R) ≃ₗ⁅R⁆ Matrix n n R :=
  { LinearMap.toMatrix' with
    map_lie' := fun {T S} => by
      let f := @LinearMap.toMatrix' R _ n n _ _
      change f (T.comp S - S.comp T) = f T * f S - f S * f T
      have h : forall T S : Module.End R _, f (T.comp S) = f T * f S := LinearMap.toMatrix'_comp
      rw [map_sub]; rw [h]; rw [h] }

@[simp]
/--
theorem `lieEquivMatrix'_apply` / 定理 `lieEquivMatrix'_apply`

English:
theorem lieEquivMatrix'_apply
  given: (f : Module.End R (n -> R))
  proof: rfl

@[simp]

中文:
定理 lieEquivMatrix'_apply
  条件: (f : 模.End R (n -> R))
  证明: rfl

@[simp]
-/
theorem lieEquivMatrix'_apply (f : Module.End R (n -> R)) :
    lieEquivMatrix' f = LinearMap.toMatrix' f :=
  rfl

@[simp]
/--
theorem `lieEquivMatrix'_symm_apply` / 定理 `lieEquivMatrix'_symm_apply`

English:
theorem lieEquivMatrix'_symm_apply
  given: (A : Matrix n n R)
  proof: rfl

中文:
定理 lieEquivMatrix'_symm_apply
  条件: (A : 矩阵 n n R)
  证明: rfl
-/
theorem lieEquivMatrix'_symm_apply (A : Matrix n n R) :
    (@lieEquivMatrix' R _ n _ _).symm A = Matrix.toLin' A :=
  rfl

namespace Matrix

/--
Definition of `lieConj` / `lieConj` 的定义

English:
definition lieConj
  signature: (P : Matrix n n R) (h : Invertible P)
  body: ((@lieEquivMatrix' R _ n _ _).symm.trans (P.toLinearEquiv' h).lieConj).trans lieEquivMatrix'

@[simp]

中文:
定义 lieConj
  签名: (P : 矩阵 n n R) (h : 可逆 P)
  定义体: ((@lieEquivMatrix' R _ n _ _).symm.trans (P.toLinearEquiv' h).lieConj).trans lieEquivMatrix'

@[simp]

Depends on / 依赖: P.toLinearEquiv, lieConj, lieEquivMatrix, symm.trans, toLinearEquiv
-/
def lieConj (P : Matrix n n R) (h : Invertible P) : Matrix n n R ≃ₗ⁅R⁆ Matrix n n R :=
  ((@lieEquivMatrix' R _ n _ _).symm.trans (P.toLinearEquiv' h).lieConj).trans lieEquivMatrix'

@[simp]
/--
theorem `lieConj_apply` / 定理 `lieConj_apply`

English:
theorem lieConj_apply
  given: (P A : Matrix n n R) (h : Invertible P)
  proof: by
  simp [LinearEquiv.conj_apply, Matrix.lieConj, LinearMap.toMatrix'_comp,
    LinearMap.toMatrix'_toLin']

@[simp]

中文:
定理 lieConj_apply
  条件: (P A : 矩阵 n n R) (h : 可逆 P)
  证明: by
  simp [LinearEquiv.conj_apply, Matrix.lieConj, LinearMap.toMatrix'_comp,
    LinearMap.toMatrix'_toLin']

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.conj_apply, LinearMap, LinearMap.toMatrix, Matrix, Matrix.lieConj, _comp, _toLin, conj_apply, lieConj, toMatrix
-/
theorem lieConj_apply (P A : Matrix n n R) (h : Invertible P) :
    P.lieConj h A = P * A * P⁻¹ := by
  simp [LinearEquiv.conj_apply, Matrix.lieConj, LinearMap.toMatrix'_comp,
    LinearMap.toMatrix'_toLin']

@[simp]
/--
theorem `lieConj_symm_apply` / 定理 `lieConj_symm_apply`

English:
theorem lieConj_symm_apply
  given: (P A : Matrix n n R) (h : Invertible P)
  proof: by
  simp [LinearEquiv.symm_conj_apply, Matrix.lieConj, LinearMap.toMatrix'_comp,
    LinearMap.toMatrix'_toLin']

中文:
定理 lieConj_symm_apply
  条件: (P A : 矩阵 n n R) (h : 可逆 P)
  证明: by
  simp [LinearEquiv.symm_conj_apply, Matrix.lieConj, LinearMap.toMatrix'_comp,
    LinearMap.toMatrix'_toLin']

Depends on / 依赖: LinearEquiv, LinearEquiv.symm_conj_apply, LinearMap, LinearMap.toMatrix, Matrix, Matrix.lieConj, _comp, _toLin, lieConj, symm_conj_apply, toMatrix
-/
theorem lieConj_symm_apply (P A : Matrix n n R) (h : Invertible P) :
    (P.lieConj h).symm A = P⁻¹ * A * P := by
  simp [LinearEquiv.symm_conj_apply, Matrix.lieConj, LinearMap.toMatrix'_comp,
    LinearMap.toMatrix'_toLin']

variable {m : Type w₁} [DecidableEq m] [Fintype m] (e : n ≃ m)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `reindexLieEquiv` / `reindexLieEquiv` 的定义

English:
definition reindexLieEquiv
  signature: : Matrix n n R ≃ₗ⁅R⁆ Matrix m m R
  body: { Matrix.reindexLinearEquiv R R e e with
    toFun := Matrix.reindex e e
    map_lie' := fun {_ _} => by
      simp only [LieRing.of_associative_ring_bracket, Matrix.reindex_apply,
        Matrix.submatrix_mul_equiv, Matrix.submatrix_sub, Pi.sub_apply] }

@[simp]

中文:
定义 reindexLieEquiv
  签名: : 矩阵 n n R ≃ₗ⁅R⁆ 矩阵 m m R
  定义体: { Matrix.reindexLinearEquiv R R e e with
    toFun := Matrix.reindex e e
    map_lie' := fun {_ _} => by
      simp only [LieRing.of_associative_ring_bracket, Matrix.reindex_apply,
        Matrix.submatrix_mul_equiv, Matrix.submatrix_sub, Pi.sub_apply] }

@[simp]

Depends on / 依赖: LieRing, LieRing.of_associative_ring_bracket, Matrix, Matrix.reindex, Matrix.reindexLinearEquiv, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.submatrix_sub, Pi.sub_apply, map_lie, of_associative_ring_bracket, reindex, reindexLinearEquiv, reindex_apply, sub_apply, submatrix_mul_equiv, submatrix_sub
-/
def reindexLieEquiv : Matrix n n R ≃ₗ⁅R⁆ Matrix m m R :=
  { Matrix.reindexLinearEquiv R R e e with
    toFun := Matrix.reindex e e
    map_lie' := fun {_ _} => by
      simp only [LieRing.of_associative_ring_bracket, Matrix.reindex_apply,
        Matrix.submatrix_mul_equiv, Matrix.submatrix_sub, Pi.sub_apply] }

@[simp]
/--
theorem `reindexLieEquiv_apply` / 定理 `reindexLieEquiv_apply`

English:
theorem reindexLieEquiv_apply
  given: (M : Matrix n n R)
  proof: rfl

@[simp]

中文:
定理 reindexLieEquiv_apply
  条件: (M : 矩阵 n n R)
  证明: rfl

@[simp]
-/
theorem reindexLieEquiv_apply (M : Matrix n n R) :
    Matrix.reindexLieEquiv e M = Matrix.reindex e e M :=
  rfl

@[simp]
/--
theorem `reindexLieEquiv_symm` / 定理 `reindexLieEquiv_symm`

English:
theorem reindexLieEquiv_symm
  proof: rfl

中文:
定理 reindexLieEquiv_symm
  证明: rfl
-/
theorem reindexLieEquiv_symm :
    (Matrix.reindexLieEquiv e : _ ≃ₗ⁅R⁆ _).symm = Matrix.reindexLieEquiv e.symm :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LieRingModule (Matrix n n R) (n -> R)
  body: mulVec
  add_lie := add_mulVec
  lie_add := mulVec_add
  leibniz_lie x y v := by simp only [Ring.lie_def, mulVec_mulVec, sub_mulVec, sub_add_cancel]

中文:
实例 :
  签名: Lie环模 (矩阵 n n R) (n -> R)
  定义体: mulVec
  add_lie := add_mulVec
  lie_add := mulVec_add
  leibniz_lie x y v := by simp only [Ring.lie_def, mulVec_mulVec, sub_mulVec, sub_add_cancel]

Depends on / 依赖: mulVec
-/
instance : LieRingModule (Matrix n n R) (n -> R) where
  bracket := mulVec
  add_lie := add_mulVec
  lie_add := mulVec_add
  leibniz_lie x y v := by simp only [Ring.lie_def, mulVec_mulVec, sub_mulVec, sub_add_cancel]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LieModule R (Matrix n n R) (n -> R)
  body: smul_mulVec
  lie_smul t A := mulVec_smul A t

中文:
实例 :
  签名: Lie模 R (矩阵 n n R) (n -> R)
  定义体: smul_mulVec
  lie_smul t A := mulVec_smul A t

Depends on / 依赖: smul_mulVec
-/
instance : LieModule R (Matrix n n R) (n -> R) where
  smul_lie := smul_mulVec
  lie_smul t A := mulVec_smul A t

/--
lemma `lie_apply` / 引理 `lie_apply`

English:
lemma lie_apply
  given: (A : Matrix n n R) (v : n -> R)
  statement: ⁅A, v⁆ = A *ᵥ v
  proof: rfl

中文:
引理 lie_apply
  条件: (A : 矩阵 n n R) (v : n -> R)
  结论: ⁅A, v⁆ = A *ᵥ v
  证明: rfl
-/
@[simp] lemma lie_apply (A : Matrix n n R) (v : n -> R) : ⁅A, v⁆ = A *ᵥ v := rfl

end Matrix

namespace LieModule

@[simp]
/--
theorem `toEnd_matrix` / 定理 `toEnd_matrix`

English:
theorem toEnd_matrix
  proof: by
  ext; simp

中文:
定理 toEnd_matrix
  证明: by
  ext; simp
-/
theorem toEnd_matrix :
    toEnd R (Matrix n n R) (n -> R) = (lieEquivMatrix' (R := R) (n := n)).symm := by
  ext; simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsFaithful R (Matrix n n R) (n -> R)
  body: by
    simpa using EmbeddingLike.injective _

中文:
实例 :
  签名: 是忠实 R (矩阵 n n R) (n -> R)
  定义体: by
    simpa using EmbeddingLike.injective _

Depends on / 依赖: EmbeddingLike, EmbeddingLike.injective, injective
-/
instance : IsFaithful R (Matrix n n R) (n -> R) where
  injective_toEnd := by
    simpa using EmbeddingLike.injective _

end LieModule

end Matrices
