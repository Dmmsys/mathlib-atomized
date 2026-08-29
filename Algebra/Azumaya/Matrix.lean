/-
Copyright (c) 2025 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Jujian Zhang
-/
module

public import Mathlib.Algebra.Azumaya.Defs
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# Matrix algebra is an Azumaya algebra over R

In this file we prove that finite-dimensional matrix algebra `Matrix n n R` over `R`
is an Azumaya algebra where `R` is a commutative ring.

## Main Results

- `IsAzumaya.Matrix`: Finite-dimensional matrix algebra over `R` is Azumaya.

-/

public section
open scoped TensorProduct

variable (R n : Type*) [CommSemiring R] [Fintype n] [DecidableEq n]

noncomputable section

open Matrix MulOpposite

/--
Definition of `AlgHom.mulLeftRightMatrix_inv` / `AlgHom.mulLeftRightMatrix_inv` 的定义

English:
abbreviation AlgHom.mulLeftRightMatrix_inv
  signature: :
  body: ∑ ⟨⟨i, j⟩, k, l⟩ : (n × n) × n × n,
    f (single j k 1) i l • (single i j 1) otimesₜ[R] op (single k l 1)
  map_add' f1 f2 := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' r f := by simp [mul_smul, Finset.smul_sum]

中文:
缩写 AlgHom.mulLeftRightMatrix_inv
  签名: :
  定义体: ∑ ⟨⟨i, j⟩, k, l⟩ : (n × n) × n × n,
    f (single j k 1) i l • (single i j 1) otimesₜ[R] op (single k l 1)
  map_add' f1 f2 := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' r f := by simp [mul_smul, Finset.smul_sum]
-/
abbrev AlgHom.mulLeftRightMatrix_inv :
    Module.End R (Matrix n n R) ->ₗ[R] Matrix n n R otimes[R] (Matrix n n R)ᵐᵒᵖ where
  toFun f := ∑ ⟨⟨i, j⟩, k, l⟩ : (n × n) × n × n,
    f (single j k 1) i l • (single i j 1) otimesₜ[R] op (single k l 1)
  map_add' f1 f2 := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' r f := by simp [mul_smul, Finset.smul_sum]

/--
lemma `AlgHom.mulLeftRightMatrix.inv_comp` / 引理 `AlgHom.mulLeftRightMatrix.inv_comp`

English:
lemma AlgHom.mulLeftRightMatrix.inv_comp
  proof: ((Matrix.stdBasis _ _ _).tensorProduct ((Matrix.stdBasis _ _ _).map (opLinearEquiv ..))).ext
  fun ⟨⟨i0, j0⟩, k0, l0⟩ => by
    simp [stdBasis_eq_single, ite_and, Fintype.sum_prod_type,
      mulLeftRight_apply, single, Matrix.mul_apply]

中文:
引理 AlgHom.mulLeftRightMatrix.inv_comp
  证明: ((Matrix.stdBasis _ _ _).tensorProduct ((Matrix.stdBasis _ _ _).map (opLinearEquiv ..))).ext
  fun ⟨⟨i0, j0⟩, k0, l0⟩ => by
    simp [stdBasis_eq_single, ite_and, Fintype.sum_prod_type,
      mulLeftRight_apply, single, Matrix.mul_apply]

Depends on / 依赖: Fintype, Fintype.sum_prod_type, Matrix, Matrix.mul_apply, Matrix.stdBasis, ite_and, mulLeftRight_apply, mul_apply, opLinearEquiv, single, stdBasis, stdBasis_eq_single, sum_prod_type, tensorProduct
-/
lemma AlgHom.mulLeftRightMatrix.inv_comp :
    (AlgHom.mulLeftRightMatrix_inv R n).comp
    (AlgHom.mulLeftRight R (Matrix n n R)).toLinearMap = .id :=
  ((Matrix.stdBasis _ _ _).tensorProduct ((Matrix.stdBasis _ _ _).map (opLinearEquiv ..))).ext
  fun ⟨⟨i0, j0⟩, k0, l0⟩ => by
    simp [stdBasis_eq_single, ite_and, Fintype.sum_prod_type,
      mulLeftRight_apply, single, Matrix.mul_apply]

/--
lemma `AlgHom.mulLeftRightMatrix.comp_inv` / 引理 `AlgHom.mulLeftRightMatrix.comp_inv`

English:
lemma AlgHom.mulLeftRightMatrix.comp_inv
  proof: by
  ext f : 1
  apply (Matrix.stdBasis _ _ _).ext
  intro ⟨i, j⟩
  simp only [LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply, map_sum,
    map_smul, stdBasis_eq_single, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.smul_apply, LinearMap.id_coe, id_eq]
  ext k l
  simp

中文:
引理 AlgHom.mulLeftRightMatrix.comp_inv
  证明: by
  ext f : 1
  apply (Matrix.stdBasis _ _ _).ext
  intro ⟨i, j⟩
  simp only [LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply, map_sum,
    map_smul, stdBasis_eq_single, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.smul_apply, LinearMap.id_coe, id_eq]
  ext k l
  simp

Depends on / 依赖: AddHom, AddHom.coe_mk, Finset, Finset.sum_apply, Fintype, Fintype.sum_prod_type, Function, Function.comp_apply, LinearMap, LinearMap.coe_comp, LinearMap.coe_mk, LinearMap.coe_sum, LinearMap.id_coe, LinearMap.smul_apply, Matrix, Matrix.mul_apply, Matrix.stdBasis, coe_comp, coe_mk, coe_sum
-/
lemma AlgHom.mulLeftRightMatrix.comp_inv :
    (AlgHom.mulLeftRight R (Matrix n n R)).toLinearMap.comp
    (AlgHom.mulLeftRightMatrix_inv R n) = .id := by
  ext f : 1
  apply (Matrix.stdBasis _ _ _).ext
  intro ⟨i, j⟩
  simp only [LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply, map_sum,
    map_smul, stdBasis_eq_single, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.smul_apply, LinearMap.id_coe, id_eq]
  ext k l
  simp [sum_apply, Matrix.mul_apply, single, Fintype.sum_prod_type, ite_and]

namespace IsAzumaya

/--
theorem `matrix` / 定理 `matrix`

English:
theorem matrix
  given: [Nonempty n]
  statement: IsAzumaya R (Matrix n n R) where
  proof: by nontriviality R; exact eq_of_smul_eq_smul
  bij := Function.bijective_iff_has_inverse.mpr
    ⟨AlgHom.mulLeftRightMatrix_inv R n,
    DFunLike.congr_fun (AlgHom.mulLeftRightMatrix.inv_comp R n),
    DFunLike.congr_fun (AlgHom.mulLeftRightMatrix.comp_inv R n)⟩

中文:
定理 matrix
  条件: [Nonempty n]
  结论: IsAzumaya R (Matrix n n R) where
  证明: by nontriviality R; exact eq_of_smul_eq_smul
  bij := Function.bijective_iff_has_inverse.mpr
    ⟨AlgHom.mulLeftRightMatrix_inv R n,
    DFunLike.congr_fun (AlgHom.mulLeftRightMatrix.inv_comp R n),
    DFunLike.congr_fun (AlgHom.mulLeftRightMatrix.comp_inv R n)⟩

Depends on / 依赖: AlgHom, AlgHom.mulLeftRightMatrix.comp_inv, AlgHom.mulLeftRightMatrix.inv_comp, AlgHom.mulLeftRightMatrix_inv, DFunLike, DFunLike.congr_fun, Function, Function.bijective_iff_has_inverse.mpr, bijective_iff_has_inverse, comp_inv, congr_fun, eq_of_smul_eq_smul, inv_comp, mulLeftRightMatrix, mulLeftRightMatrix_inv, nontriviality
-/
theorem matrix [Nonempty n] : IsAzumaya R (Matrix n n R) where
  eq_of_smul_eq_smul := by nontriviality R; exact eq_of_smul_eq_smul
  bij := Function.bijective_iff_has_inverse.mpr
    ⟨AlgHom.mulLeftRightMatrix_inv R n,
    DFunLike.congr_fun (AlgHom.mulLeftRightMatrix.inv_comp R n),
    DFunLike.congr_fun (AlgHom.mulLeftRightMatrix.comp_inv R n)⟩

end IsAzumaya

end
