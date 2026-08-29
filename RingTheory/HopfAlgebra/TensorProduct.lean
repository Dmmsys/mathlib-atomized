/-
Copyright (c) 2024 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston, Andrew Yang
-/
module

public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Bialgebra.TensorProduct

/-!
# Tensor products of Hopf algebras

We define the Hopf algebra instance on the tensor product of two Hopf algebras.

-/

@[expose] public section

open Coalgebra HopfAlgebra

namespace TensorProduct

variable {R S A B : Type*} [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]
    [Algebra R S] [HopfAlgebra R A] [HopfAlgebra S B] [Algebra R B]
    [IsScalarTower R S B]

set_option backward.defeqAttrib.useBackward true in
noncomputable
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HopfAlgebra S (B otimes[R] A)
  body: AlgebraTensorModule.map (HopfAlgebra.antipode S) (HopfAlgebra.antipode R)
  mul_antipode_rTensor_comul := by
    ext x y
    convert! congr($(mul_antipode_rTensor_comul_apply (R := S) x) otimesₜ[R]
 (mul_antipode_rTensor_comul_apply (R := R) y)) using 1
    · dsimp
      hopf_tensor_induction comul 

中文:
实例 :
  签名: Hopf代数 S (B otimes[R] A)
  定义体: AlgebraTensorModule.map (HopfAlgebra.antipode S) (HopfAlgebra.antipode R)
  mul_antipode_rTensor_comul := by
    ext x y
    convert! congr($(mul_antipode_rTensor_comul_apply (R := S) x) otimesₜ[R]
 (mul_antipode_rTensor_comul_apply (R := R) y)) using 1
    · dsimp
      hopf_tensor_induction comul 

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.map, HopfAlgebra, HopfAlgebra.antipode, antipode
-/
instance : HopfAlgebra S (B otimes[R] A) where
  antipode := AlgebraTensorModule.map (HopfAlgebra.antipode S) (HopfAlgebra.antipode R)
  mul_antipode_rTensor_comul := by
    ext x y
    convert! congr($(mul_antipode_rTensor_comul_apply (R := S) x) otimesₜ[R]
 (mul_antipode_rTensor_comul_apply (R := R) y)) using 1
    · dsimp
      hopf_tensor_induction comul (R := S) x with x₁ x₂
      hopf_tensor_induction comul (R := R) y with y₁ y₂
      simp
    · dsimp [Algebra.TensorProduct.one_def]
      simp [Algebra.algebraMap_eq_smul_one, smul_tmul']
  mul_antipode_lTensor_comul := by
    ext x y
    convert! congr($(mul_antipode_lTensor_comul_apply (R := S) x) otimesₜ[R]
 (mul_antipode_lTensor_comul_apply (R := R) y)) using 1
    · dsimp [Algebra.TensorProduct.one_def]
      hopf_tensor_induction comul (R := S) x with x₁ x₂
      hopf_tensor_induction comul (R := R) y with y₁ y₂
      simp
    · dsimp [Algebra.TensorProduct.one_def]
      simp [Algebra.algebraMap_eq_smul_one, smul_tmul']

@[simp]
/--
theorem `antipode_def` / 定理 `antipode_def`

English:
theorem antipode_def
  proof: rfl

中文:
定理 antipode_def
  证明: rfl

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.map, antipode, otimes
-/
theorem antipode_def :
    antipode S (A := B otimes[R] A) = AlgebraTensorModule.map (antipode S) (antipode R) := rfl

end TensorProduct
