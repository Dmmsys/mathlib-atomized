/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Tensor products of products

This file shows that taking `TensorProduct`s commutes with taking `Prod`s in both arguments.

## Main results

* `TensorProduct.prodLeft`
* `TensorProduct.prodRight`

## Notes

See `Mathlib/LinearAlgebra/TensorProduct/Pi.lean` for arbitrary products.

-/

@[expose] public section

variable (R S M₁ M₂ M₃ : Type*)

namespace TensorProduct

variable [CommSemiring R] [Semiring S] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Algebra R S]
variable [Module R M₁] [Module S M₁] [IsScalarTower R S M₁] [Module R M₂] [Module R M₃]

attribute [ext] TensorProduct.ext

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `prodRight` / `prodRight` 的定义

English:
definition prodRight
  signature: : M₁ otimes[R] (M₂ × M₃) ≃ₗ[S] (M₁ otimes[R] M₂) × (M₁ otimes[R] M₃)
  body: LinearEquiv.ofLinearMap
    (TensorProduct.AlgebraTensorModule.lift <|
      LinearMap.prodMapLinear R M₂ M₃ (M₁ otimes[R] M₂) (M₁ otimes[R] M₃) S ∘ₗ
        LinearMap.prod (AlgebraTensorModule.mk R S M₁ M₂) (AlgebraTensorModule.mk R S M₁ M₃))
    (LinearMap.coprod
      (AlgebraTensorModule.lTensor

中文:
定义 prodRight
  签名: : M₁ otimes[R] (M₂ × M₃) ≃ₗ[S] (M₁ otimes[R] M₂) × (M₁ otimes[R] M₃)
  定义体: LinearEquiv.ofLinearMap
    (TensorProduct.AlgebraTensorModule.lift <|
      LinearMap.prodMapLinear R M₂ M₃ (M₁ otimes[R] M₂) (M₁ otimes[R] M₃) S ∘ₗ
        LinearMap.prod (AlgebraTensorModule.mk R S M₁ M₂) (AlgebraTensorModule.mk R S M₁ M₃))
    (LinearMap.coprod
      (AlgebraTensorModule.lTensor

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.lTensor, AlgebraTensorModule.mk, LinearEquiv, LinearEquiv.ofLinearMap, LinearMap, LinearMap.coprod, LinearMap.inl, LinearMap.inr, LinearMap.prod, LinearMap.prodMapLinear, TensorProduct, TensorProduct.AlgebraTensorModule.lift, coprod, lTensor, ofLinearMap, otimes, prodMapLinear
-/
def prodRight : M₁ otimes[R] (M₂ × M₃) ≃ₗ[S] (M₁ otimes[R] M₂) × (M₁ otimes[R] M₃) :=
  LinearEquiv.ofLinearMap
    (TensorProduct.AlgebraTensorModule.lift <|
      LinearMap.prodMapLinear R M₂ M₃ (M₁ otimes[R] M₂) (M₁ otimes[R] M₃) S ∘ₗ
        LinearMap.prod (AlgebraTensorModule.mk R S M₁ M₂) (AlgebraTensorModule.mk R S M₁ M₃))
    (LinearMap.coprod
      (AlgebraTensorModule.lTensor _ _ <| LinearMap.inl _ _ _)
      (AlgebraTensorModule.lTensor _ _ <| LinearMap.inr _ _ _))
    (by ext <;> simp)
    (by ext <;> simp)

/--
theorem `prodRight_tmul` / 定理 `prodRight_tmul`

English:
theorem prodRight_tmul
  given: (m₁ : M₁) (m : M₂ × M₃)
  proof: rfl

中文:
定理 prodRight_tmul
  条件: (m₁ : M₁) (m : M₂ × M₃)
  证明: rfl
-/
@[simp] theorem prodRight_tmul (m₁ : M₁) (m : M₂ × M₃) :
    prodRight R S M₁ M₂ M₃ (m₁ otimesₜ m) = (m₁ otimesₜ m.1, m₁ otimesₜ m.2) :=
  rfl

/--
theorem `prodRight_symm_tmul` / 定理 `prodRight_symm_tmul`

English:
theorem prodRight_symm_tmul
  given: (m₁ : M₁) (m₂ : M₂) (m₃ : M₃)
  proof: (LinearEquiv.symm_apply_eq _).mpr rfl

中文:
定理 prodRight_symm_tmul
  条件: (m₁ : M₁) (m₂ : M₂) (m₃ : M₃)
  证明: (LinearEquiv.symm_apply_eq _).mpr rfl
-/
@[simp] theorem prodRight_symm_tmul (m₁ : M₁) (m₂ : M₂) (m₃ : M₃) :
    (prodRight R S M₁ M₂ M₃).symm (m₁ otimesₜ m₂, m₁ otimesₜ m₃) = (m₁ otimesₜ (m₂, m₃)) :=
  (LinearEquiv.symm_apply_eq _).mpr rfl

variable [Module S M₂] [IsScalarTower R S M₂]

/--
Definition of `prodLeft` / `prodLeft` 的定义

English:
definition prodLeft
  signature: : (M₁ × M₂) otimes[R] M₃ ≃ₗ[S] (M₁ otimes[R] M₃) × (M₂ otimes[R] M₃)
  body: AddEquiv.toLinearEquiv (TensorProduct.comm _ _ _ ≪≫ₗ
      TensorProduct.prodRight R R _ _ _ ≪≫ₗ
      (TensorProduct.comm R _ _).prodCongr (TensorProduct.comm R _ _)).toAddEquiv
    fun c x => x.induction_on (by simp) (by simp [TensorProduct.smul_tmul']) (by simp_all)

中文:
定义 prodLeft
  签名: : (M₁ × M₂) otimes[R] M₃ ≃ₗ[S] (M₁ otimes[R] M₃) × (M₂ otimes[R] M₃)
  定义体: AddEquiv.toLinearEquiv (TensorProduct.comm _ _ _ ≪≫ₗ
      TensorProduct.prodRight R R _ _ _ ≪≫ₗ
      (TensorProduct.comm R _ _).prodCongr (TensorProduct.comm R _ _)).toAddEquiv
    fun c x => x.induction_on (by simp) (by simp [TensorProduct.smul_tmul']) (by simp_all)

Depends on / 依赖: AddEquiv, AddEquiv.toLinearEquiv, TensorProduct, TensorProduct.comm, TensorProduct.prodRight, TensorProduct.smul_tmul, induction_on, prodCongr, prodRight, smul_tmul, toAddEquiv, toLinearEquiv, x.induction_on
-/
def prodLeft : (M₁ × M₂) otimes[R] M₃ ≃ₗ[S] (M₁ otimes[R] M₃) × (M₂ otimes[R] M₃) :=
  AddEquiv.toLinearEquiv (TensorProduct.comm _ _ _ ≪≫ₗ
      TensorProduct.prodRight R R _ _ _ ≪≫ₗ
      (TensorProduct.comm R _ _).prodCongr (TensorProduct.comm R _ _)).toAddEquiv
    fun c x => x.induction_on (by simp) (by simp [TensorProduct.smul_tmul']) (by simp_all)

/--
theorem `prodLeft_tmul` / 定理 `prodLeft_tmul`

English:
theorem prodLeft_tmul
  given: (m₁ : M₁) (m₂ : M₂) (m₃ : M₃)
  proof: rfl

中文:
定理 prodLeft_tmul
  条件: (m₁ : M₁) (m₂ : M₂) (m₃ : M₃)
  证明: rfl
-/
@[simp] theorem prodLeft_tmul (m₁ : M₁) (m₂ : M₂) (m₃ : M₃) :
    prodLeft R S M₁ M₂ M₃ ((m₁, m₂) otimesₜ m₃) = (m₁ otimesₜ m₃, m₂ otimesₜ m₃) :=
  rfl

/--
theorem `prodLeft_symm_tmul` / 定理 `prodLeft_symm_tmul`

English:
theorem prodLeft_symm_tmul
  given: (m₁ : M₁) (m₂ : M₂) (m₃ : M₃)
  proof: (LinearEquiv.symm_apply_eq _).mpr rfl

中文:
定理 prodLeft_symm_tmul
  条件: (m₁ : M₁) (m₂ : M₂) (m₃ : M₃)
  证明: (LinearEquiv.symm_apply_eq _).mpr rfl
-/
@[simp] theorem prodLeft_symm_tmul (m₁ : M₁) (m₂ : M₂) (m₃ : M₃) :
    (prodLeft R S M₁ M₂ M₃).symm (m₁ otimesₜ m₃, m₂ otimesₜ m₃) = ((m₁, m₂) otimesₜ m₃) :=
  (LinearEquiv.symm_apply_eq _).mpr rfl

end TensorProduct
