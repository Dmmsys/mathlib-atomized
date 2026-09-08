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
/-- Tensor products distribute over a product on the right. -/
/-
**TensorProduct.prodRight** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：prodRight : M₁ otimes[R] (M₂ × M₃) ≃ₗ[S] (M₁ otimes[R] M₂) × (M₁ otimes[R]
 M₃)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…

--- 原说明 ---
Tensor products distribute over a product on the right.
-/
def prodRight : M₁ ⊗[R] (M₂ × M₃) ≃ₗ[S] (M₁ ⊗[R] M₂) × (M₁ ⊗[R] M₃) :=
  LinearEquiv.ofLinearMap
    (TensorProduct.AlgebraTensorModule.lift <|
      LinearMap.prodMapLinear R M₂ M₃ (M₁ ⊗[R] M₂) (M₁ ⊗[R] M₃) S ∘ₗ
        LinearMap.prod (AlgebraTensorModule.mk R S M₁ M₂) (AlgebraTensorModule.mk R S M₁ M₃))
    (LinearMap.coprod
      (AlgebraTensorModule.lTensor _ _ <| LinearMap.inl _ _ _)
      (AlgebraTensorModule.lTensor _ _ <| LinearMap.inr _ _ _))
    (by ext <;> simp)
    (by ext <;> simp)
/-
**TensorProduct.prodRight_tmul** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ (R : Type u_1) (S : Type u_2) (M₁ : Type u_3) (M₂ : Type u_4) (M₃ : Type
 u_5) [inst : CommSemiring R]   [inst_1 : Semiring S] [inst_2 : AddCommMonoid M₁
] [inst_3 : AddCommMonoid M₂] [inst_4 : AddCommMonoid M₃]   [inst_5 : Algebra R 
S] [inst_6 : _root_.Module R M₁] [inst_7 : _root_.Module S M₁] [inst_8 : IsScala
rTower R S M₁]   [inst_9 : _root_.Module R M₂] [inst_10 : _root_.Module R M₃] (m
₁ : M₁) (m : M₂ × M₃),   (TensorProduct.prodRight R S M₁ M₂ M₃) (m₁ ⊗ₜ[R] m) = (
m₁ ⊗ₜ[R] m.1, m₁ ⊗ₜ[R] m.2)
参数：R : Type u_1；S : Type u_2；M₁ : Type u_3；M₂ : Type u_4；M₃ : Type u_5；m₁ : M₁；m
 : M₂ × M₃；TensorProduct.prodRight R S M₁ M₂ M₃；m₁ ⊗ₜ[R] m；m₁ ⊗ₜ[R] m.1, m₁ ⊗ₜ[R
] m.2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
@[simp] theorem prodRight_tmul (m₁ : M₁) (m : M₂ × M₃) :
    prodRight R S M₁ M₂ M₃ (m₁ ⊗ₜ m) = (m₁ ⊗ₜ m.1, m₁ ⊗ₜ m.2) :=
  rfl
/-
**TensorProduct.prodRight_symm_tmul** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ (R : Type u_1) (S : Type u_2) (M₁ : Type u_3) (M₂ : Type u_4) (M₃ : Type
 u_5) [inst : CommSemiring R]   [inst_1 : Semiring S] [inst_2 : AddCommMonoid M₁
] [inst_3 : AddCommMonoid M₂] [inst_4 : AddCommMonoid M₃]   [inst_5 : Algebra R 
S] [inst_6 : _root_.Module R M₁] [inst_7 : _root_.Module S M₁] [inst_8 : IsScala
rTower R S M₁]   [inst_9 : _root_.Module R M₂] [inst_10 : _root_.Module R M₃] (m
₁ : M₁) (m₂ : M₂) (m₃ : M₃),   (TensorProduct.prodRight R S M₁ M₂ M₃).symm (m₁ ⊗
ₜ[R] m₂, m₁ ⊗ₜ[R] m₃) = m₁ ⊗ₜ[R] (m₂, m₃)
参数：R : Type u_1；S : Type u_2；M₁ : Type u_3；M₂ : Type u_4；M₃ : Type u_5；m₁ : M₁；m
₂ : M₂；m₃ : M₃；TensorProduct.prodRight R S M₁ M₂ M₃；m₁ ⊗ₜ[R] m₂, m₁ ⊗ₜ[R] m₃；m₂,
 m₃。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `LinearEquiv.symm_apply_eq`：symm_apply_eq {x y} : e.symm x = y ↔ x = e y
-/
@[simp] theorem prodRight_symm_tmul (m₁ : M₁) (m₂ : M₂) (m₃ : M₃) :
    (prodRight R S M₁ M₂ M₃).symm (m₁ ⊗ₜ m₂, m₁ ⊗ₜ m₃) = (m₁ ⊗ₜ (m₂, m₃)) :=
  (LinearEquiv.symm_apply_eq _).mpr rfl

variable [Module S M₂] [IsScalarTower R S M₂]

/-- Tensor products distribute over a product on the left . -/
/-
**TensorProduct.prodLeft** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：prodLeft : (M₁ × M₂) otimes[R] M₃ ≃ₗ[S] (M₁ otimes[R] M₃) × (M₂ otimes[R] 
M₃)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…

--- 原说明 ---
Tensor products distribute over a product on the left .
-/
def prodLeft : (M₁ × M₂) ⊗[R] M₃ ≃ₗ[S] (M₁ ⊗[R] M₃) × (M₂ ⊗[R] M₃) :=
  AddEquiv.toLinearEquiv (TensorProduct.comm _ _ _ ≪≫ₗ
      TensorProduct.prodRight R R _ _ _ ≪≫ₗ
      (TensorProduct.comm R _ _).prodCongr (TensorProduct.comm R _ _)).toAddEquiv
    fun c x ↦ x.induction_on (by simp) (by simp [TensorProduct.smul_tmul']) (by simp_all)
/-
**TensorProduct.prodLeft_tmul** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ (R : Type u_1) (S : Type u_2) (M₁ : Type u_3) (M₂ : Type u_4) (M₃ : Type
 u_5) [inst : CommSemiring R]   [inst_1 : Semiring S] [inst_2 : AddCommMonoid M₁
] [inst_3 : AddCommMonoid M₂] [inst_4 : AddCommMonoid M₃]   [inst_5 : Algebra R 
S] [inst_6 : _root_.Module R M₁] [inst_7 : _root_.Module S M₁] [inst_8 : IsScala
rTower R S M₁]   [inst_9 : _root_.Module R M₂] [inst_10 : _root_.Module R M₃] [i
nst_11 : _root_.Module S M₂]   [inst_12 : IsScalarTower R S M₂] (m₁ : M₁) (m₂ : 
M₂) (m₃ : M₃),   (TensorProduct.prodLeft R S M₁ M₂ M₃) ((m₁, m₂) ⊗ₜ[R] m₃) = (m₁
 ⊗ₜ[R] m₃, m₂ ⊗ₜ[R] m₃)
参数：R : Type u_1；S : Type u_2；M₁ : Type u_3；M₂ : Type u_4；M₃ : Type u_5；m₁ : M₁；m
₂ : M₂；m₃ : M₃；TensorProduct.prodLeft R S M₁ M₂ M₃；(m₁, m₂) ⊗ₜ[R] m₃；m₁ ⊗ₜ[R] m₃
, m₂ ⊗ₜ[R] m₃。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
@[simp] theorem prodLeft_tmul (m₁ : M₁) (m₂ : M₂) (m₃ : M₃) :
    prodLeft R S M₁ M₂ M₃ ((m₁, m₂) ⊗ₜ m₃) = (m₁ ⊗ₜ m₃, m₂ ⊗ₜ m₃) :=
  rfl
/-
**TensorProduct.prodLeft_symm_tmul** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ (R : Type u_1) (S : Type u_2) (M₁ : Type u_3) (M₂ : Type u_4) (M₃ : Type
 u_5) [inst : CommSemiring R]   [inst_1 : Semiring S] [inst_2 : AddCommMonoid M₁
] [inst_3 : AddCommMonoid M₂] [inst_4 : AddCommMonoid M₃]   [inst_5 : Algebra R 
S] [inst_6 : _root_.Module R M₁] [inst_7 : _root_.Module S M₁] [inst_8 : IsScala
rTower R S M₁]   [inst_9 : _root_.Module R M₂] [inst_10 : _root_.Module R M₃] [i
nst_11 : _root_.Module S M₂]   [inst_12 : IsScalarTower R S M₂] (m₁ : M₁) (m₂ : 
M₂) (m₃ : M₃),   (TensorProduct.prodLeft R S M₁ M₂ M₃).symm (m₁ ⊗ₜ[R] m₃, m₂ ⊗ₜ[
R] m₃) = (m₁, m₂) ⊗ₜ[R] m₃
参数：R : Type u_1；S : Type u_2；M₁ : Type u_3；M₂ : Type u_4；M₃ : Type u_5；m₁ : M₁；m
₂ : M₂；m₃ : M₃；TensorProduct.prodLeft R S M₁ M₂ M₃；m₁ ⊗ₜ[R] m₃, m₂ ⊗ₜ[R] m₃；m₁, 
m₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `LinearEquiv.symm_apply_eq`：symm_apply_eq {x y} : e.symm x = y ↔ x = e y
-/
@[simp] theorem prodLeft_symm_tmul (m₁ : M₁) (m₂ : M₂) (m₃ : M₃) :
    (prodLeft R S M₁ M₂ M₃).symm (m₁ ⊗ₜ m₃, m₂ ⊗ₜ m₃) = ((m₁, m₂) ⊗ₜ m₃) :=
  (LinearEquiv.symm_apply_eq _).mpr rfl

end TensorProduct

