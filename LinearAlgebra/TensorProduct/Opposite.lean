/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Algebra.Algebra.Opposite

/-! # `MulOpposite` distributes over `⊗`

The main result in this file is:

* `Algebra.TensorProduct.opAlgEquiv R S A B : Aᵐᵒᵖ ⊗[R] Bᵐᵒᵖ ≃ₐ[S] (A ⊗[R] B)ᵐᵒᵖ`
-/

@[expose] public section

open scoped TensorProduct

variable (R S A B : Type*)
variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]
variable [Algebra R S] [Algebra R A] [Algebra R B] [Algebra S A]
variable [IsScalarTower R S A]

namespace Algebra.TensorProduct

open MulOpposite

/-- `MulOpposite` distributes over `TensorProduct`. Note this is an `S`-algebra morphism, where
`A/S/R` is a tower of algebras. -/
/-
**Algebra.TensorProduct.opAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.TensorProd
uct`。
形式化陈述：opAlgEquiv : Aᵐᵒᵖ otimes[R] Bᵐᵒᵖ ≃ₐ[S] (A otimes[R] B)ᵐᵒᵖ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`MulOpposite` distributes over `TensorProduct`. Note this is an `S`-algebra morp
hism, where
`A/S/R` is a tower of algebras.
-/
def opAlgEquiv : Aᵐᵒᵖ ⊗[R] Bᵐᵒᵖ ≃ₐ[S] (A ⊗[R] B)ᵐᵒᵖ :=
  letI e₁ : Aᵐᵒᵖ ⊗[R] Bᵐᵒᵖ ≃ₗ[S] (A ⊗[R] B)ᵐᵒᵖ :=
    TensorProduct.AlgebraTensorModule.congr
      (opLinearEquiv S).symm (opLinearEquiv R).symm ≪≫ₗ opLinearEquiv S
  letI e₂ : A ⊗[R] B ≃ₗ[S] (Aᵐᵒᵖ ⊗[R] Bᵐᵒᵖ)ᵐᵒᵖ :=
    TensorProduct.AlgebraTensorModule.congr (opLinearEquiv S) (opLinearEquiv R) ≪≫ₗ opLinearEquiv S
  AlgEquiv.ofAlgHom
    (algHomOfLinearMapTensorProduct e₁.toLinearMap
      (fun a₁ a₂ b₁ b₂ => unop_injective (by with_unfolding_all rfl)) (unop_injective rfl))
    (AlgHom.opComm <| algHomOfLinearMapTensorProduct e₂.toLinearMap
      (fun a₁ a₂ b₁ b₂ => unop_injective (by with_unfolding_all rfl)) (unop_injective rfl))
    (AlgHom.op.symm.injective <| by ext <;> rfl) (by ext <;> rfl)
/-
**Algebra.TensorProduct.opAlgEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Tens
orProduct`。
形式化陈述：opAlgEquiv_apply (x : Aᵐᵒᵖ otimes[R] Bᵐᵒᵖ) : opAlgEquiv R S A B x = op (_r
oot_.TensorProduct.map (opLinearEquiv R).symm.toLinearMap (opLinearEquiv R).symm
.toLinearMap x)
参数：x : Aᵐᵒᵖ otimes[R] Bᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem opAlgEquiv_apply (x : Aᵐᵒᵖ ⊗[R] Bᵐᵒᵖ) :
    opAlgEquiv R S A B x =
      op (_root_.TensorProduct.map
        (opLinearEquiv R).symm.toLinearMap (opLinearEquiv R).symm.toLinearMap x) :=
  rfl
/-
**Algebra.TensorProduct.opAlgEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
.TensorProduct`。
形式化陈述：opAlgEquiv_symm_apply (x : (A otimes[R] B)ᵐᵒᵖ) : (opAlgEquiv R S A B).symm
 x = _root_.TensorProduct.map (opLinearEquiv R).toLinearMap (opLinearEquiv R).to
LinearMap x.unop
参数：x : (A otimes[R] B)ᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem opAlgEquiv_symm_apply (x : (A ⊗[R] B)ᵐᵒᵖ) :
    (opAlgEquiv R S A B).symm x =
      _root_.TensorProduct.map (opLinearEquiv R).toLinearMap (opLinearEquiv R).toLinearMap x.unop :=
  rfl

@[simp]
/-
**Algebra.TensorProduct.opAlgEquiv_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Tenso
rProduct`。
形式化陈述：opAlgEquiv_tmul (a : Aᵐᵒᵖ) (b : Bᵐᵒᵖ) : opAlgEquiv R S A B (a otimesₜ[R] b
) = op (a.unop otimesₜ b.unop)
参数：a : Aᵐᵒᵖ；b : Bᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem opAlgEquiv_tmul (a : Aᵐᵒᵖ) (b : Bᵐᵒᵖ) :
    opAlgEquiv R S A B (a ⊗ₜ[R] b) = op (a.unop ⊗ₜ b.unop) :=
  rfl

@[simp]
/-
**Algebra.TensorProduct.opAlgEquiv_symm_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.
TensorProduct`。
形式化陈述：opAlgEquiv_symm_tmul (a : A) (b : B) : (opAlgEquiv R S A B).symm (op <| a 
otimesₜ[R] b) = op a otimesₜ op b
参数：a : A；b : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem opAlgEquiv_symm_tmul (a : A) (b : B) :
    (opAlgEquiv R S A B).symm (op <| a ⊗ₜ[R] b) = op a ⊗ₜ op b :=
  rfl

end Algebra.TensorProduct

