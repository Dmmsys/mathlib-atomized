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

/--
Definition of `opAlgEquiv` / `opAlgEquiv` 的定义

English:
definition opAlgEquiv
  signature: : Aᵐᵒᵖ otimes[R] Bᵐᵒᵖ ≃ₐ[S] (A otimes[R] B)ᵐᵒᵖ
  body: letI e₁ : Aᵐᵒᵖ otimes[R] Bᵐᵒᵖ ≃ₗ[S] (A otimes[R] B)ᵐᵒᵖ :=
    TensorProduct.AlgebraTensorModule.congr
      (opLinearEquiv S).symm (opLinearEquiv R).symm ≪≫ₗ opLinearEquiv S
  letI e₂ : A otimes[R] B ≃ₗ[S] (Aᵐᵒᵖ otimes[R] Bᵐᵒᵖ)ᵐᵒᵖ :=
    TensorProduct.AlgebraTensorModule.congr (opLinearEquiv S) (opLinearEquiv R) ≪≫ₗ opLinearEquiv S
  AlgEquiv.ofAlgHom
    (algHomOfLinearMapTensorProduct e₁.toLinearMap
      (fun a₁ a₂ b₁ b₂ => unop_injective (by with_unfolding_all rfl)) (unop_injective rfl))
    (AlgHom.opComm <| algHomOfLinearMapTensorProduct e₂.toLinearMap
      (fun a₁ a₂ b₁ b₂ => unop_injective (by with_unfolding_all rfl)) (unop_injective rfl))
    (AlgHom.op.symm.injective <| by ext <;> rfl) (by ext <;> rfl)

中文:
定义 opAlgEquiv
  签名: : Aᵐᵒᵖ otimes[R] Bᵐᵒᵖ ≃ₐ[S] (A otimes[R] B)ᵐᵒᵖ
  定义体: letI e₁ : Aᵐᵒᵖ otimes[R] Bᵐᵒᵖ ≃ₗ[S] (A otimes[R] B)ᵐᵒᵖ :=
    TensorProduct.AlgebraTensorModule.congr
      (opLinearEquiv S).symm (opLinearEquiv R).symm ≪≫ₗ opLinearEquiv S
  letI e₂ : A otimes[R] B ≃ₗ[S] (Aᵐᵒᵖ otimes[R] Bᵐᵒᵖ)ᵐᵒᵖ :=
    TensorProduct.AlgebraTensorModule.congr (opLinearEquiv S) (opLinearEquiv R) ≪≫ₗ opLinearEquiv S
  AlgEquiv.ofAlgHom
    (algHomOfLinearMapTensorProduct e₁.toLinearMap
      (fun a₁ a₂ b₁ b₂ => unop_injective (by with_unfolding_all rfl)) (unop_injective rfl))
    (AlgHom.opComm <| algHomOfLinearMapTensorProduct e₂.toLinearMap
      (fun a₁ a₂ b₁ b₂ => unop_injective (by with_unfolding_all rfl)) (unop_injective rfl))
    (AlgHom.op.symm.injective <| by ext <;> rfl) (by ext <;> rfl)

Depends on / 依赖: AlgEquiv, AlgEquiv.ofAlgHom, AlgHom, AlgHom.opComm, AlgebraTensorModule, TensorProduct, TensorProduct.AlgebraTensorModule.congr, algHomOfLinea, algHomOfLinearMapTensorProduct, ofAlgHom, opComm, opLinearEquiv, otimes, toLinearMap, unop_injective, with_unfolding_all
-/
def opAlgEquiv : Aᵐᵒᵖ otimes[R] Bᵐᵒᵖ ≃ₐ[S] (A otimes[R] B)ᵐᵒᵖ :=
  letI e₁ : Aᵐᵒᵖ otimes[R] Bᵐᵒᵖ ≃ₗ[S] (A otimes[R] B)ᵐᵒᵖ :=
    TensorProduct.AlgebraTensorModule.congr
      (opLinearEquiv S).symm (opLinearEquiv R).symm ≪≫ₗ opLinearEquiv S
  letI e₂ : A otimes[R] B ≃ₗ[S] (Aᵐᵒᵖ otimes[R] Bᵐᵒᵖ)ᵐᵒᵖ :=
    TensorProduct.AlgebraTensorModule.congr (opLinearEquiv S) (opLinearEquiv R) ≪≫ₗ opLinearEquiv S
  AlgEquiv.ofAlgHom
    (algHomOfLinearMapTensorProduct e₁.toLinearMap
      (fun a₁ a₂ b₁ b₂ => unop_injective (by with_unfolding_all rfl)) (unop_injective rfl))
    (AlgHom.opComm <| algHomOfLinearMapTensorProduct e₂.toLinearMap
      (fun a₁ a₂ b₁ b₂ => unop_injective (by with_unfolding_all rfl)) (unop_injective rfl))
    (AlgHom.op.symm.injective <| by ext <;> rfl) (by ext <;> rfl)

/--
theorem `opAlgEquiv_apply` / 定理 `opAlgEquiv_apply`

English:
theorem opAlgEquiv_apply
  given: (x : Aᵐᵒᵖ otimes[R] Bᵐᵒᵖ)
  proof: rfl

中文:
定理 opAlgEquiv_apply
  条件: (x : Aᵐᵒᵖ otimes[R] Bᵐᵒᵖ)
  证明: rfl
-/
theorem opAlgEquiv_apply (x : Aᵐᵒᵖ otimes[R] Bᵐᵒᵖ) :
    opAlgEquiv R S A B x =
      op (_root_.TensorProduct.map
        (opLinearEquiv R).symm.toLinearMap (opLinearEquiv R).symm.toLinearMap x) :=
  rfl

/--
theorem `opAlgEquiv_symm_apply` / 定理 `opAlgEquiv_symm_apply`

English:
theorem opAlgEquiv_symm_apply
  given: (x : (A otimes[R] B)ᵐᵒᵖ)
  proof: rfl

@[simp]

中文:
定理 opAlgEquiv_symm_apply
  条件: (x : (A otimes[R] B)ᵐᵒᵖ)
  证明: rfl

@[simp]
-/
theorem opAlgEquiv_symm_apply (x : (A otimes[R] B)ᵐᵒᵖ) :
    (opAlgEquiv R S A B).symm x =
      _root_.TensorProduct.map (opLinearEquiv R).toLinearMap (opLinearEquiv R).toLinearMap x.unop :=
  rfl

@[simp]
/--
theorem `opAlgEquiv_tmul` / 定理 `opAlgEquiv_tmul`

English:
theorem opAlgEquiv_tmul
  given: (a : Aᵐᵒᵖ) (b : Bᵐᵒᵖ)
  proof: rfl

@[simp]

中文:
定理 opAlgEquiv_tmul
  条件: (a : Aᵐᵒᵖ) (b : Bᵐᵒᵖ)
  证明: rfl

@[simp]
-/
theorem opAlgEquiv_tmul (a : Aᵐᵒᵖ) (b : Bᵐᵒᵖ) :
    opAlgEquiv R S A B (a otimesₜ[R] b) = op (a.unop otimesₜ b.unop) :=
  rfl

@[simp]
/--
theorem `opAlgEquiv_symm_tmul` / 定理 `opAlgEquiv_symm_tmul`

English:
theorem opAlgEquiv_symm_tmul
  given: (a : A) (b : B)
  proof: rfl

中文:
定理 opAlgEquiv_symm_tmul
  条件: (a : A) (b : B)
  证明: rfl
-/
theorem opAlgEquiv_symm_tmul (a : A) (b : B) :
    (opAlgEquiv R S A B).symm (op <| a otimesₜ[R] b) = op a otimesₜ op b :=
  rfl

end Algebra.TensorProduct
