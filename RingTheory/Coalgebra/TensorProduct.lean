/-
Copyright (c) 2024 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston, Andrew Yang
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Coalgebra.Equiv

import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.Algebra.Algebra.Bilinear

/-!
# Tensor products of coalgebras

Suppose `S` is an `R`-algebra. Given an `S`-coalgebra `A` and `R`-coalgebra `B`, we can define
a natural comultiplication map `Δ : A ⊗[R] B → (A ⊗[R] B) ⊗[S] (A ⊗[R] B)`
and counit map `ε : A ⊗[R] B → S` induced by the comultiplication and counit maps of `A` and `B`.

In this file we show that `Δ, ε` satisfy the axioms of a coalgebra, and also define other data
in the monoidal structure on `R`-coalgebras, like the tensor product of two coalgebra morphisms
as a coalgebra morphism.

In particular, when `R = S` we get tensor products of coalgebras, and when `A = S` we get
the base change `S ⊗[R] B` as an `S`-coalgebra.

-/

@[expose] public section

open TensorProduct

variable {R S A B : Type*} [CommSemiring R] [CommSemiring S] [AddCommMonoid A] [AddCommMonoid B]
    [Algebra R S] [Module R A] [Module S A] [Module R B] [IsScalarTower R S A]

namespace TensorProduct

open Coalgebra

section CoalgebraStruct
variable [CoalgebraStruct R B] [CoalgebraStruct S A]

noncomputable
/-
**TensorProduct.instCoalgebraStruct** 是 Mathlib 中的一个实例，位于命名空间 `TensorProduct`。
形式化陈述：instCoalgebraStruct : CoalgebraStruct S (A otimes[R] B) where comul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCoalgebraStruct : CoalgebraStruct S (A ⊗[R] B) where
  comul :=
    AlgebraTensorModule.tensorTensorTensorComm R S R S A A B B ∘ₗ
      AlgebraTensorModule.map comul comul
  counit := AlgebraTensorModule.rid R S S ∘ₗ AlgebraTensorModule.map counit counit
/-
**TensorProduct.comul_def** 是 Mathlib 中的一个引理，位于命名空间 `TensorProduct`。
形式化陈述：comul_def : Coalgebra.comul (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
lemma comul_def :
    Coalgebra.comul (R := S) (A := A ⊗[R] B) =
      AlgebraTensorModule.tensorTensorTensorComm R S R S A A B B ∘ₗ
        AlgebraTensorModule.map Coalgebra.comul Coalgebra.comul :=
  rfl
/-
**TensorProduct.counit_def** 是 Mathlib 中的一个引理，位于命名空间 `TensorProduct`。
形式化陈述：counit_def : Coalgebra.counit (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
lemma counit_def :
    Coalgebra.counit (R := S) (A := A ⊗[R] B) =
      AlgebraTensorModule.rid R S S ∘ₗ AlgebraTensorModule.map counit counit :=
  rfl

@[simp]
/-
**TensorProduct.comul_tmul** 是 Mathlib 中的一个引理，位于命名空间 `TensorProduct`。
形式化陈述：comul_tmul (x : A) (y : B) : comul (x otimesₜ y) = AlgebraTensorModule.ten
sorTensorTensorComm R S R S A A B B (comul x otimesₜ comul y)
参数：x : A；y : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
lemma comul_tmul (x : A) (y : B) :
    comul (x ⊗ₜ y) =
      AlgebraTensorModule.tensorTensorTensorComm R S R S A A B B (comul x ⊗ₜ comul y) := rfl

@[simp]
/-
**TensorProduct.counit_tmul** 是 Mathlib 中的一个引理，位于命名空间 `TensorProduct`。
形式化陈述：counit_tmul (x : A) (y : B) : counit (R
参数：x : A；y : B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
lemma counit_tmul (x : A) (y : B) :
    counit (R := S) (x ⊗ₜ[R] y) = counit (R := R) y • counit (R := S) x := rfl

end CoalgebraStruct

variable [Coalgebra R B] [Coalgebra S A]

open Lean.Parser.Tactic in
/-- `hopf_tensor_induction x with x₁ x₂` attempts to replace `x` by
`x₁ ⊗ₜ x₂` via linearity. This is an implementation detail that is used to set up tensor products
of coalgebras, bialgebras, and hopf algebras, and shouldn't be relied on downstream. -/
scoped macro "hopf_tensor_induction " var:elimTarget "with " var₁:ident var₂:ident : tactic =>
  `(tactic|
    (induction $var with
      | zero =>
        -- avoid the more general `map_zero` for performance reasons
        simp only [tmul_zero, LinearEquiv.map_zero, LinearMap.map_zero,
          zero_tmul, zero_mul, mul_zero]
      | add _ _ h₁ h₂ =>
        -- avoid the more general `map_add` for performance reasons
        simp only [LinearEquiv.map_add, LinearMap.map_add,
          tmul_add, add_tmul, add_mul, mul_add, h₁, h₂]
      | tmul $var₁ $var₂ => ?_))

set_option backward.defeqAttrib.useBackward true in
set_option backward.privateInPublic true in
/-
**TensorProduct.coassoc** 是 Mathlib 中的一个引理，位于命名空间 `TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma coassoc :
    TensorProduct.assoc S (A ⊗[R] B) (A ⊗[R] B) (A ⊗[R] B) ∘ₗ
      (comul (R := S) (A := (A ⊗[R] B))).rTensor (A ⊗[R] B) ∘ₗ
        (comul (R := S) (A := (A ⊗[R] B))) =
    (comul (R := S) (A := (A ⊗[R] B))).lTensor (A ⊗[R] B) ∘ₗ
      (comul (R := S) (A := (A ⊗[R] B))) := by
  ext x y
  let F : A ⊗[S] (A ⊗[S] A) ⊗[R] (B ⊗[R] (B ⊗[R] B)) ≃ₗ[S]
    A ⊗[R] B ⊗[S] (A ⊗[R] B ⊗[S] (A ⊗[R] B)) :=
    AlgebraTensorModule.tensorTensorTensorComm _ _ _ _ _ _ _ _ ≪≫ₗ
      AlgebraTensorModule.congr (.refl _ _)
        (AlgebraTensorModule.tensorTensorTensorComm _ _ _ _ _ _ _ _)
  let F' : A ⊗[S] (A ⊗[S] A) ⊗[R] (B ⊗[R] (B ⊗[R] B)) →ₗ[S]
      A ⊗[R] B ⊗[S] (A ⊗[R] B ⊗[S] (A ⊗[R] B)) :=
    TensorProduct.mapOfCompatibleSMul .. ∘ₗ
        TensorProduct.map .id (TensorProduct.mapOfCompatibleSMul ..) ∘ₗ F.toLinearMap
  convert! congr(F ($(Coalgebra.coassoc_apply x) ⊗ₜ[R] $(Coalgebra.coassoc_apply y))) using 1
  · dsimp
    hopf_tensor_induction comul (R := S) x with x₁ x₂
    hopf_tensor_induction comul (R := R) y with y₁ y₂
    dsimp
    hopf_tensor_induction comul (R := S) x₁ with x₁₁ x₁₂
    hopf_tensor_induction comul (R := R) y₁ with y₁₁ y₁₂
    rfl
  · dsimp
    hopf_tensor_induction comul (R := S) x with x₁ x₂
    hopf_tensor_induction comul (R := R) y with y₁ y₂
    dsimp
    hopf_tensor_induction comul (R := S) x₂ with x₂₁ x₂₂
    hopf_tensor_induction comul (R := R) y₂ with y₂₁ y₂₂
    rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
noncomputable
/-
**TensorProduct.instCoalgebra** 是 Mathlib 中的一个实例，位于命名空间 `TensorProduct`。
形式化陈述：instCoalgebra : Coalgebra S (A otimes[R] B) where coassoc
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.RingTheory.Coalgebra.TensorProduct.0.TensorProduct.coas
soc`：∀ {R : Type u_1} {S : Type u_2} {A : Type u_3} {B : Type u_4} [inst : CommS
emiring R] [inst_1 : CommSemiring S]   [inst_2 : AddCommMonoid A]…
-/
instance instCoalgebra : Coalgebra S (A ⊗[R] B) where
  coassoc := coassoc (R := R)
  rTensor_counit_comp_comul := by
    ext x y
    convert!
      congr((TensorProduct.lid S _).symm
        (TensorProduct.lid _ _ $(rTensor_counit_comul (R := S) x) ⊗ₜ[R]
          TensorProduct.lid _ _ $(rTensor_counit_comul (R := R) y)))
    · dsimp
      hopf_tensor_induction comul (R := S) x with x₁ x₂
      hopf_tensor_induction comul (R := R) y with y₁ y₂
      apply (TensorProduct.lid S _).injective
      dsimp
      rw [tmul_smul, smul_assoc, one_smul, smul_tmul']
    · dsimp
      simp only [one_smul]
  lTensor_counit_comp_comul := by
    ext x y
    convert!
      congr((TensorProduct.rid S _).symm
        (TensorProduct.rid _ _ $(lTensor_counit_comul (R := S) x) ⊗ₜ[R]
          TensorProduct.rid _ _ $(lTensor_counit_comul (R := R) y)))
    · dsimp
      hopf_tensor_induction comul (R := S) x with x₁ x₂
      hopf_tensor_induction comul (R := R) y with y₁ y₂
      apply (TensorProduct.rid S _).injective
      dsimp
      rw [tmul_smul, smul_assoc, one_smul, smul_tmul']
    · dsimp
      simp only [one_smul]

set_option backward.defeqAttrib.useBackward true in
/-
**TensorProduct.** 是 Mathlib 中的一个实例，位于命名空间 `TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsCocomm S A] [IsCocomm R B] : IsCocomm S (A ⊗[R] B) where
  comm_comp_comul := by
    ext x y
    dsimp
    conv_rhs => rw [← comm_comul _ x, ← comm_comul _ y]
    hopf_tensor_induction comul (R := S) x with x₁ x₂
    hopf_tensor_induction comul (R := R) y with y₁ y₂
    simp

end TensorProduct

namespace Coalgebra
namespace TensorProduct

variable {R S M N P Q : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q] [Module R M] [Module R N]
  [Module R P] [Module R Q] [Module S M] [IsScalarTower R S M] [Coalgebra S M] [Module S N]
  [IsScalarTower R S N] [Coalgebra S N] [Coalgebra R P] [Coalgebra R Q]

section

set_option backward.defeqAttrib.useBackward true in
/-- The tensor product of two coalgebra morphisms as a coalgebra morphism. -/
/-
**Coalgebra.TensorProduct.map** 是 Mathlib 中的一个定义，位于命名空间 `Coalgebra.TensorProduct
`。
形式化陈述：map (f : M ->ₗc[S] N) (g : P ->ₗc[R] Q) : M otimes[R] P ->ₗc[S] N otimes[R
] Q where toLinearMap
参数：f : M ->ₗc[S] N；g : P ->ₗc[R] Q。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tensor product of two coalgebra morphisms as a coalgebra morphism.
-/
noncomputable def map (f : M →ₗc[S] N) (g : P →ₗc[R] Q) :
    M ⊗[R] P →ₗc[S] N ⊗[R] Q where
  toLinearMap := AlgebraTensorModule.map f.toLinearMap g.toLinearMap
  counit_comp := by ext; simp
  map_comp_comul := by
    ext x y
    dsimp
    simp only [← CoalgHomClass.map_comp_comul_apply]
    hopf_tensor_induction comul (R := S) x with x₁ x₂
    hopf_tensor_induction comul (R := R) y with y₁ y₂
    simp

@[simp]
/-
**Coalgebra.TensorProduct.map_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Coalgebra.TensorPr
oduct`。
形式化陈述：map_tmul (f : M ->ₗc[S] N) (g : P ->ₗc[R] Q) (x : M) (y : P) : map f g (x 
otimesₜ y) = f x otimesₜ g y
参数：f : M ->ₗc[S] N；g : P ->ₗc[R] Q；x : M；y : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem map_tmul (f : M →ₗc[S] N) (g : P →ₗc[R] Q) (x : M) (y : P) :
    map f g (x ⊗ₜ y) = f x ⊗ₜ g y :=
  rfl

@[simp]
/-
**Coalgebra.TensorProduct.map_toLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `Coalgebra.T
ensorProduct`。
形式化陈述：map_toLinearMap (f : M ->ₗc[S] N) (g : P ->ₗc[R] Q) : map f g = AlgebraTen
sorModule.map (f : M ->ₗ[S] N) (g : P ->ₗ[R] Q)
参数：f : M ->ₗc[S] N；g : P ->ₗc[R] Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `CoalgHomClass.toSemilinearMapClass`：∀ {F : Type u_1} {R : outParam (Type
 u_2)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring 
R}   {inst_1 : AddCommMo…
-/
theorem map_toLinearMap (f : M →ₗc[S] N) (g : P →ₗc[R] Q) :
    map f g = AlgebraTensorModule.map (f : M →ₗ[S] N) (g : P →ₗ[R] Q) := rfl

variable (R S M N P)

set_option backward.defeqAttrib.useBackward true in
/-- The associator for tensor products of R-coalgebras, as a coalgebra equivalence. -/
/-
**Coalgebra.TensorProduct.assoc** 是 Mathlib 中的一个定义，位于命名空间 `Coalgebra.TensorProdu
ct`。
形式化陈述：(R : Type u_5) →   (S : Type u_6) →     (M : Type u_7) →       (N : Type u
_8) →         (P : Type u_9) →           [inst : CommSemiring R] →             [
inst_1 : CommSemiring S] →               [inst_2 : Algebra R S] →               
  [inst_3 : AddCommMonoid M] →                   [inst_4 : AddCommMonoid N] →   
                  [inst_5 : AddCommMonoid P] →                       [inst_6 : _
root_.Module R M] →                         [inst_7 : _root_.Module R N] →      
                     [inst_8 : _root_.Module R P] →                             
[inst_9 : _root_.Module S M] →                               [inst_10 : IsScalar
Tower R S M] →                                 [inst_11 : Coalgebra S M] →      
                             [inst_12 : _root_.Module S N] →                    
                 [inst_13 : IsScalarTower R S N] →                              
         [inst_14 : Coalgebra S N] →                                         [in
st_15 : Coalgebra R P] →                                           TensorProduct
 R (TensorProduct S M N) P ≃ₗc[S]                                             Te
nsorProduct S M (TensorProduct R N P)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The associator for tensor products of R-coalgebras, as a coalgebra equivalence.
-/
protected noncomputable def assoc :
    (M ⊗[S] N) ⊗[R] P ≃ₗc[S] M ⊗[S] (N ⊗[R] P) :=
  { AlgebraTensorModule.assoc R S S M N P with
    counit_comp := by ext; simp
    map_comp_comul := by
      ext x y z
      dsimp
      hopf_tensor_induction comul (R := S) x with x₁ x₂
      hopf_tensor_induction comul (R := S) y with y₁ y₂
      hopf_tensor_induction comul (R := R) z with z₁ z₂
      simp }

variable {R S M N P}

@[simp]
/-
**Coalgebra.TensorProduct.assoc_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Coalgebra.Tensor
Product`。
形式化陈述：assoc_tmul (x : M) (y : N) (z : P) : Coalgebra.TensorProduct.assoc R S M N
 P ((x otimesₜ y) otimesₜ z) = x otimesₜ (y otimesₜ z)
参数：x : M；y : N；z : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
-/
theorem assoc_tmul (x : M) (y : N) (z : P) :
    Coalgebra.TensorProduct.assoc R S M N P ((x ⊗ₜ y) ⊗ₜ z) = x ⊗ₜ (y ⊗ₜ z) :=
  rfl

@[simp]
/-
**Coalgebra.TensorProduct.assoc_symm_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Coalgebra.T
ensorProduct`。
形式化陈述：assoc_symm_tmul (x : M) (y : N) (z : P) : (Coalgebra.TensorProduct.assoc R
 S M N P).symm (x otimesₜ (y otimesₜ z)) = (x otimesₜ y) otimesₜ z
参数：x : M；y : N；z : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem assoc_symm_tmul (x : M) (y : N) (z : P) :
    (Coalgebra.TensorProduct.assoc R S M N P).symm (x ⊗ₜ (y ⊗ₜ z)) = (x ⊗ₜ y) ⊗ₜ z :=
  rfl

@[simp]
/-
**Coalgebra.TensorProduct.assoc_toLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Coalgeb
ra.TensorProduct`。
形式化陈述：assoc_toLinearEquiv : Coalgebra.TensorProduct.assoc R S M N P = AlgebraTen
sorModule.assoc R S S M N P
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem assoc_toLinearEquiv :
    Coalgebra.TensorProduct.assoc R S M N P = AlgebraTensorModule.assoc R S S M N P := rfl

variable (R P)

set_option backward.defeqAttrib.useBackward true in
/-- The base ring is a left identity for the tensor product of coalgebras, up to
coalgebra equivalence. -/
/-
**Coalgebra.TensorProduct.lid** 是 Mathlib 中的一个定义，位于命名空间 `Coalgebra.TensorProduct
`。
形式化陈述：(R : Type u_5) →   (P : Type u_9) →     [inst : CommSemiring R] →       [i
nst_1 : AddCommMonoid P] →         [inst_2 : _root_.Module R P] → [inst_3 : Coal
gebra R P] → TensorProduct R R P ≃ₗc[R] P
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The base ring is a left identity for the tensor product of coalgebras, up to
coalgebra equivalence.
-/
protected noncomputable def lid : R ⊗[R] P ≃ₗc[R] P :=
  { _root_.TensorProduct.lid R P with
    counit_comp := by ext; simp
    map_comp_comul := by
      ext x
      dsimp
      simp only [one_smul]
      hopf_tensor_induction comul (R := R) x with x₁ x₂
      simp }

variable {R P}

@[simp]
/-
**Coalgebra.TensorProduct.lid_toLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Coalgebra
.TensorProduct`。
形式化陈述：lid_toLinearEquiv : (Coalgebra.TensorProduct.lid R P) = _root_.TensorProdu
ct.lid R P
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem lid_toLinearEquiv :
    (Coalgebra.TensorProduct.lid R P) = _root_.TensorProduct.lid R P := rfl

@[simp]
/-
**Coalgebra.TensorProduct.lid_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Coalgebra.TensorPr
oduct`。
形式化陈述：lid_tmul (r : R) (a : P) : Coalgebra.TensorProduct.lid R P (r otimesₜ a) =
 r • a
参数：r : R；a : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem lid_tmul (r : R) (a : P) : Coalgebra.TensorProduct.lid R P (r ⊗ₜ a) = r • a := rfl

@[simp]
/-
**Coalgebra.TensorProduct.lid_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Coalgebra.Te
nsorProduct`。
形式化陈述：lid_symm_apply (a : P) : (Coalgebra.TensorProduct.lid R P).symm a = 1 otim
esₜ a
参数：a : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem lid_symm_apply (a : P) : (Coalgebra.TensorProduct.lid R P).symm a = 1 ⊗ₜ a := rfl

set_option backward.defeqAttrib.useBackward true in
variable (R S M) in
/-- The base ring is a right identity for the tensor product of coalgebras, up to
coalgebra equivalence. -/
/-
**Coalgebra.TensorProduct.rid** 是 Mathlib 中的一个定义，位于命名空间 `Coalgebra.TensorProduct
`。
形式化陈述：(R : Type u_5) →   (S : Type u_6) →     (M : Type u_7) →       [inst : Com
mSemiring R] →         [inst_1 : CommSemiring S] →           [inst_2 : Algebra R
 S] →             [inst_3 : AddCommMonoid M] →               [inst_4 : _root_.Mo
dule R M] →                 [inst_5 : _root_.Module S M] →                   [in
st_6 : IsScalarTower R S M] → [inst_7 : Coalgebra S M] → TensorProduct R M R ≃ₗc
[S] M
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The base ring is a right identity for the tensor product of coalgebras, up to
coalgebra equivalence.
-/
protected noncomputable def rid : M ⊗[R] R ≃ₗc[S] M :=
  { AlgebraTensorModule.rid R S M with
    counit_comp := by ext; simp
    map_comp_comul := by
      ext x
      dsimp
      simp only [one_smul]
      hopf_tensor_induction comul (R := S) x with x₁ x₂
      simp }

@[simp]
/-
**Coalgebra.TensorProduct.rid_toLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Coalgebra
.TensorProduct`。
形式化陈述：rid_toLinearEquiv : (Coalgebra.TensorProduct.rid R S M) = AlgebraTensorMod
ule.rid R S M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem rid_toLinearEquiv :
    (Coalgebra.TensorProduct.rid R S M) = AlgebraTensorModule.rid R S M := rfl

@[simp]
/-
**Coalgebra.TensorProduct.rid_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Coalgebra.TensorPr
oduct`。
形式化陈述：rid_tmul (r : R) (a : M) : Coalgebra.TensorProduct.rid R S M (a otimesₜ r)
 = r • a
参数：r : R；a : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem rid_tmul (r : R) (a : M) : Coalgebra.TensorProduct.rid R S M (a ⊗ₜ r) = r • a := rfl

@[simp]
/-
**Coalgebra.TensorProduct.rid_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Coalgebra.Te
nsorProduct`。
形式化陈述：rid_symm_apply (a : M) : (Coalgebra.TensorProduct.rid R S M).symm a = a ot
imesₜ 1
参数：a : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem rid_symm_apply (a : M) : (Coalgebra.TensorProduct.rid R S M).symm a = a ⊗ₜ 1 := rfl

end

end TensorProduct
end Coalgebra
namespace CoalgHom

variable {R M N P : Type*} [CommRing R]
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [Module R M] [Module R N]
  [Module R P] [Coalgebra R M] [Coalgebra R N] [Coalgebra R P]

variable (M)

/-- `lTensor M f : M ⊗ N →ₗc M ⊗ P` is the natural coalgebra morphism induced by `f : N →ₗc P`. -/
/-
**CoalgHom.lTensor** 是 Mathlib 中的一个缩写定义，位于命名空间 `CoalgHom`。
形式化陈述：lTensor (f : N ->ₗc[R] P) : M otimes[R] N ->ₗc[R] M otimes[R] P
参数：f : N ->ₗc[R] P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`lTensor M f : M ⊗ N →ₗc M ⊗ P` is the natural coalgebra morphism induced by `f 
: N →ₗc P`.
-/
noncomputable abbrev lTensor (f : N →ₗc[R] P) : M ⊗[R] N →ₗc[R] M ⊗[R] P :=
  Coalgebra.TensorProduct.map (CoalgHom.id R M) f

/-- `rTensor M f : N ⊗ M →ₗc P ⊗ M` is the natural coalgebra morphism induced by `f : N →ₗc P`. -/
/-
**CoalgHom.rTensor** 是 Mathlib 中的一个缩写定义，位于命名空间 `CoalgHom`。
形式化陈述：rTensor (f : N ->ₗc[R] P) : N otimes[R] M ->ₗc[R] P otimes[R] M
参数：f : N ->ₗc[R] P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`rTensor M f : N ⊗ M →ₗc P ⊗ M` is the natural coalgebra morphism induced by `f 
: N →ₗc P`.
-/
noncomputable abbrev rTensor (f : N →ₗc[R] P) : N ⊗[R] M →ₗc[R] P ⊗[R] M :=
  Coalgebra.TensorProduct.map f (CoalgHom.id R M)

end CoalgHom

namespace Coalgebra
variable {R C : Type*} [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
  [IsCocomm R C]

local notation3 "ε" => counit (R := R) (A := C)
local notation3 "μ" => LinearMap.mul' R R
local notation3 "δ" => comul (R := R)
local infix:90 " ◁ " => LinearMap.lTensor
local notation3:90 f:90 " ▷ " X:90 => LinearMap.rTensor X f
local infix:70 " ⊗ₘ " => _root_.TensorProduct.map

variable (R C) in
/-- Comultiplication as a coalgebra hom. -/
/-
**Coalgebra.comulCoalgHom** 是 Mathlib 中的一个定义，位于命名空间 `Coalgebra`。
形式化陈述：comulCoalgHom : C ->ₗc[R] C otimes[R] C where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Comultiplication as a coalgebra hom.
-/
noncomputable def comulCoalgHom : C →ₗc[R] C ⊗[R] C where
  __ := δ
  counit_comp := by
    simp only [counit_def, AlgebraTensorModule.rid_eq_rid, ← lid_eq_rid]
    calc
        (μ ∘ₗ (ε ⊗ₘ ε)) ∘ₗ δ
    _ = (μ ∘ₗ ε ▷ R) ∘ₗ (C ◁ ε ∘ₗ δ) := by simp [coassoc_simps]
    _ = ε := by ext; simp
  map_comp_comul := by simp [comul_def, coassoc_simps]

end Coalgebra

