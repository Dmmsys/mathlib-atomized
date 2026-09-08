/-
Copyright (c) 2024 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston, Andrew Yang
-/
module

public import Mathlib.RingTheory.Bialgebra.Equiv
public import Mathlib.RingTheory.Coalgebra.TensorProduct
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Tensor products of bialgebras

We define the data in the monoidal structure on the category of bialgebras - e.g. the bialgebra
instance on a tensor product of bialgebras, and the tensor product of two `BialgHom`s as a
`BialgHom`. This is done by combining the corresponding API for coalgebras and algebras.

-/

public noncomputable section

open Coalgebra
open scoped TensorProduct

namespace Bialgebra.TensorProduct

open Coalgebra.TensorProduct

variable {R S A B C D : Type*} [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

section Heterogeneous
variable (R S A B) [Bialgebra S A] [Bialgebra R B] [Algebra R A] [Algebra R S] [IsScalarTower R S A]

/-
**Bialgebra.TensorProduct.counit_eq_algHom_toLinearMap** 是 Mathlib 中的一个引理，位于命名空间
 `Bialgebra.TensorProduct`。
形式化陈述：counit_eq_algHom_toLinearMap : Coalgebra.counit (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
lemma counit_eq_algHom_toLinearMap :
    Coalgebra.counit (R := S) (A := A ⊗[R] B) =
      ((Algebra.TensorProduct.rid _ _ _).toAlgHom.comp (Algebra.TensorProduct.map
      (Bialgebra.counitAlgHom S A) (Bialgebra.counitAlgHom R B))).toLinearMap :=
  rfl
/-
**Bialgebra.TensorProduct.comul_eq_algHom_toLinearMap** 是 Mathlib 中的一个引理，位于命名空间 
`Bialgebra.TensorProduct`。
形式化陈述：comul_eq_algHom_toLinearMap : Coalgebra.comul (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
lemma comul_eq_algHom_toLinearMap :
    Coalgebra.comul (R := S) (A := A ⊗[R] B) =
      ((Algebra.TensorProduct.tensorTensorTensorComm R S R S A A B B).toAlgHom.comp
      (Algebra.TensorProduct.map (Bialgebra.comulAlgHom S A)
      (Bialgebra.comulAlgHom R B))).toLinearMap :=
  rfl
/-
**Bialgebra.TensorProduct._root_.TensorProduct.instBialgebra** 是 Mathlib 中的一个实例，
位于命名空间 `Bialgebra.TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance _root_.TensorProduct.instBialgebra : Bialgebra S (A ⊗[R] B) := by
  have hcounit := congr(DFunLike.coe $(counit_eq_algHom_toLinearMap R S A B))
  have hcomul := congr(DFunLike.coe $(comul_eq_algHom_toLinearMap R S A B))
  refine Bialgebra.mk' S (A ⊗[R] B) ?_ (fun {x y} => ?_) ?_ (fun {x y} => ?_) <;>
  simp_all only [AlgHom.toLinearMap_apply] <;>
  simp only [map_one, map_mul]
/-
**Bialgebra.TensorProduct.counitAlgHom_def** 是 Mathlib 中的一个引理，位于命名空间 `Bialgebra.
TensorProduct`。
形式化陈述：counitAlgHom_def : counitAlgHom (R
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma counitAlgHom_def :
    counitAlgHom (R := S) (A := A ⊗[R] B) =
      (Algebra.TensorProduct.rid _ _ _).toAlgHom.comp (Algebra.TensorProduct.map
      (Bialgebra.counitAlgHom S A) (Bialgebra.counitAlgHom R B)) := rfl
/-
**Bialgebra.TensorProduct.comulAlgHom_def** 是 Mathlib 中的一个引理，位于命名空间 `Bialgebra.T
ensorProduct`。
形式化陈述：comulAlgHom_def : comulAlgHom (R
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comulAlgHom_def :
    comulAlgHom (R := S) (A := A ⊗[R] B) =
      (Algebra.TensorProduct.tensorTensorTensorComm R S R S A A B B).toAlgHom.comp
        (Algebra.TensorProduct.map (Bialgebra.comulAlgHom S A)
        (Bialgebra.comulAlgHom R B)) := rfl

variable {R S A B}

variable [Semiring C] [Semiring D] [Bialgebra S C]
  [Bialgebra R D] [Algebra R C] [IsScalarTower R S C]

/-- The tensor product of two bialgebra morphisms as a bialgebra morphism. -/
/-
**Bialgebra.TensorProduct.map** 是 Mathlib 中的一个定义，位于命名空间 `Bialgebra.TensorProduct
`。
形式化陈述：{R : Type u_1} →   {S : Type u_2} →     {A : Type u_3} →       {B : Type u
_4} →         {C : Type u_5} →           {D : Type u_6} →             [inst : Co
mmSemiring R] →               [inst_1 : CommSemiring S] →                 [inst_
2 : Semiring A] →                   [inst_3 : Semiring B] →                     
[inst_4 : Bialgebra S A] →                       [inst_5 : Bialgebra R B] →     
                    [inst_6 : Algebra R A] →                           [inst_7 :
 Algebra R S] →                             [inst_8 : IsScalarTower R S A] →    
                           [inst_9 : Semiring C] →                              
   [inst_10 : Semiring D] →                                   [inst_11 : Bialgeb
ra S C] →                                     [inst_12 : Bialgebra R D] →       
                                [inst_13 : Algebra R C] →                       
                  [inst_14 : IsScalarTower R S C] →                             
              (A →ₐc[S] C) → (B →ₐc[R] D) → TensorProduct R A B →ₐc[S] TensorPro
duct R C D
参数：A →ₐc[S] C；B →ₐc[R] D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tensor product of two bialgebra morphisms as a bialgebra morphism.
-/
@[expose] def map (f : A →ₐc[S] C) (g : B →ₐc[R] D) : A ⊗[R] B →ₐc[S] C ⊗[R] D :=
  { Coalgebra.TensorProduct.map (f : A →ₗc[S] C) (g : B →ₗc[R] D),
    Algebra.TensorProduct.map (f : A →ₐ[S] C) (g : B →ₐ[R] D) with }

@[simp]
/-
**Bialgebra.TensorProduct.map_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Bialgebra.TensorPr
oduct`。
形式化陈述：map_tmul (f : A ->ₐc[S] C) (g : B ->ₐc[R] D) (x : A) (y : B) : map f g (x 
otimesₜ y) = f x otimesₜ g y
参数：f : A ->ₐc[S] C；g : B ->ₐc[R] D；x : A；y : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem map_tmul (f : A →ₐc[S] C) (g : B →ₐc[R] D) (x : A) (y : B) :
    map f g (x ⊗ₜ y) = f x ⊗ₜ g y :=
  rfl

@[simp]
/-
**Bialgebra.TensorProduct.map_toCoalgHom** 是 Mathlib 中的一个定理，位于命名空间 `Bialgebra.Te
nsorProduct`。
形式化陈述：map_toCoalgHom (f : A ->ₐc[S] C) (g : B ->ₐc[R] D) : map f g = Coalgebra.T
ensorProduct.map (f : A ->ₗc[S] C) (g : B ->ₗc[R] D)
参数：f : A ->ₐc[S] C；g : B ->ₐc[R] D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `BialgHomClass.toCoalgHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)
} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   
{inst_1 : Semiring …
-/
theorem map_toCoalgHom (f : A →ₐc[S] C) (g : B →ₐc[R] D) :
    map f g = Coalgebra.TensorProduct.map (f : A →ₗc[S] C) (g : B →ₗc[R] D) := rfl

@[simp]
/-
**Bialgebra.TensorProduct.map_toAlgHom** 是 Mathlib 中的一个定理，位于命名空间 `Bialgebra.Tens
orProduct`。
形式化陈述：map_toAlgHom (f : A ->ₐc[S] C) (g : B ->ₐc[R] D) : (map f g : A otimes[R] 
B ->ₐ[S] C otimes[R] D) = Algebra.TensorProduct.map (f : A ->ₐ[S] C) (g : B ->ₐ[
R] D)
参数：f : A ->ₐc[S] C；g : B ->ₐc[R] D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem map_toAlgHom (f : A →ₐc[S] C) (g : B →ₐc[R] D) :
    (map f g : A ⊗[R] B →ₐ[S] C ⊗[R] D) =
      Algebra.TensorProduct.map (f : A →ₐ[S] C) (g : B →ₐ[R] D) :=
  rfl

variable (R S A C D) in
/-- The associator for tensor products of R-bialgebras, as a bialgebra equivalence. -/
/-
**Bialgebra.TensorProduct.assoc** 是 Mathlib 中的一个定义，位于命名空间 `Bialgebra.TensorProdu
ct`。
形式化陈述：(R : Type u_1) →   (S : Type u_2) →     (A : Type u_3) →       (C : Type u
_5) →         (D : Type u_6) →           [inst : CommSemiring R] →             [
inst_1 : CommSemiring S] →               [inst_2 : Semiring A] →                
 [inst_3 : Bialgebra S A] →                   [inst_4 : Algebra R A] →          
           [inst_5 : Algebra R S] →                       [inst_6 : IsScalarTowe
r R S A] →                         [inst_7 : Semiring C] →                      
     [inst_8 : Semiring D] →                             [inst_9 : Bialgebra S C
] →                               [inst_10 : Bialgebra R D] →                   
              [inst_11 : Algebra R C] →                                   [inst_
12 : IsScalarTower R S C] →                                     TensorProduct R 
(TensorProduct S A C) D ≃ₐc[S]                                       TensorProdu
ct S A (TensorProduct R C D)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The associator for tensor products of R-bialgebras, as a bialgebra equivalence.
-/
@[expose] protected def assoc : (A ⊗[S] C) ⊗[R] D ≃ₐc[S] A ⊗[S] (C ⊗[R] D) :=
  { Coalgebra.TensorProduct.assoc R S A C D, Algebra.TensorProduct.assoc R S S A C D with }

@[simp]
/-
**Bialgebra.TensorProduct.assoc_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Bialgebra.Tensor
Product`。
形式化陈述：assoc_tmul (x : A) (y : C) (z : D) : Bialgebra.TensorProduct.assoc R S A C
 D ((x otimesₜ y) otimesₜ z) = x otimesₜ (y otimesₜ z)
参数：x : A；y : C；z : D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
-/
theorem assoc_tmul (x : A) (y : C) (z : D) :
    Bialgebra.TensorProduct.assoc R S A C D ((x ⊗ₜ y) ⊗ₜ z) = x ⊗ₜ (y ⊗ₜ z) :=
  rfl

@[simp]
/-
**Bialgebra.TensorProduct.assoc_symm_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Bialgebra.T
ensorProduct`。
形式化陈述：assoc_symm_tmul (x : A) (y : C) (z : D) : (Bialgebra.TensorProduct.assoc R
 S A C D).symm (x otimesₜ (y otimesₜ z)) = (x otimesₜ y) otimesₜ z
参数：x : A；y : C；z : D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem assoc_symm_tmul (x : A) (y : C) (z : D) :
    (Bialgebra.TensorProduct.assoc R S A C D).symm (x ⊗ₜ (y ⊗ₜ z)) = (x ⊗ₜ y) ⊗ₜ z :=
  rfl

@[simp]
/-
**Bialgebra.TensorProduct.assoc_toCoalgEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Bialgebr
a.TensorProduct`。
形式化陈述：assoc_toCoalgEquiv : (Bialgebra.TensorProduct.assoc R S A C D : _ ≃ₗc[S] _
) = Coalgebra.TensorProduct.assoc R S A C D
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `BialgEquivClass.toCoalgEquivClass`：∀ {F : Type u_1} {R : outParam (Type 
u_2)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R
}   {inst_1 : Semiring …
· 使用定理 `BialgEquiv.instBialgEquivClass`：∀ {R : Type u} {A : Type v} {B : Type w}
 [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 :
 Algebra R A] [inst_…
-/
theorem assoc_toCoalgEquiv :
    (Bialgebra.TensorProduct.assoc R S A C D : _ ≃ₗc[S] _) =
    Coalgebra.TensorProduct.assoc R S A C D := rfl

@[simp]
/-
**Bialgebra.TensorProduct.assoc_toAlgEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Bialgebra.
TensorProduct`。
形式化陈述：assoc_toAlgEquiv : (Bialgebra.TensorProduct.assoc R S A C D : _ ≃ₐ[S] _) =
 Algebra.TensorProduct.assoc R S S A C D
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem assoc_toAlgEquiv :
    (Bialgebra.TensorProduct.assoc R S A C D : _ ≃ₐ[S] _) =
    Algebra.TensorProduct.assoc R S S A C D := rfl

variable (R B) in
/-- The base ring is a left identity for the tensor product of bialgebras, up to
bialgebra equivalence. -/
/-
**Bialgebra.TensorProduct.lid** 是 Mathlib 中的一个定义，位于命名空间 `Bialgebra.TensorProduct
`。
形式化陈述：(R : Type u_1) →   (B : Type u_4) →     [inst : CommSemiring R] → [inst_1 
: Semiring B] → [inst_2 : Bialgebra R B] → TensorProduct R R B ≃ₐc[R] B
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The base ring is a left identity for the tensor product of bialgebras, up to
bialgebra equivalence.
-/
@[expose] protected def lid : R ⊗[R] B ≃ₐc[R] B :=
  { Coalgebra.TensorProduct.lid R B, Algebra.TensorProduct.lid R B with }

@[simp]
/-
**Bialgebra.TensorProduct.lid_toCoalgEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Bialgebra.
TensorProduct`。
形式化陈述：lid_toCoalgEquiv : (Bialgebra.TensorProduct.lid R B : R otimes[R] B ≃ₗc[R]
 B) = Coalgebra.TensorProduct.lid R B
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `BialgEquivClass.toCoalgEquivClass`：∀ {F : Type u_1} {R : outParam (Type 
u_2)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R
}   {inst_1 : Semiring …
· 使用定理 `BialgEquiv.instBialgEquivClass`：∀ {R : Type u} {A : Type v} {B : Type w}
 [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 :
 Algebra R A] [inst_…
-/
theorem lid_toCoalgEquiv :
    (Bialgebra.TensorProduct.lid R B : R ⊗[R] B ≃ₗc[R] B) = Coalgebra.TensorProduct.lid R B := rfl

@[simp]
/-
**Bialgebra.TensorProduct.lid_toAlgEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Bialgebra.Te
nsorProduct`。
形式化陈述：lid_toAlgEquiv : (Bialgebra.TensorProduct.lid R B : R otimes[R] B ≃ₐ[R] B)
 = Algebra.TensorProduct.lid R B
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem lid_toAlgEquiv :
    (Bialgebra.TensorProduct.lid R B : R ⊗[R] B ≃ₐ[R] B) = Algebra.TensorProduct.lid R B := rfl

@[simp]
/-
**Bialgebra.TensorProduct.lid_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Bialgebra.TensorPr
oduct`。
形式化陈述：lid_tmul (r : R) (a : B) : Bialgebra.TensorProduct.lid R B (r otimesₜ a) =
 r • a
参数：r : R；a : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem lid_tmul (r : R) (a : B) : Bialgebra.TensorProduct.lid R B (r ⊗ₜ a) = r • a := rfl

@[simp]
/-
**Bialgebra.TensorProduct.lid_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Bialgebra.Te
nsorProduct`。
形式化陈述：lid_symm_apply (a : B) : (Bialgebra.TensorProduct.lid R B).symm a = 1 otim
esₜ a
参数：a : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem lid_symm_apply (a : B) : (Bialgebra.TensorProduct.lid R B).symm a = 1 ⊗ₜ a := rfl
/-
**Bialgebra.TensorProduct.coalgebra_rid_eq_algebra_rid_apply** 是 Mathlib 中的一个定理，
位于命名空间 `Bialgebra.TensorProduct`。
形式化陈述：coalgebra_rid_eq_algebra_rid_apply (x : A otimes[R] R) : Coalgebra.TensorP
roduct.rid R S A x = Algebra.TensorProduct.rid R R A x
参数：x : A otimes[R] R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem coalgebra_rid_eq_algebra_rid_apply (x : A ⊗[R] R) :
    Coalgebra.TensorProduct.rid R S A x = Algebra.TensorProduct.rid R R A x := rfl

variable (R S A) in
/-- The base ring is a right identity for the tensor product of bialgebras, up to
bialgebra equivalence. -/
/-
**Bialgebra.TensorProduct.rid** 是 Mathlib 中的一个定义，位于命名空间 `Bialgebra.TensorProduct
`。
形式化陈述：(R : Type u_1) →   (S : Type u_2) →     (A : Type u_3) →       [inst : Com
mSemiring R] →         [inst_1 : CommSemiring S] →           [inst_2 : Semiring 
A] →             [inst_3 : Bialgebra S A] →               [inst_4 : Algebra R A]
 →                 [inst_5 : Algebra R S] → [inst_6 : IsScalarTower R S A] → Ten
sorProduct R A R ≃ₐc[S] A
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The base ring is a right identity for the tensor product of bialgebras, up to
bialgebra equivalence.
-/
@[expose] protected def rid : A ⊗[R] R ≃ₐc[S] A where
  toCoalgEquiv := Coalgebra.TensorProduct.rid R S A
  map_mul' x y := by
    simp only [CoalgEquiv.toCoalgHom_eq_coe, CoalgHom.toLinearMap_eq_coe, AddHom.toFun_eq_coe,
      LinearMap.coe_toAddHom, CoalgHom.coe_toLinearMap, CoalgHom.coe_coe,
      coalgebra_rid_eq_algebra_rid_apply, map_mul]

@[simp]
/-
**Bialgebra.TensorProduct.rid_toCoalgEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Bialgebra.
TensorProduct`。
形式化陈述：rid_toCoalgEquiv : (TensorProduct.rid R S A : A otimes[R] R ≃ₗc[S] A) = Co
algebra.TensorProduct.rid R S A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `BialgEquivClass.toCoalgEquivClass`：∀ {F : Type u_1} {R : outParam (Type 
u_2)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R
}   {inst_1 : Semiring …
· 使用定理 `BialgEquiv.instBialgEquivClass`：∀ {R : Type u} {A : Type v} {B : Type w}
 [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 :
 Algebra R A] [inst_…
-/
theorem rid_toCoalgEquiv :
    (TensorProduct.rid R S A : A ⊗[R] R ≃ₗc[S] A) = Coalgebra.TensorProduct.rid R S A := rfl

@[simp]
/-
**Bialgebra.TensorProduct.rid_toAlgEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Bialgebra.Te
nsorProduct`。
形式化陈述：rid_toAlgEquiv : (Bialgebra.TensorProduct.rid R S A : A otimes[R] R ≃ₐ[S] 
A) = Algebra.TensorProduct.rid R S A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.ext`：ext {f g : A₁ ≃ₐ[R] A₂} (h : forall a, f a = g a) : f = g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Bialgebra.TensorProduct.coalgebra_rid_eq_algebra_rid_apply`：coalgebra_ri
d_eq_algebra_rid_apply (x : A otimes[R] R) : Coalgebra.TensorProduct.rid R S A x
 = Algebra.TensorProduct.rid R R A x
-/
theorem rid_toAlgEquiv :
    (Bialgebra.TensorProduct.rid R S A : A ⊗[R] R ≃ₐ[S] A) = Algebra.TensorProduct.rid R S A := by
  ext x
  exact coalgebra_rid_eq_algebra_rid_apply x

@[simp]
/-
**Bialgebra.TensorProduct.rid_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Bialgebra.TensorPr
oduct`。
形式化陈述：rid_tmul (r : R) (a : A) : Bialgebra.TensorProduct.rid R S A (a otimesₜ r)
 = r • a
参数：r : R；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem rid_tmul (r : R) (a : A) : Bialgebra.TensorProduct.rid R S A (a ⊗ₜ r) = r • a := rfl

@[simp]
/-
**Bialgebra.TensorProduct.rid_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Bialgebra.Te
nsorProduct`。
形式化陈述：rid_symm_apply (a : A) : (Bialgebra.TensorProduct.rid R S A).symm a = a ot
imesₜ 1
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem rid_symm_apply (a : A) : (Bialgebra.TensorProduct.rid R S A).symm a = a ⊗ₜ 1 := rfl

end Heterogeneous

section Homogeneous
variable (R S A B) [Bialgebra R A] [Bialgebra R B]

set_option backward.defeqAttrib.useBackward true in
/-- The tensor product of `R`-bialgebras is commutative, up to bialgebra isomorphism. -/
/-
**Bialgebra.TensorProduct.comm** 是 Mathlib 中的一个定义，位于命名空间 `Bialgebra.TensorProduc
t`。
形式化陈述：(R : Type u_1) →   (A : Type u_3) →     (B : Type u_4) →       [inst : Com
mSemiring R] →         [inst_1 : Semiring A] →           [inst_2 : Semiring B] →
             [inst_3 : Bialgebra R A] → [inst_4 : Bialgebra R B] → TensorProduct
 R A B ≃ₐc[R] TensorProduct R B A
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tensor product of `R`-bialgebras is commutative, up to bialgebra isomorphism
.
-/
@[expose] def comm : A ⊗[R] B ≃ₐc[R] B ⊗[R] A :=
  .ofAlgEquiv (Algebra.TensorProduct.comm R A B) (by ext <;> simp) <| by
    ext a <;>
    · dsimp
      rw [← (ℛ R a).eq]
      simp [TensorProduct.tmul_sum, TensorProduct.sum_tmul, Algebra.TensorProduct.one_def]

end Homogeneous
end Bialgebra.TensorProduct

namespace BialgHom

variable {R A B C : Type*} [CommRing R] [Ring A] [Ring B] [Ring C]
    [Bialgebra R A] [Bialgebra R B] [Bialgebra R C]

variable (A)

/-- `lTensor A f : A ⊗ B →ₐc A ⊗ C` is the natural bialgebra morphism induced by `f : B →ₐc C`. -/
/-
**BialgHom.lTensor** 是 Mathlib 中的一个缩写定义，位于命名空间 `BialgHom`。
形式化陈述：lTensor (f : B ->ₐc[R] C) : A otimes[R] B ->ₐc[R] A otimes[R] C
参数：f : B ->ₐc[R] C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`lTensor A f : A ⊗ B →ₐc A ⊗ C` is the natural bialgebra morphism induced by `f 
: B →ₐc C`.
-/
abbrev lTensor (f : B →ₐc[R] C) : A ⊗[R] B →ₐc[R] A ⊗[R] C :=
  Bialgebra.TensorProduct.map (BialgHom.id R A) f

/-- `rTensor A f : B ⊗ A →ₐc C ⊗ A` is the natural bialgebra morphism induced by `f : B →ₐc C`. -/
/-
**BialgHom.rTensor** 是 Mathlib 中的一个缩写定义，位于命名空间 `BialgHom`。
形式化陈述：rTensor (f : B ->ₐc[R] C) : B otimes[R] A ->ₐc[R] C otimes[R] A
参数：f : B ->ₐc[R] C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`rTensor A f : B ⊗ A →ₐc C ⊗ A` is the natural bialgebra morphism induced by `f 
: B →ₐc C`.
-/
abbrev rTensor (f : B →ₐc[R] C) : B ⊗[R] A →ₐc[R] C ⊗[R] A :=
  Bialgebra.TensorProduct.map f (BialgHom.id R A)

end BialgHom

namespace Bialgebra
variable {R A B ι κ : Type*} [CommSemiring R]

section Semiring
variable [Semiring A] [Bialgebra R A] [Semiring B] [Bialgebra R B] {a : A} {b : B}

variable (R A) in
/-- Comultiplication as a bialgebra hom. -/
/-
**Bialgebra.comulBialgHom** 是 Mathlib 中的一个定义，位于命名空间 `Bialgebra`。
形式化陈述：(R : Type u_1) →   (A : Type u_2) →     [inst : CommSemiring R] →       [i
nst_1 : Semiring A] → [inst_2 : Bialgebra R A] → [Coalgebra.IsCocomm R A] → A →ₐ
c[R] TensorProduct R A A
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Comultiplication as a bialgebra hom.
-/
@[expose] def comulBialgHom [IsCocomm R A] : A →ₐc[R] A ⊗[R] A where
  __ := comulAlgHom R A
  __ := comulCoalgHom R A
/-
**Bialgebra.comm_comp_comulBialgHom** 是 Mathlib 中的一个引理，位于命名空间 `Bialgebra`。
形式化陈述：comm_comp_comulBialgHom [IsCocomm R A] : (TensorProduct.comm R A A).toBial
gHom.comp (comulBialgHom R A) = comulBialgHom R A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BialgHom.ext`：ext {φ₁ φ₂ : A ->ₐc[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁
 = φ₂
· 使用定理 `Coalgebra.comm_comul`：∀ (R : Type u) {A : Type v} [inst : CommSemiring R
] [inst_1 : AddCommMonoid A] [inst_2 : _root_.Module R A]   [inst_3 : Coalgebra 
R A] [Coal…
-/
lemma comm_comp_comulBialgHom [IsCocomm R A] :
    (TensorProduct.comm R A A).toBialgHom.comp (comulBialgHom R A) = comulBialgHom R A := by
  ext; exact comm_comul _ _

variable (R A) in
/-- Multiplication on a bialgebra as a coalgebra hom. -/
@[expose]
/-
**Bialgebra.mulCoalgHom** 是 Mathlib 中的一个定义，位于命名空间 `Bialgebra`。
形式化陈述：mulCoalgHom : A otimes[R] A ->ₗc[R] A where toLinearMap
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiplication on a bialgebra as a coalgebra hom.
-/
def mulCoalgHom : A ⊗[R] A →ₗc[R] A where
  toLinearMap := .mul' R A
  counit_comp := by ext; simp [mul_comm]
  map_comp_comul := by
    ext a b
    simp [← (ℛ R a).eq, ← (ℛ R b).eq, TensorProduct.sum_tmul]
    simp [TensorProduct.tmul_sum, Finset.sum_mul_sum]

-- TODO: Generate this using `simps` once the coercion from `LinearMapClass` is gone.
@[simp]
/-
**Bialgebra.toLinearMap_mulCoalgHom** 是 Mathlib 中的一个引理，位于命名空间 `Bialgebra`。
形式化陈述：toLinearMap_mulCoalgHom : mulCoalgHom R A = LinearMap.mul' R A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CoalgHomClass.toSemilinearMapClass`：∀ {F : Type u_1} {R : outParam (Type
 u_2)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring 
R}   {inst_1 : AddCommMo…
-/
lemma toLinearMap_mulCoalgHom : mulCoalgHom R A = LinearMap.mul' R A := rfl
/-
**Bialgebra.coe_mulCoalgHom** 是 Mathlib 中的一个定理，位于命名空间 `Bialgebra`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} [inst : CommSemiring R] [inst_1 : Semiring
 A] [inst_2 : Bialgebra R A],   ⇑(Bialgebra.mulCoalgHom R A) = ⇑(LinearMap.mul' 
R A)
参数：Bialgebra.mulCoalgHom R A；LinearMap.mul' R A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_mulCoalgHom : ⇑(mulCoalgHom R A) = LinearMap.mul' R A := rfl

/-- Representations of `a` and `b` yield a representation of `a ⊗ b`. -/
@[expose, simps]
/-
**Bialgebra._root_.Coalgebra.Repr.tmul** 是 Mathlib 中的一个定义，位于命名空间 `Bialgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Representations of `a` and `b` yield a representation of `a ⊗ b`.
-/
protected def _root_.Coalgebra.Repr.tmul (ℛa : Coalgebra.Repr R a ι) (ℛb : Coalgebra.Repr R b κ) :
    Coalgebra.Repr R (a ⊗ₜ[R] b) (ι × κ) where
  index := ℛa.index ×ˢ ℛb.index
  left i := ℛa.left i.1 ⊗ₜ ℛb.left i.2
  right i := ℛa.right i.1 ⊗ₜ ℛb.right i.2
  eq := by
    simp [← ℛa.eq, ← ℛb.eq, TensorProduct.sum_tmul ℛa.index, TensorProduct.tmul_sum,
      ← Finset.sum_product']

/-- Representations of `a` and `b` yield a representation of `a * b`. -/
@[expose, simps! left right index] protected
/-
**Bialgebra._root_.Coalgebra.Repr.mul** 是 Mathlib 中的一个定义，位于命名空间 `Bialgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Representations of `a` and `b` yield a representation of `a * b`.
-/
def _root_.Coalgebra.Repr.mul {b : A} (ℛ₁ : Coalgebra.Repr R a ι) (ℛ₂ : Coalgebra.Repr R b κ) :
    Coalgebra.Repr R (a * b) (ι × κ) := (ℛ₁.tmul ℛ₂).induced (R := R) (mulCoalgHom R A)

end Semiring

@[simp]
/-
**Bialgebra.counitAlgHom_comp_includeRight** 是 Mathlib 中的一个引理，位于命名空间 `Bialgebra`
。
形式化陈述：counitAlgHom_comp_includeRight [CommSemiring A] [Semiring B] [Algebra R A]
 [Bialgebra R B] : ((counitAlgHom A (A otimes[R] B)).restrictScalars R).comp Alg
ebra.TensorProduct.includeRight = (Algebra.ofId R A).comp (counitAlgHom R B)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bialgebra.counitAlgHom_apply`：∀ (R : Type u) (A : Type v) [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Bialgebra R A] (a : A),   (Bialgebra.c
ounitAlgHom R A) a…
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma counitAlgHom_comp_includeRight [CommSemiring A] [Semiring B] [Algebra R A] [Bialgebra R B] :
    ((counitAlgHom A (A ⊗[R] B)).restrictScalars R).comp Algebra.TensorProduct.includeRight =
      (Algebra.ofId R A).comp (counitAlgHom R B) := by
  ext; simp [Algebra.algebraMap_eq_smul_one]
/-
**Bialgebra.comul_includeRight** 是 Mathlib 中的一个引理，位于命名空间 `Bialgebra`。
形式化陈述：comul_includeRight [CommSemiring A] [CommSemiring B] [Bialgebra R B] [Alge
bra R A] : (RingHomClass.toRingHom (Bialgebra.comulAlgHom A (A otimes[R] B))).co
mp (RingHomClass.toRingHom Algebra.TensorProduct.includeRight) = (Algebra.Tensor
Product.mapRingHom (algebraMap R A) (RingHomClass.toRingHom (Algebra.TensorProdu
ct.includeRight (A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `Bialgebra.comulAlgHom_apply`：∀ (R : Type u) (A : Type v) [inst : CommSem
iring R] [inst_1 : Semiring A] [inst_2 : Bialgebra R A] (a : A),   (Bialgebra.co
mulAlgHom R A) a …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Coalgebra.Repr.eq`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [
inst_1 : AddCommMonoid A] [inst_2 : _root_.Module R A]   [inst_3 : CoalgebraStru
ct R A]…
· 使用定理 `TensorProduct.tmul_sum`：tmul_sum (m : M) {α : Type*} (s : Finset α) (n :
 α -> N) : (m otimesₜ[R] ∑ a in s, n a) = ∑ a in s, m otimesₜ[R] n a
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Algebra.TensorProduct.mapRingHom_tmul`：mapRingHom_tmul (s : S) (t : T) :
 mapRingHom fR fS fT HS HT (s otimesₜ t) = fS s otimesₜ fT t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comul_includeRight [CommSemiring A] [CommSemiring B] [Bialgebra R B] [Algebra R A] :
    (RingHomClass.toRingHom (Bialgebra.comulAlgHom A (A ⊗[R] B))).comp
      (RingHomClass.toRingHom Algebra.TensorProduct.includeRight) =
      (Algebra.TensorProduct.mapRingHom (algebraMap R A)
        (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight (A := A)))
        (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight (A := A)))
        (by simp [← IsScalarTower.algebraMap_eq])
        (by simp [← IsScalarTower.algebraMap_eq])).comp
        (RingHomClass.toRingHom (Bialgebra.comulAlgHom R B)) := by
  ext x; simp [← (ℛ R x).eq, TensorProduct.tmul_sum]

section CommSemiring
variable [CommSemiring A] [Bialgebra R A]

variable (R A) in
/-- Multiplication on a commutative bialgebra as a bialgebra hom. -/
@[expose, simps toCoalgHom]
/-
**Bialgebra.mulBialgHom** 是 Mathlib 中的一个定义，位于命名空间 `Bialgebra`。
形式化陈述：mulBialgHom : A otimes[R] A ->ₐc[R] A where toCoalgHom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiplication on a commutative bialgebra as a bialgebra hom.
-/
def mulBialgHom : A ⊗[R] A →ₐc[R] A where
  toCoalgHom := mulCoalgHom R A
  __ := Algebra.TensorProduct.lmul' R

@[simp]
/-
**Bialgebra.mulBialgHom_toAlgHom** 是 Mathlib 中的一个引理，位于命名空间 `Bialgebra`。
形式化陈述：mulBialgHom_toAlgHom : (mulBialgHom R A).toAlgHom = Algebra.TensorProduct.
lmul' R
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mulBialgHom_toAlgHom : (mulBialgHom R A).toAlgHom = Algebra.TensorProduct.lmul' R := rfl
/-
**Bialgebra.coe_mulBialgHom** 是 Mathlib 中的一个定理，位于命名空间 `Bialgebra`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} [inst : CommSemiring R] [inst_1 : CommSemi
ring A] [inst_2 : Bialgebra R A],   ⇑(Bialgebra.mulBialgHom R A) = ⇑(LinearMap.m
ul' R A)
参数：Bialgebra.mulBialgHom R A；LinearMap.mul' R A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_mulBialgHom : ⇑(mulBialgHom R A) = LinearMap.mul' R A := rfl

end CommSemiring
end Bialgebra

