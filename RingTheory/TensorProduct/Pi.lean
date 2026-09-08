/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Tensor product and products of algebras

In this file we examine the behaviour of the tensor product with (finite) products. This
is a direct application of `Mathlib/LinearAlgebra/TensorProduct/Pi.lean` to the algebra case.

-/

@[expose] public section

open TensorProduct

namespace Algebra.TensorProduct

variable (R S A : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S] [Semiring A]
  [Algebra R A] [Algebra S A] [IsScalarTower R S A]
variable {ι : Type*} (B : ι → Type*) [∀ i, Semiring (B i)] [∀ i, Algebra R (B i)]

@[simp]
/-
**Algebra.TensorProduct.piRightHom_one** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Tensor
Product`。
形式化陈述：piRightHom_one : piRightHom R S A B 1 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
lemma piRightHom_one : piRightHom R S A B 1 = 1 := rfl

variable {R S A B} in
@[simp]
/-
**Algebra.TensorProduct.piRightHom_mul** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Tensor
Product`。
形式化陈述：piRightHom_mul (x y : A otimes[R] forall i, B i) : piRightHom R S A B (x *
 y) = piRightHom R S A B x * piRightHom R S A B y
参数：x y : A otimes[R] forall i, B i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
-/
lemma piRightHom_mul (x y : A ⊗[R] ∀ i, B i) :
    piRightHom R S A B (x * y) = piRightHom R S A B x * piRightHom R S A B y := by
  induction x
  · simp
  · induction y
    · simp
    · ext j
      simp
    · simp_all [mul_add]
  · simp_all [add_mul]

/-- The canonical map `A ⊗[R] (∀ i, B i) →ₐ[S] ∀ i, A ⊗[R] B i`. This is an isomorphism
if `ι` is finite (see `Algebra.TensorProduct.piRight`). -/
/-
**Algebra.TensorProduct.piRightHom** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.TensorProd
uct`。
形式化陈述：piRightHom : A otimes[R] (forall i, B i) ->ₐ[S] forall i, A otimes[R] B i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map `A ⊗[R] (∀ i, B i) →ₐ[S] ∀ i, A ⊗[R] B i`. This is an isomorph
ism
if `ι` is finite (see `Algebra.TensorProduct.piRight`).
-/
def piRightHom : A ⊗[R] (∀ i, B i) →ₐ[S] ∀ i, A ⊗[R] B i :=
  AlgHom.ofLinearMap (_root_.TensorProduct.piRightHom R S A B) (by simp) (by simp)

variable [Fintype ι] [DecidableEq ι]

/-- Tensor product of rings commutes with finite products on the right. -/
/-
**Algebra.TensorProduct.piRight** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.TensorProduct
`。
形式化陈述：piRight : A otimes[R] (forall i, B i) ≃ₐ[S] forall i, A otimes[R] B i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Tensor product of rings commutes with finite products on the right.
-/
def piRight : A ⊗[R] (∀ i, B i) ≃ₐ[S] ∀ i, A ⊗[R] B i :=
  AlgEquiv.ofLinearEquiv (_root_.TensorProduct.piRight R S A B) (by simp) (by simp)

@[simp]
/-
**Algebra.TensorProduct.piRight_tmul** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.TensorPr
oduct`。
形式化陈述：piRight_tmul (x : A) (f : forall i, B i) : piRight R S A B (x otimesₜ f) =
 (fun j => x otimesₜ f j)
参数：x : A；f : forall i, B i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
lemma piRight_tmul (x : A) (f : ∀ i, B i) :
    piRight R S A B (x ⊗ₜ f) = (fun j ↦ x ⊗ₜ f j) := rfl

variable (ι) in
/-- Variant of `Algebra.TensorProduct.piRight` with constant factors. -/
/-
**Algebra.TensorProduct.piScalarRight** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.TensorP
roduct`。
形式化陈述：piScalarRight : A otimes[R] (ι -> R) ≃ₐ[S] ι -> A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Variant of `Algebra.TensorProduct.piRight` with constant factors.
-/
def piScalarRight : A ⊗[R] (ι → R) ≃ₐ[S] ι → A :=
  (piRight R S A (fun _ : ι ↦ R)).trans <|
    AlgEquiv.piCongrRight (fun _ ↦ Algebra.TensorProduct.rid R S A)
/-
**Algebra.TensorProduct.piScalarRight_tmul** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Te
nsorProduct`。
形式化陈述：piScalarRight_tmul (x : A) (y : ι -> R) : piScalarRight R S A ι (x otimesₜ
 y) = fun i => y i • x
参数：x : A；y : ι -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
lemma piScalarRight_tmul (x : A) (y : ι → R) :
    piScalarRight R S A ι (x ⊗ₜ y) = fun i ↦ y i • x :=
  rfl

@[simp]
/-
**Algebra.TensorProduct.piScalarRight_tmul_apply** 是 Mathlib 中的一个引理，位于命名空间 `Alge
bra.TensorProduct`。
形式化陈述：piScalarRight_tmul_apply (x : A) (y : ι -> R) (i : ι) : piScalarRight R S 
A ι (x otimesₜ y) i = y i • x
参数：x : A；y : ι -> R；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
lemma piScalarRight_tmul_apply (x : A) (y : ι → R) (i : ι) :
    piScalarRight R S A ι (x ⊗ₜ y) i = y i • x :=
  rfl

section

variable (B C : Type*) [Semiring B] [Semiring C] [Algebra R B] [Algebra R C]

/-- Tensor product of rings commutes with binary products on the right. -/
nonrec def prodRight : A ⊗[R] (B × C) ≃ₐ[S] A ⊗[R] B × A ⊗[R] C :=
  AlgEquiv.ofLinearEquiv (TensorProduct.prodRight R S A B C)
    (by simp [Algebra.TensorProduct.one_def])
    (LinearMap.map_mul_of_map_mul_tmul (fun _ _ _ _ ↦ by simp))

/-
**Algebra.TensorProduct.prodRight_tmul** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Tensor
Product`。
形式化陈述：prodRight_tmul (a : A) (x : B × C) : prodRight R S A B C (a otimesₜ x) = (
a otimesₜ x.1, a otimesₜ x.2)
参数：a : A；x : B × C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
lemma prodRight_tmul (a : A) (x : B × C) : prodRight R S A B C (a ⊗ₜ x) = (a ⊗ₜ x.1, a ⊗ₜ x.2) :=
  rfl

@[simp]
/-
**Algebra.TensorProduct.prodRight_tmul_fst** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Te
nsorProduct`。
形式化陈述：prodRight_tmul_fst (a : A) (x : B × C) : (prodRight R S A B C (a otimesₜ x
)).fst = a otimesₜ x.1
参数：a : A；x : B × C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
lemma prodRight_tmul_fst (a : A) (x : B × C) : (prodRight R S A B C (a ⊗ₜ x)).fst = a ⊗ₜ x.1 :=
  rfl

@[simp]
/-
**Algebra.TensorProduct.prodRight_tmul_snd** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Te
nsorProduct`。
形式化陈述：prodRight_tmul_snd (a : A) (x : B × C) : (prodRight R S A B C (a otimesₜ x
)).snd = a otimesₜ x.2
参数：a : A；x : B × C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
lemma prodRight_tmul_snd (a : A) (x : B × C) : (prodRight R S A B C (a ⊗ₜ x)).snd = a ⊗ₜ x.2 :=
  rfl

@[simp]
/-
**Algebra.TensorProduct.prodRight_symm_tmul** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.T
ensorProduct`。
形式化陈述：prodRight_symm_tmul (a : A) (b : B) (c : C) : (prodRight R S A B C).symm (
a otimesₜ b, a otimesₜ c) = a otimesₜ (b, c)
参数：a : A；b : B；c : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.injective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.apply_symm_apply`：apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma prodRight_symm_tmul (a : A) (b : B) (c : C) :
    (prodRight R S A B C).symm (a ⊗ₜ b, a ⊗ₜ c) = a ⊗ₜ (b, c) := by
  apply (prodRight R S A B C).injective
  simp [prodRight_tmul]

end

end Algebra.TensorProduct

/-
**TensorProduct.piScalarRight_symm_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TensorProduct.piScalarRight_symm_algebraMap (R : Type*) [CommSemiring R] (
S : Type*) [CommSemiring S] [Algebra R S] (ι : Type*) [Fintype ι] [DecidableEq ι
] {N : Type*} [Semiring N] [Algebra R N] [Module S N] [IsScalarTower R S N] (x :
 ι -> R) : (TensorProduct.piScalarRight R S N ι).symm (algebraMap _ _ x) = 1 oti
mesₜ[R] x
参数：R : Type*；S : Type*；ι : Type*；x : ι -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用引理 `TensorProduct.piScalarRight_apply`：piScalarRight_apply (x : N otimes[R] 
(ι -> R)) : piScalarRight R S N ι x = piScalarRightHom R S N ι x
· 使用引理 `TensorProduct.piScalarRightHom_tmul`：piScalarRightHom_tmul (x : N) (f : 
ι -> R) : piScalarRightHom R S N ι (x otimesₜ f) = (fun j => f j • x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem TensorProduct.piScalarRight_symm_algebraMap
    (R : Type*) [CommSemiring R] (S : Type*) [CommSemiring S] [Algebra R S]
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    {N : Type*} [Semiring N] [Algebra R N] [Module S N] [IsScalarTower R S N]
    (x : ι → R) :
    (TensorProduct.piScalarRight R S N ι).symm (algebraMap _ _ x) = 1 ⊗ₜ[R] x := by
  simp [Algebra.algebraMap_eq_smul_one, Pi.smul_def', LinearEquiv.symm_apply_eq,
    piScalarRight_apply, piScalarRightHom_tmul]
