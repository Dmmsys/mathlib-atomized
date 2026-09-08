/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Bryan Wang
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.DirectSum.Finsupp

/-!
# Tensor product with free modules.

This file contains lemmas about tensoring with free modules.
-/

@[expose] public section

open TensorProduct

variable {R : Type*} (A : Type*) {V : Type*}
    [CommSemiring A] [CommSemiring R] [Algebra R A]
    [AddCommGroup V] [Module R V]
    {ι : Type*} (b : Module.Basis ι R V)

/--
The `A`-algebra isomorphism `A ⊗[R] V ≃ₗ[A] (ι → A)` coming from an
`ι`-indexed basis of a finite free `R`-module `V`.
-/
@[simps! apply symm_apply]
/-
**Algebra.TensorProduct.equivPiOfFiniteBasis** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Algebra.TensorProduct.equivPiOfFiniteBasis [Finite ι] : (A otimes[R] V) ≃ₗ
[A] (ι -> A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `A`-algebra isomorphism `A ⊗[R] V ≃ₗ[A] (ι → A)` coming from an
`ι`-indexed basis of a finite free `R`-module `V`.
-/
noncomputable def Algebra.TensorProduct.equivPiOfFiniteBasis [Finite ι] :
    (A ⊗[R] V) ≃ₗ[A] (ι → A) :=
  open scoped Classical in
  have : Fintype ι := .ofFinite _
  (b.equivFun.baseChange R A _ _) ≪≫ₗ TensorProduct.piScalarRight R A A ι

/--
The `A`-algebra isomorphism `A ⊗[R] V ≃ₗ[A] (ι →₀ A)` coming from an
`ι`-indexed basis of a free `R`-module `V`.
-/
@[simps! apply symm_apply]
/-
**Algebra.TensorProduct.equivFinsuppOfBasis** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Algebra.TensorProduct.equivFinsuppOfBasis : (A otimes[R] V) ≃ₗ[A] (ι ->₀ A
)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `A`-algebra isomorphism `A ⊗[R] V ≃ₗ[A] (ι →₀ A)` coming from an
`ι`-indexed basis of a free `R`-module `V`.
-/
noncomputable def Algebra.TensorProduct.equivFinsuppOfBasis :
    (A ⊗[R] V) ≃ₗ[A] (ι →₀ A) :=
  open scoped Classical in
  (b.repr.baseChange R A _ _) ≪≫ₗ TensorProduct.finsuppScalarRight R A A ι
