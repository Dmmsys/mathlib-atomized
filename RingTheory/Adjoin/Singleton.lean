/-
Copyright (c) 2025 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux, María Inés de Frutos Fernández
-/
module

public import Mathlib.RingTheory.Adjoin.Polynomial.Basic
public import Mathlib.RingTheory.Polynomial.Tower
/-!
# Adjoin one single element

This file contains basic results on `Algebra.adjoin`, specifically on adjoining singletons.

## Tags

adjoin, algebra, ringhom

-/

@[expose] public section

variable {A B C : Type*} [CommSemiring A] [CommSemiring B] [CommSemiring C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] (b : B)

namespace Algebra

open Polynomial

/-- Ring homomorphism between `A[b]` and `A[↑b]`. -/
/-
**Algebra.RingHom.adjoinAlgebraMap** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.RingHom`。
形式化陈述：{A : Type u_1} →   {B : Type u_2} →     {C : Type u_3} →       [inst : Com
mSemiring A] →         [inst_1 : CommSemiring B] →           [inst_2 : CommSemir
ing C] →             [inst_3 : Algebra A B] →               [inst_4 : Algebra B 
C] →                 [inst_5 : Algebra A C] → [IsScalarTower A B C] → (b : B) → 
↥A[b] →+* ↥A[(algebraMap B C) b]
参数：b : B；algebraMap B C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Ring homomorphism between `A[b]` and `A[↑b]`.
-/
def RingHom.adjoinAlgebraMap :
    A[b] →+* A[(algebraMap B C) b] :=
  RingHom.codRestrict (((Algebra.ofId B C).restrictScalars A).comp
    (Subalgebra.val A[b])) _
    (fun x ↦ by induction x using adjoin_singleton_induction with
      | f p => aesop (add norm [adjoin_singleton_eq_range_aeval, aeval_algebraMap_apply]))

@[simp]
/-
**Algebra.RingHom.adjoinAlgebraMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Ring
Hom`。
形式化陈述：∀ {A : Type u_1} {B : Type u_2} {C : Type u_3} [inst : CommSemiring A] [in
st_1 : CommSemiring B]   [inst_2 : CommSemiring C] [inst_3 : Algebra A B] [inst_
4 : Algebra B C] [inst_5 : Algebra A C]   [inst_6 : IsScalarTower A B C] (b : B)
 (x : ↥A[b]), ↑((Algebra.RingHom.adjoinAlgebraMap b) x) = (algebraMap B C) ↑x
参数：b : B；x : ↥A[b]；(Algebra.RingHom.adjoinAlgebraMap b) x；algebraMap B C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem RingHom.adjoinAlgebraMap_apply (x : A[b]) :
    (RingHom.adjoinAlgebraMap b x (C := C) : C) = algebraMap B C x := rfl

@[deprecated (since := "2026-02-27")]
alias RingHom.adjoin_algebraMap_apply := RingHom.adjoinAlgebraMap_apply
/-
**Algebra.RingHom.adjoinAlgebraMap_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
.RingHom`。
形式化陈述：∀ {A : Type u_1} {B : Type u_2} {C : Type u_3} [inst : CommSemiring A] [in
st_1 : CommSemiring B]   [inst_2 : CommSemiring C] [inst_3 : Algebra A B] [inst_
4 : Algebra B C] [inst_5 : Algebra A C]   [inst_6 : IsScalarTower A B C] (b : B)
, Function.Surjective ⇑(Algebra.RingHom.adjoinAlgebraMap b)
参数：b : B；Algebra.RingHom.adjoinAlgebraMap b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.adjoin_eq_exists_aeval`：adjoin_eq_exists_aeval (a : R[x]) : exis
ts p : R[X], aeval x p = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.aeval_algebraMap_apply`：aeval_algebraMap_apply (x : A) (p : R
[X]) : aeval (algebraMap A B x) p = algebraMap A B (aeval x p)
-/
theorem RingHom.adjoinAlgebraMap_surjective :
    Function.Surjective (RingHom.adjoinAlgebraMap (A := A) b (C := C)) := by
  intro c
  obtain ⟨p, hp⟩ := adjoin_eq_exists_aeval A (algebraMap B C b) c
  aesop (add safe ((aeval_algebraMap_apply C b p).symm))

@[deprecated (since := "2026-02-27")]
alias RingHom.adjoin_algebraMap_surjective := RingHom.adjoinAlgebraMap_surjective
/-
**Algebra.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Algebra A[b] A[(algebraMap B C) b] :=
  RingHom.toAlgebra (RingHom.adjoinAlgebraMap b)
/-
**Algebra.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsScalarTower A[b] A[(algebraMap B C) b] C :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- If the `algebraMap` injective then we have a Ring isomorphism between A[b] and A[↑b]. -/
/-
**Algebra.RingHom.adjoinAlgebraMapEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.RingH
om`。
形式化陈述：{A : Type u_1} →   {B : Type u_2} →     {C : Type u_3} →       [inst : Com
mSemiring A] →         [inst_1 : CommSemiring B] →           [inst_2 : CommSemir
ing C] →             [inst_3 : Algebra A B] →               [inst_4 : Algebra B 
C] →                 [inst_5 : Algebra A C] →                   [IsScalarTower A
 B C] → (b : B) → [FaithfulSMul B C] → ↥A[b] ≃+* ↥A[(algebraMap B C) b]
参数：b : B；algebraMap B C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the `algebraMap` injective then we have a Ring isomorphism between A[b] and A
[↑b].
-/
noncomputable def RingHom.adjoinAlgebraMapEquiv [FaithfulSMul B C] :
    A[b] ≃+* A[(algebraMap B C) b] := by
  apply RingEquiv.ofBijective (RingHom.adjoinAlgebraMap b)
     ((Function.bijective_iff_existsUnique (adjoinAlgebraMap b)).mpr (fun y ↦ ?_))
  induction y using Algebra.adjoin_singleton_induction with | f p =>
  use ⟨p.aeval b, by simp⟩
  aesop (add norm [Polynomial.aeval_algebraMap_apply, Subtype.ext_iff])

end Algebra

