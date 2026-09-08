/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# Linear independence and algebra maps

This file collects results relating linear independence along algebra maps.

These results cannot go in `LinearAlgebra/LinearIndependent/Basic.lean` due to the algebra import.
-/

public section

variable {R S A : Type*} [CommSemiring R] [CommSemiring S] [Semiring A]
  [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A] [FaithfulSMul S A]

@[simp]
/-
**LinearIndependent.algebraMap_comp_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndependent.algebraMap_comp_iff {ι : Type*} {v : ι -> S} : LinearInd
ependent R (algebraMap S A ∘ v) ↔ LinearIndependent R v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.linearIndependent_iff_of_injOn`：∀ {ι : Type u'} {R : Type u_2}
 {M : Type u_4} {M' : Type u_5} {v : ι → M} [inst : Semiring R] [inst_1 : AddCom
mMonoid M]   [inst_2 : AddComm…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem LinearIndependent.algebraMap_comp_iff {ι : Type*} {v : ι → S} :
    LinearIndependent R (algebraMap S A ∘ v) ↔ LinearIndependent R v :=
  (IsScalarTower.toAlgHom R S A).toLinearMap.linearIndependent_iff_of_injOn (by simp)

@[simp]
/-
**LinearIndepOn.algebraMap_comp_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndepOn.algebraMap_comp_iff {ι : Type*} {v : ι -> S} {s : Set ι} : L
inearIndepOn R (algebraMap S A ∘ v) s ↔ LinearIndepOn R v s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIndependent.algebraMap_comp_iff`：LinearIndependent.algebraMap_comp
_iff {ι : Type*} {v : ι -> S} : LinearIndependent R (algebraMap S A ∘ v) ↔ Linea
rIndependent R v
-/
theorem LinearIndepOn.algebraMap_comp_iff {ι : Type*} {v : ι → S} {s : Set ι} :
    LinearIndepOn R (algebraMap S A ∘ v) s ↔ LinearIndepOn R v s :=
  LinearIndependent.algebraMap_comp_iff

@[simp]
/-
**LinearIndepOn.id_image_algebraMap_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndepOn.id_image_algebraMap_iff {s : Set S} : LinearIndepOn R id (al
gebraMap S A '' s) ↔ LinearIndepOn R id s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `linearIndepOn_iff_image`：linearIndepOn_iff_image {ι} {s : Set ι} {f : ι 
-> M} (hf : Set.InjOn f s) : LinearIndepOn R f s ↔ LinearIndepOn R id (f '' s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `LinearIndepOn.algebraMap_comp_iff`：LinearIndepOn.algebraMap_comp_iff {ι 
: Type*} {v : ι -> S} {s : Set ι} : LinearIndepOn R (algebraMap S A ∘ v) s ↔ Lin
earIndepOn R v s
-/
theorem LinearIndepOn.id_image_algebraMap_iff {s : Set S} :
    LinearIndepOn R id (algebraMap S A '' s) ↔ LinearIndepOn R id s :=
  (linearIndepOn_iff_image (by simp)).symm.trans LinearIndepOn.algebraMap_comp_iff
