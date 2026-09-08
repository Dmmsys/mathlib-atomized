/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Polynomials and adjoining roots

## Main results

* `Algebra.instCommSemiringAdjoinSingleton, Algebra.instCommRingAdjoinSingleton`:
  adjoining an element to a commutative (semi)ring gives a commutative (semi)ring
* `Algebra.adjoin_singleton_induction`:
  proving a fact about `a : adjoin R {x}` is the same as proving it for `aeval x p` where `p`
  is an arbitrary polynomial
-/

public section

noncomputable section

open Finset

open Polynomial

namespace Algebra

universe u v w z

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

section aeval

open Algebra

variable [CommSemiring R] [Semiring A] [CommSemiring A'] [Semiring B]
variable [Algebra R A] [Algebra R B]
variable {p q : R[X]} (x : A)

@[simp]
/-
**Algebra._root_.Polynomial.adjoin_X** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Polynomial.adjoin_X : adjoin R ({X} : Set R[X]) = ⊤ := by
  refine top_unique fun p _hp => ?_
  set S := adjoin R ({X} : Set R[X])
  rw [← sum_monomial_eq p]; simp only [← smul_X_eq_monomial]
  exact S.sum_mem fun n _hn => S.smul_mem (S.pow_mem (subset_adjoin rfl) _) _

variable (R)
/-
**Algebra.adjoin_singleton_eq_range_aeval** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：adjoin_singleton_eq_range_aeval (x : A) : adjoin R {x} = (aeval x).range
参数：x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.map_top`：map_top (f : A ->ₐ[R] B) : (⊤ : Subalgebra R A).map f =
 f.range
· 使用定理 `Polynomial.adjoin_X`：∀ {R : Type u} [inst : CommSemiring R], R[Polynomia
l.X] = ⊤
· 使用定理 `AlgHom.map_adjoin`：map_adjoin (φ : A ->ₐ[R] B) (s : Set A) : (adjoin R s
).map φ = adjoin R (φ '' s)
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
-/
theorem adjoin_singleton_eq_range_aeval (x : A) :
    adjoin R {x} = (aeval x).range := by
  rw [← Algebra.map_top, ← adjoin_X, AlgHom.map_adjoin, Set.image_singleton, aeval_X]

@[simp]
/-
**Algebra._root_.Polynomial.aeval_mem_adjoin_singleton** 是 Mathlib 中的一个定理，位于命名空间
 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Polynomial.aeval_mem_adjoin_singleton : aeval x p ∈ adjoin R {x} := by
  simp [adjoin_singleton_eq_range_aeval]
/-
**Algebra.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {A B : Type*} [CommSemiring A] [Semiring B] [Algebra A B] (x : B) (p : Polynomial A) :
    CoeDep B (p.aeval x) (Algebra.adjoin A {x}) where
  coe := ⟨p.aeval x, aeval_mem_adjoin_singleton A x⟩
/-
**Algebra.adjoin_mem_exists_aeval** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：adjoin_mem_exists_aeval {a : A} (h : a in R[x]) : exists p : R[X], aeval x
 p = a
参数：h : a in R[x]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.adjoin_singleton_eq_range_aeval`：adjoin_singleton_eq_range_aeval
 (x : A) : adjoin R {x} = (aeval x).range
-/
theorem adjoin_mem_exists_aeval {a : A} (h : a ∈ R[x]) :
    ∃ p : R[X], aeval x p = a := by
  rw [Algebra.adjoin_singleton_eq_range_aeval] at h
  simp_all
/-
**Algebra.adjoin_eq_exists_aeval** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：adjoin_eq_exists_aeval (a : R[x]) : exists p : R[X], aeval x p = a
参数：a : R[x]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Algebra.adjoin_singleton_eq_range_aeval`：adjoin_singleton_eq_range_aeval
 (x : A) : adjoin R {x} = (aeval x).range
-/
theorem adjoin_eq_exists_aeval (a : R[x]) :
    ∃ p : R[X], aeval x p = a := by
  have : (a : A) ∈ R[x] := by simp
  set y := (a : A) with h
  rw [Algebra.adjoin_singleton_eq_range_aeval] at this
  simp_all

/--
Proving a fact about `a : adjoin R {x}` is the same as proving it for
`aeval x p` where `p`is an arbitrary polynomial. -/
@[elab_as_elim]
/-
**Algebra.adjoin_singleton_induction** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：adjoin_singleton_induction {M : (adjoin R {x}) -> Prop} (a : adjoin R {x})
 (f : forall (p : Polynomial R), M (aeval x p : adjoin R {x})) : M a
参数：adjoin R {x}；a : adjoin R {x}；f : forall (p : Polynomial R), M (aeval x p : a
djoin R {x})。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.aeval_mem_adjoin_singleton`：∀ (R : Type u) {A : Type z} [inst
 : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] {p : Polynomial 
R}   (x : A), (Polynomial.a…
· 使用定理 `Algebra.adjoin_eq_exists_aeval`：adjoin_eq_exists_aeval (a : R[x]) : exis
ts p : R[X], aeval x p = a

--- 原说明 ---
Proving a fact about `a : adjoin R {x}` is the same as proving it for
`aeval x p` where `p`is an arbitrary polynomial.
-/
theorem adjoin_singleton_induction {M : (adjoin R {x}) → Prop}
    (a : adjoin R {x}) (f : ∀ (p : Polynomial R), M (aeval x p : adjoin R {x})) : M a := by
  obtain ⟨p, hp⟩ := Algebra.adjoin_eq_exists_aeval _ x a
  grind
/-
**Algebra.instCommSemiringAdjoinSingleton** 是 Mathlib 中的一个实例，位于命名空间 `Algebra`。
形式化陈述：instCommSemiringAdjoinSingleton : CommSemiring adjoin R {x} where mul_comm
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommSemiringAdjoinSingleton :
    CommSemiring <| adjoin R {x} where
  mul_comm := fun ⟨p, hp⟩ ⟨q, hq⟩ ↦ by
      obtain ⟨p', rfl⟩ := Algebra.adjoin_singleton_eq_range_aeval R x ▸ hp
      obtain ⟨q', rfl⟩ := Algebra.adjoin_singleton_eq_range_aeval R x ▸ hq
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MulMemClass.mk_mul_mk, ← map_mul,
        mul_comm p' q']
/-
**Algebra.instCommRingAdjoinSingleton** 是 Mathlib 中的一个定义，位于命名空间 `Algebra`。
形式化陈述：{R : Type u_3} →   {A : Type u_4} → [inst : CommRing R] → [inst_1 : Ring A
] → [inst_2 : Algebra R A] → (x : A) → CommRing ↥R[x]
参数：x : A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommRingAdjoinSingleton {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (x : A) :
    CommRing <| R[x] where

end aeval

end Algebra

