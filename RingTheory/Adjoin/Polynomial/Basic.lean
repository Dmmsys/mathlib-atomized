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

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : Nat}

section aeval

open Algebra

variable [CommSemiring R] [Semiring A] [CommSemiring A'] [Semiring B]
variable [Algebra R A] [Algebra R B]
variable {p q : R[X]} (x : A)

@[simp]
/--
theorem `_root_.Polynomial.adjoin_X` / 定理 `_root_.Polynomial.adjoin_X`

English:
theorem _root_.Polynomial.adjoin_X
  statement: adjoin R ({X} : Set R[X]) = ⊤
  proof: by
  refine top_unique fun p _hp => ?_
  set S := adjoin R ({X} : Set R[X])
  rw [← sum_monomial_eq p]; simp only [← smul_X_eq_monomial]
  exact S.sum_mem fun n _hn => S.smul_mem (S.pow_mem (subset_adjoin rfl) _) _

中文:
定理 _root_.多项式.adjoin_X
  结论: adjoin R ({X} : 集合 R[X]) = ⊤
  证明: by
  refine top_unique fun p _hp => ?_
  set S := adjoin R ({X} : Set R[X])
  rw [← sum_monomial_eq p]; simp only [← smul_X_eq_monomial]
  exact S.sum_mem fun n _hn => S.smul_mem (S.pow_mem (subset_adjoin rfl) _) _

Depends on / 依赖: S.pow_mem, S.smul_mem, S.sum_mem, adjoin, pow_mem, smul_X_eq_monomial, smul_mem, subset_adjoin, sum_mem, sum_monomial_eq, top_unique
-/
theorem _root_.Polynomial.adjoin_X : adjoin R ({X} : Set R[X]) = ⊤ := by
  refine top_unique fun p _hp => ?_
  set S := adjoin R ({X} : Set R[X])
  rw [← sum_monomial_eq p]; simp only [← smul_X_eq_monomial]
  exact S.sum_mem fun n _hn => S.smul_mem (S.pow_mem (subset_adjoin rfl) _) _

variable (R)
/--
theorem `adjoin_singleton_eq_range_aeval` / 定理 `adjoin_singleton_eq_range_aeval`

English:
theorem adjoin_singleton_eq_range_aeval
  given: (x : A)
  proof: by
  rw [← Algebra.map_top]; rw [← adjoin_X]; rw [AlgHom.map_adjoin]; rw [Set.image_singleton]; rw [aeval_X]

@[simp]

中文:
定理 adjoin_singleton_eq_range_aeval
  条件: (x : A)
  证明: by
  rw [← Algebra.map_top]; rw [← adjoin_X]; rw [AlgHom.map_adjoin]; rw [Set.image_singleton]; rw [aeval_X]

@[simp]

Depends on / 依赖: AlgHom, AlgHom.map_adjoin, Algebra, Algebra.map_top, Set.image_singleton, adjoin_X, aeval_X, image_singleton, map_adjoin, map_top
-/
theorem adjoin_singleton_eq_range_aeval (x : A) :
    adjoin R {x} = (aeval x).range := by
  rw [← Algebra.map_top]; rw [← adjoin_X]; rw [AlgHom.map_adjoin]; rw [Set.image_singleton]; rw [aeval_X]

@[simp]
/--
theorem `_root_.Polynomial.aeval_mem_adjoin_singleton` / 定理 `_root_.Polynomial.aeval_mem_adjoin_singleton`

English:
theorem _root_.Polynomial.aeval_mem_adjoin_singleton
  statement: aeval x p in adjoin R {x}
  proof: by
  simp [adjoin_singleton_eq_range_aeval]

中文:
定理 _root_.多项式.aeval_mem_adjoin_singleton
  结论: aeval x p in adjoin R {x}
  证明: by
  simp [adjoin_singleton_eq_range_aeval]

Depends on / 依赖: adjoin_singleton_eq_range_aeval
-/
theorem _root_.Polynomial.aeval_mem_adjoin_singleton : aeval x p in adjoin R {x} := by
  simp [adjoin_singleton_eq_range_aeval]

instance {A B : Type*} [CommSemiring A] [Semiring B] [Algebra A B] (x : B) (p : Polynomial A) :
    CoeDep B (p.aeval x) (Algebra.adjoin A {x}) where
  coe := ⟨p.aeval x, aeval_mem_adjoin_singleton A x⟩

/--
theorem `adjoin_mem_exists_aeval` / 定理 `adjoin_mem_exists_aeval`

English:
theorem adjoin_mem_exists_aeval
  given: {a : A} (h : a in R[x])
  proof: by
  rw [Algebra.adjoin_singleton_eq_range_aeval] at h
  simp_all

中文:
定理 adjoin_mem_存在_aeval
  条件: {a : A} (h : a in R[x])
  证明: by
  rw [Algebra.adjoin_singleton_eq_range_aeval] at h
  simp_all

Depends on / 依赖: Algebra, Algebra.adjoin_singleton_eq_range_aeval, adjoin_singleton_eq_range_aeval
-/
theorem adjoin_mem_exists_aeval {a : A} (h : a in R[x]) :
    exists p : R[X], aeval x p = a := by
  rw [Algebra.adjoin_singleton_eq_range_aeval] at h
  simp_all

/--
theorem `adjoin_eq_exists_aeval` / 定理 `adjoin_eq_exists_aeval`

English:
theorem adjoin_eq_exists_aeval
  given: (a : R[x])
  proof: by
  have : (a : A) in R[x] := by simp
  set y := (a : A) with h
  rw [Algebra.adjoin_singleton_eq_range_aeval] at this
  simp_all

中文:
定理 adjoin_eq_存在_aeval
  条件: (a : R[x])
  证明: by
  have : (a : A) in R[x] := by simp
  set y := (a : A) with h
  rw [Algebra.adjoin_singleton_eq_range_aeval] at this
  simp_all

Depends on / 依赖: Algebra, Algebra.adjoin_singleton_eq_range_aeval, adjoin_singleton_eq_range_aeval
-/
theorem adjoin_eq_exists_aeval (a : R[x]) :
    exists p : R[X], aeval x p = a := by
  have : (a : A) in R[x] := by simp
  set y := (a : A) with h
  rw [Algebra.adjoin_singleton_eq_range_aeval] at this
  simp_all

/--
Proving a fact about `a : adjoin R {x}` is the same as proving it for
`aeval x p` where `p`is an arbitrary polynomial. -/
@[elab_as_elim]
/--
theorem `adjoin_singleton_induction` / 定理 `adjoin_singleton_induction`

English:
theorem adjoin_singleton_induction
  statement: {M : (adjoin R {x}) -> Prop}
  proof: by
  obtain ⟨p, hp⟩ := Algebra.adjoin_eq_exists_aeval _ x a
  grind

中文:
定理 adjoin_singleton_induction
  结论: {M : (adjoin R {x}) -> 命题}
  证明: by
  obtain ⟨p, hp⟩ := Algebra.adjoin_eq_exists_aeval _ x a
  grind

Depends on / 依赖: Algebra, Algebra.adjoin_eq_exists_aeval, adjoin_eq_exists_aeval
-/
theorem adjoin_singleton_induction {M : (adjoin R {x}) -> Prop}
    (a : adjoin R {x}) (f : forall (p : Polynomial R), M (aeval x p : adjoin R {x})) : M a := by
  obtain ⟨p, hp⟩ := Algebra.adjoin_eq_exists_aeval _ x a
  grind

/--
Instance `instCommSemiringAdjoinSingleton` / 实例 `instCommSemiringAdjoinSingleton`

English:
instance instCommSemiringAdjoinSingleton
  signature: :
  body: fun ⟨p, hp⟩ ⟨q, hq⟩ => by
      obtain ⟨p', rfl⟩ := Algebra.adjoin_singleton_eq_range_aeval R x ▸ hp
      obtain ⟨q', rfl⟩ := Algebra.adjoin_singleton_eq_range_aeval R x ▸ hq
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MulMemClass.mk_mul_mk, ← map_mul,
        mul_comm p' q']

中文:
实例 instCommSemiringAdjoinSingleton
  签名: :
  定义体: fun ⟨p, hp⟩ ⟨q, hq⟩ => by
      obtain ⟨p', rfl⟩ := Algebra.adjoin_singleton_eq_range_aeval R x ▸ hp
      obtain ⟨q', rfl⟩ := Algebra.adjoin_singleton_eq_range_aeval R x ▸ hq
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MulMemClass.mk_mul_mk, ← map_mul,
        mul_comm p' q']

Depends on / 依赖: AlgHom, AlgHom.toRingHom_eq_coe, Algebra, Algebra.adjoin_singleton_eq_range_aeval, MulMemClass, MulMemClass.mk_mul_mk, RingHom, RingHom.coe_coe, adjoin_singleton_eq_range_aeval, coe_coe, map_mul, mk_mul_mk, mul_comm, toRingHom_eq_coe
-/
instance instCommSemiringAdjoinSingleton :
CommSemiring adjoin R {x} where
  mul_comm := fun ⟨p, hp⟩ ⟨q, hq⟩ => by
      obtain ⟨p', rfl⟩ := Algebra.adjoin_singleton_eq_range_aeval R x ▸ hp
      obtain ⟨q', rfl⟩ := Algebra.adjoin_singleton_eq_range_aeval R x ▸ hq
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MulMemClass.mk_mul_mk, ← map_mul,
        mul_comm p' q']

/--
Instance `instCommRingAdjoinSingleton` / 实例 `instCommRingAdjoinSingleton`

English:
instance instCommRingAdjoinSingleton
  signature: {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (x : A)

中文:
实例 instCommRingAdjoinSingleton
  签名: {R A : 类型} [交换环 R] [环 A] [代数 R A] (x : A)
-/
instance instCommRingAdjoinSingleton {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (x : A) :
CommRing R[x] where

end aeval

end Algebra
