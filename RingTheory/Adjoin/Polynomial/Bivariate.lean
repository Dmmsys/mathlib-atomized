/-
Copyright (c) 2026 Xavier Généreux, María Inés de Frutos Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux, María Inés de Frutos Fernández
-/
module

public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.Algebra.Ring.Defs

/-!
# Bivariate polynomials and adjoining transcendental elements

## Main results

* `IsAlgebraic.adjoin_singleton`:
  Given two transcendental elements `a`, `b` over `R`, if one of them, say `a`, is algebraic over
  `R[b]` then `b` is algebraic over `R[a]`.
-/

@[expose] public noncomputable section

namespace Polynomial.Bivariate

open Polynomial Bivariate Algebra Transcendental

variable {R A : Type*} [CommRing R]

section Ring

variable [Ring A] [Algebra R A] {x : A}

/--
Definition of `Transcendental.algEquivAdjoin` / `Transcendental.algEquivAdjoin` 的定义

English:
definition Transcendental.algEquivAdjoin
  signature: (hx : Transcendental R x)
  body: mapAlgEquiv (algEquivOfTranscendental _ x hx)

中文:
定义 Transcendental.algEquivAdjoin
  签名: (hx : Transcendental R x)
  定义体: mapAlgEquiv (algEquivOfTranscendental _ x hx)

Depends on / 依赖: algEquivOfTranscendental, mapAlgEquiv
-/
def Transcendental.algEquivAdjoin (hx : Transcendental R x) :
    R[X][Y] ≃ₐ[R] (Algebra.adjoin R {x})[X] :=
  mapAlgEquiv (algEquivOfTranscendental _ x hx)

/--
theorem `Transcendental.algEquivAdjoin_apply` / 定理 `Transcendental.algEquivAdjoin_apply`

English:
theorem Transcendental.algEquivAdjoin_apply
  given: (hx : Transcendental R x) (p : R[X][Y])
  proof: rfl

中文:
定理 Transcendental.algEquivAdjoin_apply
  条件: (hx : Transcendental R x) (p : R[X][Y])
  证明: rfl
-/
theorem Transcendental.algEquivAdjoin_apply (hx : Transcendental R x) (p : R[X][Y]) :
    hx.algEquivAdjoin p = mapAlgHom (aeval ⟨x, self_mem_adjoin_singleton R x⟩) p :=
  rfl

attribute [local instance] algebra in
/--
theorem `Transcendental.algEquivAdjoin_swap_eq_aeval` / 定理 `Transcendental.algEquivAdjoin_swap_eq_aeval`

English:
theorem Transcendental.algEquivAdjoin_swap_eq_aeval
  given: (hx : Transcendental R x) (p : R[X][Y])
  proof: by
  simp [algEquivAdjoin, Bivariate.aveal_eq_map_swap]

中文:
定理 Transcendental.algEquivAdjoin_swap_eq_aeval
  条件: (hx : Transcendental R x) (p : R[X][Y])
  证明: by
  simp [algEquivAdjoin, Bivariate.aveal_eq_map_swap]

Depends on / 依赖: Bivariate, Bivariate.aveal_eq_map_swap, algEquivAdjoin, aveal_eq_map_swap
-/
theorem Transcendental.algEquivAdjoin_swap_eq_aeval (hx : Transcendental R x) (p : R[X][Y]) :
    hx.algEquivAdjoin (swap p) = aeval (C ⟨x, self_mem_adjoin_singleton R x⟩) p := by
  simp [algEquivAdjoin, Bivariate.aveal_eq_map_swap]

end Ring

section CommRing

variable [CommRing A] [Algebra R A]

variable {B : Type*} [CommRing B] [Algebra A B] [Algebra R B] [IsScalarTower R A B]

attribute [local instance] Polynomial.algebra in
/--
theorem `aeval_aeval_eq_aeval_algEquivAdjoin` / 定理 `aeval_aeval_eq_aeval_algEquivAdjoin`

English:
theorem aeval_aeval_eq_aeval_algEquivAdjoin
  statement: {x : A} (y : B)
  proof: by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp_all [map_add]
  | monomial n a =>
    simp_all [aeval_algebraMap_apply, Transcendental.algEquivAdjoin, Subalgebra.algebraMap_def]

中文:
定理 aeval_aeval_eq_aeval_algEquivAdjoin
  结论: {x : A} (y : B)
  证明: by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp_all [map_add]
  | monomial n a =>
    simp_all [aeval_algebraMap_apply, Transcendental.algEquivAdjoin, Subalgebra.algebraMap_def]

Depends on / 依赖: Polynomial, Polynomial.induction_on, Subalgebra, Subalgebra.algebraMap_def, Transcendental, Transcendental.algEquivAdjoin, aeval_algebraMap_apply, algEquivAdjoin, algebraMap_def, induction_on, map_add, monomial
-/
theorem aeval_aeval_eq_aeval_algEquivAdjoin {x : A} (y : B)
    (hx : Transcendental R x) (p : R[X][Y]) :
    aeval (algebraMap A B x) (aeval (C (⟨y, self_mem_adjoin_singleton R y⟩ :
      adjoin R {y})) p) = aeval y (hx.algEquivAdjoin p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp_all [map_add]
  | monomial n a =>
    simp_all [aeval_algebraMap_apply, Transcendental.algEquivAdjoin, Subalgebra.algebraMap_def]

/--
theorem `_root_.IsAlgebraic.adjoin_singleton` / 定理 `_root_.IsAlgebraic.adjoin_singleton`

English:
theorem _root_.IsAlgebraic.adjoin_singleton
  statement: {x : A} {y : B} (hx : Transcendental R x)
  proof: by
  obtain ⟨f, hnezero, halg⟩ := h
  refine ⟨hy.algEquivAdjoin (swap (hx.algEquivAdjoin.symm f)),
    by simpa only [map_ne_zero_iff _ (AlgEquiv.injective _)], ?_⟩
  simpa [Transcendental.algEquivAdjoin_swap_eq_aeval hy, aeval_aeval_eq_aeval_algEquivAdjoin y hx]

中文:
定理 _root_.IsAlgebraic.adjoin_singleton
  结论: {x : A} {y : B} (hx : Transcendental R x)
  证明: by
  obtain ⟨f, hnezero, halg⟩ := h
  refine ⟨hy.algEquivAdjoin (swap (hx.algEquivAdjoin.symm f)),
    by simpa only [map_ne_zero_iff _ (AlgEquiv.injective _)], ?_⟩
  simpa [Transcendental.algEquivAdjoin_swap_eq_aeval hy, aeval_aeval_eq_aeval_algEquivAdjoin y hx]

Depends on / 依赖: AlgEquiv, AlgEquiv.injective, Transcendental, Transcendental.algEquivAdjoin_swap_eq_aeval, aeval_aeval_eq_aeval_algEquivAdjoin, algEquivAdjoin, algEquivAdjoin_swap_eq_aeval, hnezero, hx.algEquivAdjoin.symm, hy.algEquivAdjoin, injective, map_ne_zero_iff
-/
theorem _root_.IsAlgebraic.adjoin_singleton {x : A} {y : B} (hx : Transcendental R x)
    (hy : Transcendental R y) (h : IsAlgebraic (adjoin R {x}) y) :
    IsAlgebraic (adjoin R {y}) (algebraMap A B x) := by
  obtain ⟨f, hnezero, halg⟩ := h
  refine ⟨hy.algEquivAdjoin (swap (hx.algEquivAdjoin.symm f)),
    by simpa only [map_ne_zero_iff _ (AlgEquiv.injective _)], ?_⟩
  simpa [Transcendental.algEquivAdjoin_swap_eq_aeval hy, aeval_aeval_eq_aeval_algEquivAdjoin y hx]

end CommRing

end Polynomial.Bivariate

end
