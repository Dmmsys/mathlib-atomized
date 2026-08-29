/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Evaluation of polynomials in an algebra

This file concerns evaluating polynomials where the map is `algebraMap`

TODO: merge with parts of `Mathlib/Algebra/Polynomial/AlgebraMap.lean`?
-/

public section

noncomputable section

open Finset AddMonoidAlgebra

open Polynomial

namespace Polynomial

universe u v w y

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : Nat}

section CommSemiring

section Eval

section Algebra

variable [CommSemiring R] [Semiring S] [Algebra R S] (x : S) (p q : R[X])

@[simp]
/--
theorem `eval₂_mul'` / 定理 `eval₂_mul'`

English:
theorem eval₂_mul'
  proof: by
  exact eval₂_mul_noncomm _ _ fun k => Algebra.commute_algebraMap_left (coeff q k) x

@[simp]

中文:
定理 eval₂_mul'
  证明: by
  exact eval₂_mul_noncomm _ _ fun k => Algebra.commute_algebraMap_left (coeff q k) x

@[simp]

Depends on / 依赖: Algebra, Algebra.commute_algebraMap_left, commute_algebraMap_left
-/
theorem eval₂_mul' :
    (p * q).eval₂ (algebraMap R S) x = p.eval₂ (algebraMap R S) x * q.eval₂ (algebraMap R S) x := by
  exact eval₂_mul_noncomm _ _ fun k => Algebra.commute_algebraMap_left (coeff q k) x

@[simp]
/--
theorem `eval₂_pow'` / 定理 `eval₂_pow'`

English:
theorem eval₂_pow'
  given: (n : Nat)
  proof: by
  induction n with
  | zero => simp only [pow_zero, eval₂_one]
  | succ n ih => rw [pow_succ, pow_succ, eval₂_mul', ih]

@[simp]

中文:
定理 eval₂_pow'
  条件: (n : 自然数)
  证明: by
  induction n with
  | zero => simp only [pow_zero, eval₂_one]
  | succ n ih => rw [pow_succ, pow_succ, eval₂_mul', ih]

@[simp]

Depends on / 依赖: pow_succ, pow_zero
-/
theorem eval₂_pow' (n : Nat) :
    (p ^ n).eval₂ (algebraMap R S) x = (p.eval₂ (algebraMap R S) x) ^ n := by
  induction n with
  | zero => simp only [pow_zero, eval₂_one]
  | succ n ih => rw [pow_succ, pow_succ, eval₂_mul', ih]

@[simp]
/--
theorem `eval₂_comp'` / 定理 `eval₂_comp'`

English:
theorem eval₂_comp'
  statement: eval₂ (algebraMap R S) x (p.comp q) =
  proof: by
  induction p using Polynomial.induction_on' with
  | add r s hr hs => simp only [add_comp, eval₂_add, hr, hs]
  | monomial n a => simp only [monomial_comp, eval₂_mul', eval₂_C, eval₂_monomial, eval₂_pow']

中文:
定理 eval₂_comp'
  结论: eval₂ (algebraMap R S) x (p.comp q) =
  证明: by
  induction p using Polynomial.induction_on' with
  | add r s hr hs => simp only [add_comp, eval₂_add, hr, hs]
  | monomial n a => simp only [monomial_comp, eval₂_mul', eval₂_C, eval₂_monomial, eval₂_pow']

Depends on / 依赖: Polynomial, Polynomial.induction_on, add_comp, induction_on, monomial, monomial_comp
-/
theorem eval₂_comp' : eval₂ (algebraMap R S) x (p.comp q) =
    eval₂ (algebraMap R S) (eval₂ (algebraMap R S) x q) p := by
  induction p using Polynomial.induction_on' with
  | add r s hr hs => simp only [add_comp, eval₂_add, hr, hs]
  | monomial n a => simp only [monomial_comp, eval₂_mul', eval₂_C, eval₂_monomial, eval₂_pow']

end Algebra

end Eval

end CommSemiring

end Polynomial
