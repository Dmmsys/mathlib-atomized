/-
Copyright (c) 2023 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruben Van de Velde
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Topology.Algebra.Ring.Basic

/-!
# Multivariate polynomials and continuity

In this file we prove the following lemma:

* `MvPolynomial.continuous_eval`: `MvPolynomial.eval` is continuous

## Tags

multivariate polynomial, continuity
-/

public section

variable {X σ : Type*} [TopologicalSpace X] [CommSemiring X] [IsTopologicalSemiring X]
  (p : MvPolynomial σ X)

/--
theorem `MvPolynomial.continuous_eval` / 定理 `MvPolynomial.continuous_eval`

English:
theorem MvPolynomial.continuous_eval
  statement: Continuous fun x => eval x p
  proof: by
  continuity

中文:
定理 多元多项式.continuous_eval
  结论: 连续 fun x => eval x p
  证明: by
  continuity

Depends on / 依赖: continuity
-/
theorem MvPolynomial.continuous_eval : Continuous fun x => eval x p := by
  continuity
