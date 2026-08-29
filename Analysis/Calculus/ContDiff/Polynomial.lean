/-
Copyright (c) 2025 Geoffrey Irving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Irving
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Higher smoothness of polynomials

We prove that polynomials are `C^∞`.
-/

public section

namespace Polynomial

/--
lemma `contDiff_aeval` / 引理 `contDiff_aeval`

English:
lemma contDiff_aeval
  statement: {R 𝕜 : Type*} [CommSemiring R] [NontriviallyNormedField 𝕜] [Algebra R 𝕜]
  proof: by
  induction f using Polynomial.induction_on' with
  | add f g fc gc => simpa using fc.add gc
  | monomial n a => simpa using contDiff_const.mul (contDiff_id.pow _)

中文:
引理 contDiff_aeval
  结论: {R 𝕜 : 类型} [交换半环 R] [NontriviallyNormedField 𝕜] [代数 R 𝕜]
  证明: by
  induction f using Polynomial.induction_on' with
  | add f g fc gc => simpa using fc.add gc
  | monomial n a => simpa using contDiff_const.mul (contDiff_id.pow _)

Depends on / 依赖: Polynomial, Polynomial.induction_on, contDiff_const, contDiff_const.mul, contDiff_id, contDiff_id.pow, fc.add, induction_on, monomial
-/
lemma contDiff_aeval {R 𝕜 : Type*} [CommSemiring R] [NontriviallyNormedField 𝕜] [Algebra R 𝕜]
    (f : Polynomial R) (n : WithTop Nat∞) : ContDiff 𝕜 n (fun x : 𝕜 => f.aeval x) := by
  induction f using Polynomial.induction_on' with
  | add f g fc gc => simpa using fc.add gc
  | monomial n a => simpa using contDiff_const.mul (contDiff_id.pow _)

end Polynomial
