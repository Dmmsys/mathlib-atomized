/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Geißer, Michael Stoll
-/
module

public import Mathlib.Algebra.ContinuedFractions.Computation.ApproximationCorollaries
public import Mathlib.Algebra.ContinuedFractions.Computation.Translations
public import Mathlib.NumberTheory.DiophantineApproximation.Basic

/-!
# Diophantine Approximation using continued fractions

## Main statements

There are two versions of Legendre's Theorem.`Real.exists_rat_eq_convergent`,
defined in `Mathlib/NumberTheory/DiophantineApproximation/Basic.lean`, uses `Real.convergent`,
a simple recursive definition of the convergents that is also defined in that file.
This file provides `Real.exists_convs_eq_rat`, using `GenContFract.convs` of `GenContFract.of ξ`.
-/

public section

section Convergent

namespace Real

open Int

/-!
Our `convergent`s agree with `GenContFract.convs`.
-/

open GenContFract

/--
theorem `convs_eq_convergent` / 定理 `convs_eq_convergent`

English:
theorem convs_eq_convergent
  given: (ξ : Real) (n : Nat)
  proof: by
  induction n generalizing ξ with
  | zero => simp only [zeroth_conv_eq_h, of_h_eq_floor, convergent_zero, Rat.cast_intCast]
  | succ n ih => rw [convs_succ, ih (fract ξ)⁻¹, convergent_succ, one_div]; norm_cast

中文:
定理 convs_eq_convergent
  条件: (ξ : 实数) (n : 自然数)
  证明: by
  induction n generalizing ξ with
  | zero => simp only [zeroth_conv_eq_h, of_h_eq_floor, convergent_zero, Rat.cast_intCast]
  | succ n ih => rw [convs_succ, ih (fract ξ)⁻¹, convergent_succ, one_div]; norm_cast

Depends on / 依赖: Rat.cast_intCast, cast_intCast, convergent_succ, convergent_zero, convs_succ, generalizing, of_h_eq_floor, one_div, zeroth_conv_eq_h
-/
theorem convs_eq_convergent (ξ : Real) (n : Nat) :
    (GenContFract.of ξ).convs n = ξ.convergent n := by
  induction n generalizing ξ with
  | zero => simp only [zeroth_conv_eq_h, of_h_eq_floor, convergent_zero, Rat.cast_intCast]
  | succ n ih => rw [convs_succ, ih (fract ξ)⁻¹, convergent_succ, one_div]; norm_cast

end Real

end Convergent

namespace Real

variable {ξ : Real} {u v : Int}

/--
theorem `exists_convs_eq_rat` / 定理 `exists_convs_eq_rat`

English:
theorem exists_convs_eq_rat
  statement: {q : Rat}
  proof: by
  obtain ⟨n, hn⟩ := exists_rat_eq_convergent h
  exact ⟨n, hn.symm ▸ convs_eq_convergent ξ n⟩

中文:
定理 exists_convs_eq_rat
  结论: {q : Rat}
  证明: by
  obtain ⟨n, hn⟩ := exists_rat_eq_convergent h
  exact ⟨n, hn.symm ▸ convs_eq_convergent ξ n⟩

Depends on / 依赖: convs_eq_convergent, exists_rat_eq_convergent, hn.symm
-/
theorem exists_convs_eq_rat {q : Rat}
    (h : |ξ - q| < 1 / (2 * (q.den : Real) ^ 2)) : exists n, (GenContFract.of ξ).convs n = q := by
  obtain ⟨n, hn⟩ := exists_rat_eq_convergent h
  exact ⟨n, hn.symm ▸ convs_eq_convergent ξ n⟩

end Real
