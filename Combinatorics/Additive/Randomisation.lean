/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
public import Mathlib.Combinatorics.Additive.Dissociation

/-!
# Randomising by a function of dissociated support

This file proves that a function from a finite abelian group can be randomised by a function of
dissociated support.

Precisely, for `G` a finite abelian group and two functions `c : AddChar G ℂ → ℝ` and
`d : AddChar G ℂ → ℝ` such that `{ψ | d ψ ≠ 0}` is dissociated, the product of the `c ψ` over `ψ` is
the same as the average over `a` of the product of the `c ψ + Re (d ψ * ψ a)`.
-/

public section

open Finset
open scoped BigOperators ComplexConjugate

variable {G : Type*} [Fintype G] [AddCommGroup G] {p : Nat}

/--
lemma `AddDissociated.randomisation` / 引理 `AddDissociated.randomisation`

English:
lemma AddDissociated.randomisation
  statement: (c : AddChar G Complex -> Real) (d : AddChar G Complex -> Complex)
  proof: by
  refine Complex.ofReal_injective ?_
  push_cast
  calc
    _ = ∑ t, (𝔼 a, ∏ ψ in t, ((d ψ * ψ a) + conj (d ψ * ψ a)) / 2) * ∏ ψ in tᶜ, (c ψ : Complex) := by
        simp_rw [expect_mul, ← expect_sum_comm, ← Fintype.prod_add, add_comm,
          Complex.re_eq_add_conj]
    _ = (𝔼 a, ∏ ψ in ∅, ((d

中文:
引理 AddDissociated.randomisation
  结论: (c : 加法特征 G 复形 -> 实数) (d : 加法特征 G 复形 -> 复形)
  证明: by
  refine Complex.ofReal_injective ?_
  push_cast
  calc
    _ = ∑ t, (𝔼 a, ∏ ψ in t, ((d ψ * ψ a) + conj (d ψ * ψ a)) / 2) * ∏ ψ in tᶜ, (c ψ : Complex) := by
        simp_rw [expect_mul, ← expect_sum_comm, ← Fintype.prod_add, add_comm,
          Complex.re_eq_add_conj]
    _ = (𝔼 a, ∏ ψ in ∅, ((d

Depends on / 依赖: Complex.ofReal_injective, Complex.re_eq_add_conj, Fintype, Fintype.prod_add, Fintype.sum_eq_single, add_comm, expect, expect_mul, expect_sum_comm, map_mul, mul_eq_zero_of_left, ofReal_injective, prod_add, prod_const, prod_div_distrib, re_eq_add_conj, simp_rw, sum_eq_single
-/
lemma AddDissociated.randomisation (c : AddChar G Complex -> Real) (d : AddChar G Complex -> Complex)
    (hcd : AddDissociated {ψ | d ψ != 0}) : 𝔼 a, ∏ ψ, (c ψ + (d ψ * ψ a).re) = ∏ ψ, c ψ := by
  refine Complex.ofReal_injective ?_
  push_cast
  calc
    _ = ∑ t, (𝔼 a, ∏ ψ in t, ((d ψ * ψ a) + conj (d ψ * ψ a)) / 2) * ∏ ψ in tᶜ, (c ψ : Complex) := by
        simp_rw [expect_mul, ← expect_sum_comm, ← Fintype.prod_add, add_comm,
          Complex.re_eq_add_conj]
    _ = (𝔼 a, ∏ ψ in ∅, ((d ψ * ψ a) + conj (d ψ * ψ a)) / 2) * ∏ ψ in ∅ᶜ, (c ψ : Complex) :=
        Fintype.sum_eq_single ∅ fun t ht => mul_eq_zero_of_left ?_ _
    _ = ∏ ψ, (c ψ : Complex) := by simp
  simp only [map_mul, prod_div_distrib, prod_add, prod_const, ← expect_div, expect_sum_comm,
    div_eq_zero_iff, pow_eq_zero_iff', OfNat.ofNat_ne_zero, ne_eq, card_eq_zero,
    false_and, or_false]
  refine sum_eq_zero fun u _ => ?_
  calc
    𝔼 a, (∏ ψ in u, d ψ * ψ a) * ∏ ψ in t \ u, conj (d ψ) * conj (ψ a)
      = ((∏ ψ in u, d ψ) * ∏ ψ in t \ u, conj (d ψ)) * 𝔼 a, (∑ ψ in u, ψ - ∑ ψ in t \ u, ψ) a := by
        simp_rw [mul_expect, AddChar.sub_apply, AddChar.sum_apply, mul_mul_mul_comm,
          ← prod_mul_distrib, AddChar.map_neg_eq_conj]
    _ = 0 := ?_
  rw [mul_eq_zero]; rw [AddChar.expect_eq_zero_iff_ne_zero]; rw [sub_ne_zero]; rw [or_iff_not_imp_left]; rw [← Ne]; rw [mul_ne_zero_iff]; rw [prod_ne_zero_iff]; rw [prod_ne_zero_iff]
  exact fun h => hcd.ne h.1 (by simpa only [map_ne_zero] using! h.2)
    (sdiff_ne_right.2 <| .inl ht).symm
