/-
Copyright (c) 2024 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-!
# Cyclotomic extensions of `ℚ` are totally complex number fields.

We prove that cyclotomic extensions of `ℚ` are totally complex, meaning that
`NrRealPlaces K = 0` if `IsCyclotomicExtension {n} ℚ K` and `2 < n`.

## Main results
* `nrRealPlaces_eq_zero`: If `K` is an `n`-th cyclotomic extension of `ℚ`, where `2 < n`,
  then there are no real places of `K`.
-/

public section

universe u

namespace IsCyclotomicExtension.Rat

open NumberField InfinitePlace Module Complex Nat Polynomial

variable {n : Nat} [NeZero n] (K : Type u) [Field K] [CharZero K]

/--
theorem `nrRealPlaces_eq_zero` / 定理 `nrRealPlaces_eq_zero`

English:
theorem nrRealPlaces_eq_zero
  given: [IsCyclotomicExtension {n} Rat K] (hn : 2 < n)
  proof: IsCyclotomicExtension.numberField {n} Rat K
    nrRealPlaces K = 0 := by
  have := IsCyclotomicExtension.numberField {n} Rat K
  apply (IsCyclotomicExtension.zeta_spec n Rat K).nrRealPlaces_eq_zero_of_two_lt hn

中文:
定理 nrRealPlaces_eq_zero
  条件: [IsCyclotomicExtension {n} Rat K] (hn : 2 < n)
  证明: IsCyclotomicExtension.numberField {n} Rat K
    nrRealPlaces K = 0 := by
  have := IsCyclotomicExtension.numberField {n} Rat K
  apply (IsCyclotomicExtension.zeta_spec n Rat K).nrRealPlaces_eq_zero_of_two_lt hn

Depends on / 依赖: IsCyclotomicExtension, IsCyclotomicExtension.numberField, numberField
-/
theorem nrRealPlaces_eq_zero [IsCyclotomicExtension {n} Rat K] (hn : 2 < n) :
    haveI := IsCyclotomicExtension.numberField {n} Rat K
    nrRealPlaces K = 0 := by
  have := IsCyclotomicExtension.numberField {n} Rat K
  apply (IsCyclotomicExtension.zeta_spec n Rat K).nrRealPlaces_eq_zero_of_two_lt hn

/--
theorem `isTotallyComplex` / 定理 `isTotallyComplex`

English:
theorem isTotallyComplex
  given: [IsCyclotomicExtension {n} Rat K] (hn : 2 < n)
  proof: by
  have := IsCyclotomicExtension.numberField {n} Rat K
exact nrRealPlaces_eq_zero_iff.mp nrRealPlaces_eq_zero K hn

中文:
定理 isTotallyComplex
  条件: [IsCyclotomicExtension {n} Rat K] (hn : 2 < n)
  证明: by
  have := IsCyclotomicExtension.numberField {n} Rat K
exact nrRealPlaces_eq_zero_iff.mp nrRealPlaces_eq_zero K hn

Depends on / 依赖: IsCyclotomicExtension, IsCyclotomicExtension.numberField, nrRealPlaces_eq_zero, nrRealPlaces_eq_zero_iff, nrRealPlaces_eq_zero_iff.mp, numberField
-/
theorem isTotallyComplex [IsCyclotomicExtension {n} Rat K] (hn : 2 < n) :
    IsTotallyComplex K := by
  have := IsCyclotomicExtension.numberField {n} Rat K
exact nrRealPlaces_eq_zero_iff.mp nrRealPlaces_eq_zero K hn

variable (n)

/--
theorem `nrComplexPlaces_eq_totient_div_two` / 定理 `nrComplexPlaces_eq_totient_div_two`

English:
theorem nrComplexPlaces_eq_totient_div_two
  given: [h : IsCyclotomicExtension {n} Rat K]
  proof: IsCyclotomicExtension.numberField {n} Rat K
    nrComplexPlaces K = φ n / 2 := by
  have := IsCyclotomicExtension.numberField {n} Rat K
  by_cases hn : 2 < n
  · obtain ⟨k, hk : φ n = k + k⟩ := totient_even hn
    have key := card_add_two_mul_card_eq_rank K
    rw [nrRealPlaces_eq_zero K hn]; rw [ze

中文:
定理 nrComplexPlaces_eq_totient_div_two
  条件: [h : IsCyclotomicExtension {n} Rat K]
  证明: IsCyclotomicExtension.numberField {n} Rat K
    nrComplexPlaces K = φ n / 2 := by
  have := IsCyclotomicExtension.numberField {n} Rat K
  by_cases hn : 2 < n
  · obtain ⟨k, hk : φ n = k + k⟩ := totient_even hn
    have key := card_add_two_mul_card_eq_rank K
    rw [nrRealPlaces_eq_zero K hn]; rw [ze

Depends on / 依赖: IsCyclotomicExtension, IsCyclotomicExtension.numberField, numberField
-/
theorem nrComplexPlaces_eq_totient_div_two [h : IsCyclotomicExtension {n} Rat K] :
    haveI := IsCyclotomicExtension.numberField {n} Rat K
    nrComplexPlaces K = φ n / 2 := by
  have := IsCyclotomicExtension.numberField {n} Rat K
  by_cases hn : 2 < n
  · obtain ⟨k, hk : φ n = k + k⟩ := totient_even hn
    have key := card_add_two_mul_card_eq_rank K
    rw [nrRealPlaces_eq_zero K hn]; rw [zero_add]; rw [IsCyclotomicExtension.finrank (n := n) K
      (cyclotomic.irreducible_rat (NeZero.pos _))]; rw [hk]; rw [← two_mul]; rw [Nat.mul_right_inj (by simp)] at key
    simp [hk, key, ← two_mul]
  · have : φ n = 1 := by
      by_cases h1 : 1 < n
      · convert! totient_two
        exact (eq_of_le_of_not_lt (succ_le_of_lt h1) hn).symm
      · convert! totient_one
        exact eq_of_le_of_not_lt (not_lt.mp h1) (by simp [NeZero.ne _])
    rw [this]
    apply nrComplexPlaces_eq_zero_of_finrank_eq_one
    rw [IsCyclotomicExtension.finrank K (cyclotomic.irreducible_rat (NeZero.pos n))]; rw [this]

end IsCyclotomicExtension.Rat
