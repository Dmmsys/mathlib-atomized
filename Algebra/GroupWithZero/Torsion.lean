/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Xavier Roblot
-/
module

public import Mathlib.Algebra.Regular.Basic
public import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors

/-!
# Torsion-free monoids with zero

We prove that if `M` is an `UniqueFactorizationMonoid` that can be equipped with a
`NormalizationMonoid` structure and such that `Mˣ` is torsion-free, then `M` is torsion-free.

Note. You need to import this file to get that the monoid of ideals of a Dedekind domain is
torsion-free.
-/

public section

variable {M : Type*} [CommMonoidWithZero M]

/--
theorem `IsMulTorsionFree.mk'` / 定理 `IsMulTorsionFree.mk'`

English:
theorem IsMulTorsionFree.mk'
  statement: [IsReduced M]
  proof: by
  refine ⟨fun n hn x y hxy => ?_⟩
  by_cases h : x != 0 ∧ y != 0
  · exact ih x h.1 y h.2 n hn hxy
  grind [eq_zero_of_pow_eq_zero, zero_pow]

中文:
定理 是MulTorsionFree.mk'
  结论: [是既约 M]
  证明: by
  refine ⟨fun n hn x y hxy => ?_⟩
  by_cases h : x != 0 ∧ y != 0
  · exact ih x h.1 y h.2 n hn hxy
  grind [eq_zero_of_pow_eq_zero, zero_pow]

Depends on / 依赖: eq_zero_of_pow_eq_zero, imageToKernel, zero_pow
-/
theorem IsMulTorsionFree.mk' [IsReduced M]
    (ih : forall x != 0, forall y != 0, forall n != 0, (x ^ n : M) = y ^ n -> x = y) :
    IsMulTorsionFree M := by
  refine ⟨fun n hn x y hxy => ?_⟩
  by_cases h : x != 0 ∧ y != 0
  · exact ih x h.1 y h.2 n hn hxy
  grind [eq_zero_of_pow_eq_zero, zero_pow]

variable [UniqueFactorizationMonoid M] [NormalizationMonoid M] [IsMulTorsionFree Mˣ]

namespace UniqueFactorizationMonoid

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsMulTorsionFree M
  body: by
  refine .mk' fun x hx y hy n hn hxy => ?_
  obtain ⟨u, hu⟩ : Associated x y := by
    have := (Associated.of_eq hxy).normalizedFactors_eq
    rwa [normalizedFactors_pow, normalizedFactors_pow, nsmul_right_inj hn,
      ← associated_iff_normalizedFactors_eq_normalizedFactors hx hy] at this
  repl

中文:
实例 :
  签名: 是MulTorsionFree M
  定义体: by
  refine .mk' fun x hx y hy n hn hxy => ?_
  obtain ⟨u, hu⟩ : Associated x y := by
    have := (Associated.of_eq hxy).normalizedFactors_eq
    rwa [normalizedFactors_pow, normalizedFactors_pow, nsmul_right_inj hn,
      ← associated_iff_normalizedFactors_eq_normalizedFactors hx hy] at this
  repl

Depends on / 依赖: Associated, Associated.of_eq, IsLeftCancelMulZero, IsLeftCancelMulZero.mul_left_cancel_of_ne_zero, IsLeftRegular, IsLeftRegular.mul_left_eq_self_iff, Units.va, Units.val_pow_eq_pow_val, associated_iff_normalizedFactors_eq_normalizedFactors, eq_comm, mul_left_cancel_of_ne_zero, mul_left_eq_self_iff, mul_pow, normalizedFactors_eq, normalizedFactors_pow, nsmul_right_inj, of_eq, replace, val_pow_eq_pow_val
-/
instance : IsMulTorsionFree M := by
  refine .mk' fun x hx y hy n hn hxy => ?_
  obtain ⟨u, hu⟩ : Associated x y := by
    have := (Associated.of_eq hxy).normalizedFactors_eq
    rwa [normalizedFactors_pow, normalizedFactors_pow, nsmul_right_inj hn,
      ← associated_iff_normalizedFactors_eq_normalizedFactors hx hy] at this
  replace hx : IsLeftRegular (x ^ n) := (IsLeftCancelMulZero.mul_left_cancel_of_ne_zero hx).pow n
  rw [← hu]; rw [mul_pow]; rw [eq_comm]; rw [IsLeftRegular.mul_left_eq_self_iff hx]; rw [← Units.val_pow_eq_pow_val]; rw [Units.val_eq_one]; rw [pow_eq_one_iff_left hn] at hxy
  rwa [hxy, Units.val_one, mul_one] at hu

end UniqueFactorizationMonoid
