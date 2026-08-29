/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yakov Pechersky
-/
module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Valuation.ValuationRing

/-!
# Integral elements over the ring of integers of a valuation

The ring of integers is integrally closed inside the original ring.
-/

public section


universe u v w

namespace Valuation

namespace Integers

section CommRing

variable {R : Type u} {Γ₀ : Type v} [CommRing R] [LinearOrderedCommGroupWithZero Γ₀]
variable {v : Valuation R Γ₀} {O : Type w} [CommRing O] [Algebra O R] (hv : Integers v O)
include hv

open Polynomial

/--
lemma `isIntegral_iff_v_le_one` / 引理 `isIntegral_iff_v_le_one`

English:
lemma isIntegral_iff_v_le_one
  given: {x : R}
  proof: by
  nontriviality R
  have : Nontrivial O := hv.nontrivial_iff.mpr inferInstance
  constructor
  · rintro ⟨f, hm, hf⟩
    by_cases hn : f.natDegree = 0
    · rw [Polynomial.natDegree_eq_zero] at hn
      obtain ⟨c, rfl⟩ := hn
      simp [map_eq_zero_iff _ hv.hom_inj, hm.ne_zero_of_C] at hf
    simp

中文:
引理 isIntegral_iff_v_le_one
  条件: {x : R}
  证明: by
  nontriviality R
  have : Nontrivial O := hv.nontrivial_iff.mpr inferInstance
  constructor
  · rintro ⟨f, hm, hf⟩
    by_cases hn : f.natDegree = 0
    · rw [Polynomial.natDegree_eq_zero] at hn
      obtain ⟨c, rfl⟩ := hn
      simp [map_eq_zero_iff _ hv.hom_inj, hm.ne_zero_of_C] at hf
    simp

Depends on / 依赖: Finset, Finset.sum_range_succ, Nontrivial, Polynomial, Polynomial.eval, Polynomial.natDegree_eq_zero, add_eq_zero_iff_eq_neg, apply_fun, coeff_natDegree, contrapose, f.natDegree, hm.coeff_natDegree, hm.ne_zero_of_C, hom_inj, hv.hom_inj, hv.nontrivial_iff.mpr, map_eq_zero_iff, map_neg, map_one, map_pow
-/
lemma isIntegral_iff_v_le_one {x : R} :
    IsIntegral O x ↔ v x <= 1 := by
  nontriviality R
  have : Nontrivial O := hv.nontrivial_iff.mpr inferInstance
  constructor
  · rintro ⟨f, hm, hf⟩
    by_cases hn : f.natDegree = 0
    · rw [Polynomial.natDegree_eq_zero] at hn
      obtain ⟨c, rfl⟩ := hn
      simp [map_eq_zero_iff _ hv.hom_inj, hm.ne_zero_of_C] at hf
    simp only [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hm.coeff_natDegree, map_one,
      one_mul, add_eq_zero_iff_eq_neg] at hf
    apply_fun v at hf
    simp only [map_neg, map_pow] at hf
    contrapose! hf
    refine ne_of_lt (v.map_sum_lt ?_ ?_)
    · simp [hn, (hf.trans' (zero_lt_one)).ne']
    · simp only [Finset.mem_range, map_mul, map_pow]
      intro _ hi
exact mul_lt_of_le_one_of_lt (hv.map_le_one _) pow_lt_pow_right₀ hf hi
  · intro h
    obtain ⟨y, rfl⟩ := hv.exists_of_le_one h
    exact ⟨Polynomial.X - .C y, by monicity, by simp⟩

/--
theorem `mem_of_integral` / 定理 `mem_of_integral`

English:
theorem mem_of_integral
  given: {x : R} (hx : IsIntegral O x)
  statement: x in v.integer
  proof: hv.isIntegral_iff_v_le_one.mp hx

中文:
定理 mem_of_integral
  条件: {x : R} (hx : Is整数egral O x)
  结论: x in v.integer
  证明: hv.isIntegral_iff_v_le_one.mp hx

Depends on / 依赖: hv.isIntegral_iff_v_le_one.mp, isIntegral_iff_v_le_one
-/
theorem mem_of_integral {x : R} (hx : IsIntegral O x) : x in v.integer :=
  hv.isIntegral_iff_v_le_one.mp hx

/--
theorem `integralClosure` / 定理 `integralClosure`

English:
theorem integralClosure
  statement: integralClosure O R = ⊥
  proof: bot_unique fun _ hr =>
    let ⟨x, hx⟩ := hv.3 (hv.mem_of_integral hr)
    Algebra.mem_bot.2 ⟨x, hx⟩

中文:
定理 integralClosure
  结论: integralClosure O R = ⊥
  证明: bot_unique fun _ hr =>
    let ⟨x, hx⟩ := hv.3 (hv.mem_of_integral hr)
    Algebra.mem_bot.2 ⟨x, hx⟩
-/
protected theorem integralClosure : integralClosure O R = ⊥ :=
  bot_unique fun _ hr =>
    let ⟨x, hx⟩ := hv.3 (hv.mem_of_integral hr)
    Algebra.mem_bot.2 ⟨x, hx⟩

end CommRing

section FractionField

variable {K : Type u} {Γ₀ : Type v} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
variable {v : Valuation K Γ₀} {O : Type w} [CommRing O]
variable [Algebra O K]
variable (hv : Integers v O)

include hv in
/--
theorem `isIntegrallyClosed` / 定理 `isIntegrallyClosed`

English:
theorem isIntegrallyClosed
  statement: IsIntegrallyClosed O
  proof: by
  have : IsFractionRing O K := hv.isFractionRing
  exact
    (IsIntegrallyClosed.integralClosure_eq_bot_iff K).mp (Valuation.Integers.integralClosure hv)

中文:
定理 isIntegrallyClosed
  结论: Is整数egrallyClosed O
  证明: by
  have : IsFractionRing O K := hv.isFractionRing
  exact
    (IsIntegrallyClosed.integralClosure_eq_bot_iff K).mp (Valuation.Integers.integralClosure hv)

Depends on / 依赖: Integers, IsFractionRing, IsIntegrallyClosed, IsIntegrallyClosed.integralClosure_eq_bot_iff, Valuation, Valuation.Integers.integralClosure, hv.isFractionRing, integralClosure, integralClosure_eq_bot_iff, isFractionRing
-/
theorem isIntegrallyClosed : IsIntegrallyClosed O := by
  have : IsFractionRing O K := hv.isFractionRing
  exact
    (IsIntegrallyClosed.integralClosure_eq_bot_iff K).mp (Valuation.Integers.integralClosure hv)

/--
Instance `isIntegrallyClosed_integers` / 实例 `isIntegrallyClosed_integers`

English:
instance isIntegrallyClosed_integers
  signature: (v : Valuation K Γ₀)
  body: (Valuation.integer.integers v).isIntegrallyClosed

中文:
实例 isIntegrallyClosed_integers
  签名: (v : Valuation K Γ₀)
  定义体: (Valuation.integer.integers v).isIntegrallyClosed

Depends on / 依赖: Valuation, Valuation.integer.integers, integer, integers, isIntegrallyClosed
-/
instance isIntegrallyClosed_integers (v : Valuation K Γ₀) :
    IsIntegrallyClosed v.integer :=
  (Valuation.integer.integers v).isIntegrallyClosed

end FractionField

end Integers

end Valuation
