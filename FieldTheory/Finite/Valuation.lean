/-
Copyright (c) 2026 María Inés de Frutos-Fernández, Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Xavier Généreux
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.Valuation.Basic

/-!
# Valuations on an algebra over a finite field.
-/

public section

namespace FiniteField

open Valuation

variable {Fq A Γ : Type*} [Field Fq] [Finite Fq] [Ring A] [Algebra Fq A]
  [LinearOrderedCommMonoidWithZero Γ] (v : Valuation A Γ)

@[grind =>]
/--
lemma `valuation_algebraMap_eq_one` / 引理 `valuation_algebraMap_eq_one`

English:
lemma valuation_algebraMap_eq_one
  given: (a : Fq) (ha : a != 0)
  statement: v (algebraMap Fq A a) = 1
  proof: by
  have : Fintype Fq := Fintype.ofFinite Fq
  have hpow : (v (algebraMap Fq A a)) ^ (Fintype.card Fq - 1) = 1 := by
    simp [← map_pow, FiniteField.pow_card_sub_one_eq_one a ha]
  grind [pow_eq_one_iff, -> IsPrimePow.two_le, FiniteField.isPrimePow_card]

中文:
引理 valuation_algebraMap_eq_one
  条件: (a : Fq) (ha : a != 0)
  结论: v (algebraMap Fq A a) = 1
  证明: by
  have : Fintype Fq := Fintype.ofFinite Fq
  have hpow : (v (algebraMap Fq A a)) ^ (Fintype.card Fq - 1) = 1 := by
    simp [← map_pow, FiniteField.pow_card_sub_one_eq_one a ha]
  grind [pow_eq_one_iff, -> IsPrimePow.two_le, FiniteField.isPrimePow_card]

Depends on / 依赖: FiniteField, FiniteField.isPrimePow_card, FiniteField.pow_card_sub_one_eq_one, Fintype, Fintype.card, Fintype.ofFinite, IsPrimePow, IsPrimePow.two_le, algebraMap, isPrimePow_card, map_pow, ofFinite, pow_card_sub_one_eq_one, pow_eq_one_iff, two_le
-/
lemma valuation_algebraMap_eq_one (a : Fq) (ha : a != 0) : v (algebraMap Fq A a) = 1 := by
  have : Fintype Fq := Fintype.ofFinite Fq
  have hpow : (v (algebraMap Fq A a)) ^ (Fintype.card Fq - 1) = 1 := by
    simp [← map_pow, FiniteField.pow_card_sub_one_eq_one a ha]
  grind [pow_eq_one_iff, -> IsPrimePow.two_le, FiniteField.isPrimePow_card]

/--
lemma `valuation_algebraMap_le_one` / 引理 `valuation_algebraMap_le_one`

English:
lemma valuation_algebraMap_le_one
  given: (v : Valuation A Γ) (a : Fq)
  proof: by by_cases a = 0 <;> grind [zero_le]

中文:
引理 valuation_algebraMap_le_one
  条件: (v : 赋值 A Γ) (a : Fq)
  证明: by by_cases a = 0 <;> grind [zero_le]

Depends on / 依赖: zero_le
-/
lemma valuation_algebraMap_le_one (v : Valuation A Γ) (a : Fq) :
    v (algebraMap Fq A a) <= 1 := by by_cases a = 0 <;> grind [zero_le]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsTrivialOn Fq v
  body: FiniteField.valuation_algebraMap_eq_one v a ha

中文:
实例 :
  签名: 是TrivialOn Fq v
  定义体: FiniteField.valuation_algebraMap_eq_one v a ha

Depends on / 依赖: FiniteField, FiniteField.valuation_algebraMap_eq_one, valuation_algebraMap_eq_one
-/
instance : IsTrivialOn Fq v where
  eq_one a ha := FiniteField.valuation_algebraMap_eq_one v a ha

end FiniteField
