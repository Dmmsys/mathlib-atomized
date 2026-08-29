/-
Copyright (c) 2024 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero
-/
module

public import Mathlib.Algebra.Order.Archimedean.Submonoid
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.Valuation.Archimedean
public import Mathlib.RingTheory.Valuation.Discrete.RankOne
public import Mathlib.Topology.Algebra.Valued.NormedValued

import Mathlib.Algebra.FiniteSupport.Basic

/-!
# Finite places of number fields

This file defines finite places of a number field `K` as absolute values coming from an embedding
into a completion of `K` associated to a non-zero prime ideal of `𝓞 K`.

Many of the results in this file are expressed in the generality of: `R` is a Dedekind domain
with field of fractions `K` such that `Module.Finite ℤ R` and `Module.Free ℤ R`. If `K` is
a number field, then this characterises `R` as being isomorphic to `𝓞 K` without explicitly
requiring `𝓞 K`. This is so that `ℤ` and `𝓞 ℚ` can be used interchangeably.

## Main Definitions and Results
* `NumberField.adicAbv`: a `v`-adic absolute value on `K`.
* `NumberField.FinitePlace`: the type of finite places of a number field `K`.
* `NumberField.FinitePlace.embedding`: the canonical embedding of a number field `K` to the
  `v`-adic completion `v.adicCompletion K` of `K`, where `v` is a non-zero prime ideal of `𝓞 K`
* `NumberField.FinitePlace.norm_embedding`: the norm of `embedding v x` is the same as the `v`-adic
  absolute value of `x`. See also `NumberField.FinitePlace.norm_embedding'` and
  `NumberField.FinitePlace.norm_embedding_int` for versions where the `v`-adic absolute value is
  unfolded.
* `NumberField.FinitePlace.hasFiniteMulSupport`: the `v`-adic absolute value of a non-zero element
  of `K` is different from 1 for at most finitely many `v`.
* The valuation subrings of the field at the `v`-valuation and it's adic completion are
   discrete valuation rings.

## Tags
number field, places, finite places
-/

@[expose] public section

open Ideal IsDedekindDomain HeightOneSpectrum WithZeroMulInt WithZero

open scoped WithZero NNReal

section DVR

variable (A : Type*) [CommRing A] [IsDedekindDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (v : HeightOneSpectrum A) (hv : Finite (A ⧸ v.asIdeal))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsPrincipalIdealRing (v.valuation K).integer
  body: by
  rw [(Valuation.integer.integers (v.valuation K)).isPrincipalIdealRing_iff_not_denselyOrdered]; rw [WithZero.denselyOrdered_set_iff_subsingleton]
  simpa using (v.valuation K).toMonoidWithZeroHom.range_nontrivial

中文:
实例 :
  签名: 是主理想环 (v.valuation K).integer
  定义体: by
  rw [(Valuation.integer.integers (v.valuation K)).isPrincipalIdealRing_iff_not_denselyOrdered]; rw [WithZero.denselyOrdered_set_iff_subsingleton]
  simpa using (v.valuation K).toMonoidWithZeroHom.range_nontrivial

Depends on / 依赖: Valuation, Valuation.integer.integers, WithZero, WithZero.denselyOrdered_set_iff_subsingleton, denselyOrdered_set_iff_subsingleton, integer, integers, isPrincipalIdealRing_iff_not_denselyOrdered, range_nontrivial, toMonoidWithZeroHom, toMonoidWithZeroHom.range_nontrivial, v.valuation, valuation
-/
instance : IsPrincipalIdealRing (v.valuation K).integer := by
  rw [(Valuation.integer.integers (v.valuation K)).isPrincipalIdealRing_iff_not_denselyOrdered]; rw [WithZero.denselyOrdered_set_iff_subsingleton]
  simpa using (v.valuation K).toMonoidWithZeroHom.range_nontrivial

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsDiscreteValuationRing (v.valuation K).integer
  body: (v.valuation K).valuationSubring_isDiscreteValuationRing

中文:
实例 :
  签名: 是离散赋值环 (v.valuation K).integer
  定义体: (v.valuation K).valuationSubring_isDiscreteValuationRing

Depends on / 依赖: v.valuation, valuation, valuationSubring_isDiscreteValuationRing
-/
instance : IsDiscreteValuationRing (v.valuation K).integer :=
  (v.valuation K).valuationSubring_isDiscreteValuationRing

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsPrincipalIdealRing (v.adicCompletionIntegers K)
  body: by
  unfold HeightOneSpectrum.adicCompletionIntegers
  rw [(Valuation.valuationSubring.integers (Valued.v)).isPrincipalIdealRing_iff_not_denselyOrdered]; rw [WithZero.denselyOrdered_set_iff_subsingleton]
  simpa using Valued.v.range_nontrivial

中文:
实例 :
  签名: 是主理想环 (v.adicCompletion整数egers K)
  定义体: by
  unfold HeightOneSpectrum.adicCompletionIntegers
  rw [(Valuation.valuationSubring.integers (Valued.v)).isPrincipalIdealRing_iff_not_denselyOrdered]; rw [WithZero.denselyOrdered_set_iff_subsingleton]
  simpa using Valued.v.range_nontrivial

Depends on / 依赖: HeightOneSpectrum, HeightOneSpectrum.adicCompletionIntegers, Valuation, Valuation.valuationSubring.integers, Valued, Valued.v, Valued.v.range_nontrivial, WithZero, WithZero.denselyOrdered_set_iff_subsingleton, adicCompletionIntegers, denselyOrdered_set_iff_subsingleton, integers, isPrincipalIdealRing_iff_not_denselyOrdered, range_nontrivial, valuationSubring
-/
instance : IsPrincipalIdealRing (v.adicCompletionIntegers K) := by
  unfold HeightOneSpectrum.adicCompletionIntegers
  rw [(Valuation.valuationSubring.integers (Valued.v)).isPrincipalIdealRing_iff_not_denselyOrdered]; rw [WithZero.denselyOrdered_set_iff_subsingleton]
  simpa using Valued.v.range_nontrivial

-- TODO: make this inferred from `IsRankOneDiscrete`, or
-- develop the API for a completion of a base `IsDVR` ring
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsDiscreteValuationRing (v.adicCompletionIntegers K)
  body: by
    unfold HeightOneSpectrum.adicCompletionIntegers
    simp only [ne_eq, Ideal.ext_iff, Valuation.mem_maximalIdeal_iff, Ideal.mem_bot, Subtype.ext_iff,
      ZeroMemClass.coe_zero, Subtype.forall, Valuation.mem_valuationSubring_iff, not_forall,
      exists_prop]
    obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
    use (WithVal.equiv (v.valuation K)).symm π
    simp [hπ, ← exp_zero, -exp_neg,
      ← (Valued.v : Valuation (v.adicCompletion K) Intᵐ⁰).map_eq_zero_iff]

中文:
实例 :
  签名: 是离散赋值环 (v.adicCompletion整数egers K)
  定义体: by
    unfold HeightOneSpectrum.adicCompletionIntegers
    simp only [ne_eq, Ideal.ext_iff, Valuation.mem_maximalIdeal_iff, Ideal.mem_bot, Subtype.ext_iff,
      ZeroMemClass.coe_zero, Subtype.forall, Valuation.mem_valuationSubring_iff, not_forall,
      exists_prop]
    obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
    use (WithVal.equiv (v.valuation K)).symm π
    simp [hπ, ← exp_zero, -exp_neg,
      ← (Valued.v : Valuation (v.adicCompletion K) Intᵐ⁰).map_eq_zero_iff]

Depends on / 依赖: HeightOneSpectrum, HeightOneSpectrum.adicCompletionIntegers, Ideal.ext_iff, Ideal.mem_bot, Subtype, Subtype.ext_iff, Subtype.forall, Valuation, Valuation.mem_maximalIdeal_iff, Valuation.mem_valuationSubring_iff, Valued, Valued.v, WithVal, WithVal.equiv, ZeroMemClass, ZeroMemClass.coe_zero, adicCompletion, adicCompletionIntegers, coe_zero, exists_prop
-/
instance : IsDiscreteValuationRing (v.adicCompletionIntegers K) where
  not_a_field' := by
    unfold HeightOneSpectrum.adicCompletionIntegers
    simp only [ne_eq, Ideal.ext_iff, Valuation.mem_maximalIdeal_iff, Ideal.mem_bot, Subtype.ext_iff,
      ZeroMemClass.coe_zero, Subtype.forall, Valuation.mem_valuationSubring_iff, not_forall,
      exists_prop]
    obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
    use (WithVal.equiv (v.valuation K)).symm π
    simp [hπ, ← exp_zero, -exp_neg,
      ← (Valued.v : Valuation (v.adicCompletion K) Intᵐ⁰).map_eq_zero_iff]

end DVR

namespace NumberField

variable {K : Type*} [Field K] {R : Type*} [CommRing R] [Algebra R K] [IsDedekindDomain R]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

/--
Definition of `FinitePlace.embedding` / `FinitePlace.embedding` 的定义

English:
definition FinitePlace.embedding
  signature: : K ->+* adicCompletion K v
  body: (adicCompletion.equiv K v).symm.toRingHom.comp
    (UniformSpace.Completion.coeRingHom.comp (WithVal.equiv (v.valuation K)).symm)

中文:
定义 FinitePlace.embedding
  签名: : K ->+* adicCompletion K v
  定义体: (adicCompletion.equiv K v).symm.toRingHom.comp
    (UniformSpace.Completion.coeRingHom.comp (WithVal.equiv (v.valuation K)).symm)

Depends on / 依赖: Completion, UniformSpace, UniformSpace.Completion.coeRingHom.comp, WithVal, WithVal.equiv, adicCompletion, adicCompletion.equiv, coeRingHom, symm.toRingHom.comp, toRingHom, v.valuation, valuation
-/
noncomputable def FinitePlace.embedding : K ->+* adicCompletion K v :=
  (adicCompletion.equiv K v).symm.toRingHom.comp
    (UniformSpace.Completion.coeRingHom.comp (WithVal.equiv (v.valuation K)).symm)

/--
theorem `FinitePlace.embedding_apply` / 定理 `FinitePlace.embedding_apply`

English:
theorem FinitePlace.embedding_apply
  given: (x : K)
  statement: embedding v x = ↑x
  proof: rfl

中文:
定理 FinitePlace.embedding_apply
  条件: (x : K)
  结论: embedding v x = ↑x
  证明: rfl
-/
theorem FinitePlace.embedding_apply (x : K) : embedding v x = ↑x := rfl

section AbsoluteValue

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ((Valued.v : Valuation (v.adicCompletion K) Intᵐ⁰)).IsRankOneDiscrete
  body: by
    have h : (v.valuation K).IsRankOneDiscrete := Valuation.IsRankOneDiscrete.mk' (valuation K v)
    exact ⟨h.generator, by rw [h.generator_zpowers_eq_valueGroup, adicCompletion_valueGroup_eq],
      h.generator_lt_one⟩

中文:
实例 :
  签名: ((赋值.v : 赋值 (v.adicCompletion K) 整数ᵐ⁰)).是RankOneDiscrete
  定义体: by
    have h : (v.valuation K).IsRankOneDiscrete := Valuation.IsRankOneDiscrete.mk' (valuation K v)
    exact ⟨h.generator, by rw [h.generator_zpowers_eq_valueGroup, adicCompletion_valueGroup_eq],
      h.generator_lt_one⟩

Depends on / 依赖: IsRankOneDiscrete, Valuation, Valuation.IsRankOneDiscrete.mk, adicCompletion_valueGroup_eq, generator, generator_lt_one, generator_zpowers_eq_valueGroup, h.generator, h.generator_lt_one, h.generator_zpowers_eq_valueGroup, v.valuation, valuation
-/
noncomputable instance : ((Valued.v : Valuation (v.adicCompletion K) Intᵐ⁰)).IsRankOneDiscrete where
  exists_generator_lt_one' := by
    have h : (v.valuation K).IsRankOneDiscrete := Valuation.IsRankOneDiscrete.mk' (valuation K v)
    exact ⟨h.generator, by rw [h.generator_zpowers_eq_valueGroup, adicCompletion_valueGroup_eq],
      h.generator_lt_one⟩

section FiniteFree

/-! In this section we assume further that `Module.Finite ℤ R` and `Module.Free ℤ R`.
This characterises `R` as being isomorphic to `𝓞 K` without explicitly requiring that type.
As a result, if `F = ℚ`, then we can use `ℤ` and `𝓞 ℚ` interchangeably. -/

variable [Module.Finite Int R] [Module.Free Int R]

namespace HeightOneSpectrum

/--
lemma `one_lt_absNorm` / 引理 `one_lt_absNorm`

English:
lemma one_lt_absNorm
  statement: 1 < absNorm v.asIdeal
  proof: by
  by_contra! h
  apply IsPrime.ne_top v.isPrime
  rw [← absNorm_eq_one_iff]
  have : 0 < absNorm v.asIdeal := by
    rw [Nat.pos_iff_ne_zero]; rw [absNorm_ne_zero_iff]
    exact v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  lia

中文:
引理 one_lt_absNorm
  结论: 1 < absNorm v.asIdeal
  证明: by
  by_contra! h
  apply IsPrime.ne_top v.isPrime
  rw [← absNorm_eq_one_iff]
  have : 0 < absNorm v.asIdeal := by
    rw [Nat.pos_iff_ne_zero]; rw [absNorm_ne_zero_iff]
    exact v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  lia

Depends on / 依赖: IsPrime, IsPrime.ne_top, Nat.pos_iff_ne_zero, absNorm, absNorm_eq_one_iff, absNorm_ne_zero_iff, asIdeal, finiteQuotientOfFreeOfNeBot, isPrime, ne_bot, ne_top, pos_iff_ne_zero, v.asIdeal, v.asIdeal.finiteQuotientOfFreeOfNeBot, v.isPrime, v.ne_bot
-/
lemma one_lt_absNorm : 1 < absNorm v.asIdeal := by
  by_contra! h
  apply IsPrime.ne_top v.isPrime
  rw [← absNorm_eq_one_iff]
  have : 0 < absNorm v.asIdeal := by
    rw [Nat.pos_iff_ne_zero]; rw [absNorm_ne_zero_iff]
    exact v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  lia

/--
lemma `one_lt_absNorm_nnreal` / 引理 `one_lt_absNorm_nnreal`

English:
lemma one_lt_absNorm_nnreal
  statement: 1 < (absNorm v.asIdeal : Real>=0)
  proof: mod_cast one_lt_absNorm v

中文:
引理 one_lt_absNorm_nnreal
  结论: 1 < (absNorm v.asIdeal : 实数>=0)
  证明: mod_cast one_lt_absNorm v

Depends on / 依赖: mod_cast, one_lt_absNorm
-/
lemma one_lt_absNorm_nnreal : 1 < (absNorm v.asIdeal : Real>=0) := mod_cast one_lt_absNorm v

/--
lemma `absNorm_ne_zero` / 引理 `absNorm_ne_zero`

English:
lemma absNorm_ne_zero
  statement: (absNorm v.asIdeal : Real>=0) != 0
  proof: ne_zero_of_lt (one_lt_absNorm_nnreal v)

中文:
引理 absNorm_ne_zero
  结论: (absNorm v.asIdeal : 实数>=0) != 0
  证明: ne_zero_of_lt (one_lt_absNorm_nnreal v)

Depends on / 依赖: ne_zero_of_lt, one_lt_absNorm_nnreal
-/
lemma absNorm_ne_zero : (absNorm v.asIdeal : Real>=0) != 0 :=
  ne_zero_of_lt (one_lt_absNorm_nnreal v)

variable (K)

/--
Definition of `adicAbv` / `adicAbv` 的定义

English:
definition adicAbv
  signature: : AbsoluteValue K Real
  body: v.adicAbv one_lt_absNorm_nnreal v

中文:
定义 adicAbv
  签名: : 绝对值 K 实数
  定义体: v.adicAbv one_lt_absNorm_nnreal v

Depends on / 依赖: adicAbv, one_lt_absNorm_nnreal, v.adicAbv
-/
noncomputable def adicAbv : AbsoluteValue K Real := v.adicAbv one_lt_absNorm_nnreal v

/--
theorem `adicAbv_def` / 定理 `adicAbv_def`

English:
theorem adicAbv_def
  given: {x : K}
  statement: adicAbv K v x = toNNReal (absNorm_ne_zero v) (v.valuation K x)
  proof: rfl

中文:
定理 adicAbv_def
  条件: {x : K}
  结论: adicAbv K v x = toNN实数 (absNorm_ne_zero v) (v.valuation K x)
  证明: rfl
-/
theorem adicAbv_def {x : K} : adicAbv K v x = toNNReal (absNorm_ne_zero v) (v.valuation K x) := rfl

/--
theorem `isNonarchimedean_adicAbv` / 定理 `isNonarchimedean_adicAbv`

English:
theorem isNonarchimedean_adicAbv
  statement: IsNonarchimedean (adicAbv K v)
  proof: v.isNonarchimedean_adicAbv one_lt_absNorm_nnreal v

中文:
定理 isNonarchimedean_adicAbv
  结论: IsNonarchimedean (adicAbv K v)
  证明: v.isNonarchimedean_adicAbv one_lt_absNorm_nnreal v

Depends on / 依赖: isNonarchimedean_adicAbv, one_lt_absNorm_nnreal, v.isNonarchimedean_adicAbv
-/
theorem isNonarchimedean_adicAbv : IsNonarchimedean (adicAbv K v) :=
v.isNonarchimedean_adicAbv one_lt_absNorm_nnreal v

open Valuation.IsRankOneDiscrete

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (v.valuation K).RankOne
  body: rankOne (v.valuation K) (one_lt_absNorm_nnreal v)

中文:
实例 :
  签名: (v.valuation K).秩一
  定义体: rankOne (v.valuation K) (one_lt_absNorm_nnreal v)

Depends on / 依赖: one_lt_absNorm_nnreal, rankOne, v.valuation, valuation
-/
noncomputable instance : (v.valuation K).RankOne :=
  rankOne (v.valuation K) (one_lt_absNorm_nnreal v)

/--
Instance `instRankOneAdicCompletion` / 实例 `instRankOneAdicCompletion`

English:
instance instRankOneAdicCompletion
  signature: :
  body: rankOne (Valued.v : Valuation (v.adicCompletion K) Intᵐ⁰) (one_lt_absNorm_nnreal v)

中文:
实例 instRankOneAdicCompletion
  签名: :
  定义体: rankOne (Valued.v : Valuation (v.adicCompletion K) Intᵐ⁰) (one_lt_absNorm_nnreal v)

Depends on / 依赖: Valuation, Valued, Valued.v, adicCompletion, one_lt_absNorm_nnreal, rankOne, v.adicCompletion
-/
noncomputable instance instRankOneAdicCompletion :
    (Valued.v : Valuation (v.adicCompletion K) Intᵐ⁰).RankOne :=
  rankOne (Valued.v : Valuation (v.adicCompletion K) Intᵐ⁰) (one_lt_absNorm_nnreal v)

/--
lemma `rankOne_hom'_def` / 引理 `rankOne_hom'_def`

English:
lemma rankOne_hom'_def
  proof: rfl

中文:
引理 rankOne_hom'_def
  证明: rfl
-/
lemma rankOne_hom'_def :
    (instRankOneAdicCompletion K v).hom' = (toNNReal (absNorm_ne_zero v)).comp
      (valueGroup₀_equiv_withZeroMulInt Valued.v).toMonoidWithZeroHom := rfl

/--
Instance `instNormedFieldValuedAdicCompletion` / 实例 `instNormedFieldValuedAdicCompletion`

English:
instance instNormedFieldValuedAdicCompletion
  signature: : NormedField (adicCompletion K v)
  body: Valued.toNormedField (adicCompletion K v) Intᵐ⁰

中文:
实例 instNormedFieldValuedAdicCompletion
  签名: : 赋范域 (adicCompletion K v)
  定义体: Valued.toNormedField (adicCompletion K v) Intᵐ⁰

Depends on / 依赖: Valued, Valued.toNormedField, adicCompletion, toNormedField
-/
noncomputable instance instNormedFieldValuedAdicCompletion : NormedField (adicCompletion K v) :=
  Valued.toNormedField (adicCompletion K v) Intᵐ⁰

/--
lemma `toNNReal_valued_eq_adicAbv` / 引理 `toNNReal_valued_eq_adicAbv`

English:
lemma toNNReal_valued_eq_adicAbv
  given: (x : WithVal (v.valuation K))
  proof: rfl

中文:
引理 toNN实数_valued_eq_adicAbv
  条件: (x : WithVal (v.valuation K))
  证明: rfl
-/
lemma toNNReal_valued_eq_adicAbv (x : WithVal (v.valuation K)) :
    toNNReal (absNorm_ne_zero v) (Valued.v x) = adicAbv K v (WithVal.equiv _ x) := rfl

/--
theorem `adicAbv_add_le_max` / 定理 `adicAbv_add_le_max`

English:
theorem adicAbv_add_le_max
  given: (x y : K)
  proof: isNonarchimedean_adicAbv K v x y

中文:
定理 adicAbv_add_le_max
  条件: (x y : K)
  证明: isNonarchimedean_adicAbv K v x y

Depends on / 依赖: isNonarchimedean_adicAbv
-/
theorem adicAbv_add_le_max (x y : K) :
    adicAbv K v (x + y) <= (adicAbv K v x) ⊔ (adicAbv K v y) := isNonarchimedean_adicAbv K v x y

/--
theorem `adicAbv_natCast_le_one` / 定理 `adicAbv_natCast_le_one`

English:
theorem adicAbv_natCast_le_one
  given: (n : Nat)
  statement: adicAbv K v n <= 1
  proof: (isNonarchimedean_adicAbv K v).apply_natCast_le_one

中文:
定理 adicAbv_natCast_le_one
  条件: (n : 自然数)
  结论: adicAbv K v n <= 1
  证明: (isNonarchimedean_adicAbv K v).apply_natCast_le_one

Depends on / 依赖: apply_natCast_le_one, isNonarchimedean_adicAbv
-/
theorem adicAbv_natCast_le_one (n : Nat) : adicAbv K v n <= 1 :=
  (isNonarchimedean_adicAbv K v).apply_natCast_le_one

/--
theorem `adicAbv_intCast_le_one` / 定理 `adicAbv_intCast_le_one`

English:
theorem adicAbv_intCast_le_one
  given: (n : Int)
  statement: adicAbv K v n <= 1
  proof: (isNonarchimedean_adicAbv K v).apply_intCast_le_one

中文:
定理 adicAbv_intCast_le_one
  条件: (n : 整数)
  结论: adicAbv K v n <= 1
  证明: (isNonarchimedean_adicAbv K v).apply_intCast_le_one

Depends on / 依赖: apply_intCast_le_one, isNonarchimedean_adicAbv
-/
theorem adicAbv_intCast_le_one (n : Int) : adicAbv K v n <= 1 :=
  (isNonarchimedean_adicAbv K v).apply_intCast_le_one

set_option linter.dupNamespace false in
@[deprecated (since := "2026-03-11")]
alias NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm := one_lt_absNorm
@[deprecated (since := "2026-03-11")]
alias _root_.NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm := one_lt_absNorm
set_option linter.dupNamespace false in
@[deprecated (since := "2026-03-11")]
alias NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm_nnreal := one_lt_absNorm_nnreal
@[deprecated (since := "2026-03-11")]
alias _root_.NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm_nnreal :=
  one_lt_absNorm_nnreal
set_option linter.dupNamespace false in
@[deprecated (since := "2026-03-11")]
alias NumberField.RingOfIntegers.HeightOneSpectrum.absNorm_ne_zero := absNorm_ne_zero
@[deprecated (since := "2026-03-11")]
alias _root_.NumberField.RingOfIntegers.HeightOneSpectrum.absNorm_ne_zero := absNorm_ne_zero
set_option linter.dupNamespace false in
@[deprecated (since := "2026-03-11")]
alias NumberField.RingOfIntegers.HeightOneSpectrum.adicAbv := adicAbv
@[deprecated (since := "2026-03-11")]
alias _root_.NumberField.RingOfIntegers.HeightOneSpectrum.adicAbv := adicAbv
set_option linter.dupNamespace false in
@[deprecated (since := "2026-03-11")]
alias NumberField.RingOfIntegers.HeightOneSpectrum.adicAbv_def := adicAbv_def
@[deprecated (since := "2026-03-11")]
alias _root_.NumberField.RingOfIntegers.HeightOneSpectrum.adicAbv_def := adicAbv_def
set_option linter.dupNamespace false in
@[deprecated (since := "2026-03-11")]
alias NumberField.RingOfIntegers.HeightOneSpectrum.isNonarchimedean_adicAbv :=
  isNonarchimedean_adicAbv
@[deprecated (since := "2026-03-11")]
alias _root_.NumberField.RingOfIntegers.HeightOneSpectrum.isNonarchimedean_adicAbv :=
  isNonarchimedean_adicAbv
set_option linter.dupNamespace false in
@[deprecated (since := "2026-03-11")]
alias NumberField.instRankOneAdicCompletion := instRankOneAdicCompletion
@[deprecated (since := "2026-03-11")]
alias _root_.NumberField.instRankOneAdicCompletion := instRankOneAdicCompletion
set_option linter.dupNamespace false in
@[deprecated (since := "2026-03-11")]
alias NumberField.instNormedFieldValuedAdicCompletion := instNormedFieldValuedAdicCompletion
@[deprecated (since := "2026-03-11")]
alias _root_.NumberField.instNormedFieldValuedAdicCompletion := instNormedFieldValuedAdicCompletion
set_option linter.dupNamespace false in
@[deprecated (since := "2026-03-11")]
alias NumberField.rankOne_hom'_def := rankOne_hom'_def
@[deprecated (since := "2026-03-11")]
alias _root_.NumberField.rankOne_hom'_def := rankOne_hom'_def
set_option linter.dupNamespace false in
@[deprecated (since := "2026-03-11")]
alias NumberField.toNNReal_valued_eq_adicAbv := toNNReal_valued_eq_adicAbv
@[deprecated (since := "2026-03-11")]
alias _root_.NumberField.toNNReal_valued_eq_adicAbv := toNNReal_valued_eq_adicAbv
set_option linter.dupNamespace false in
@[deprecated (since := "2026-03-11")]
alias NumberField.RingOfIntegers.HeightOneSpectrum.adicAbv_add_le_max := adicAbv_add_le_max
@[deprecated (since := "2026-03-11")]
alias _root_.NumberField.RingOfIntegers.HeightOneSpectrum.adicAbv_add_le_max := adicAbv_add_le_max
set_option linter.dupNamespace false in
@[deprecated (since := "2026-03-11")]
alias NumberField.RingOfIntegers.HeightOneSpectrum.adicAbv_natCast_le_one := adicAbv_natCast_le_one
@[deprecated (since := "2026-03-11")]
alias _root_.NumberField.RingOfIntegers.HeightOneSpectrum.adicAbv_natCast_le_one :=
  adicAbv_natCast_le_one
set_option linter.dupNamespace false in
@[deprecated (since := "2026-03-11")]
alias NumberField.RingOfIntegers.HeightOneSpectrum.adicAbv_intCast_le_one := adicAbv_intCast_le_one
@[deprecated (since := "2026-03-11")]
alias _root_.NumberField.RingOfIntegers.HeightOneSpectrum.adicAbv_intCast_le_one :=
  adicAbv_intCast_le_one

end HeightOneSpectrum

open HeightOneSpectrum Valuation.IsRankOneDiscrete

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `FinitePlace.norm_def` / 定理 `FinitePlace.norm_def`

English:
theorem FinitePlace.norm_def
  given: (x : v.adicCompletion K)
  proof: by
  simp [Valued.toNormedField.norm_def, Valuation.RankOne.hom, HeightOneSpectrum.rankOne_hom'_def,
    valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective
      (valuedAdicCompletion_surjective K v)]

中文:
定理 FinitePlace.norm_def
  条件: (x : v.adicCompletion K)
  证明: by
  simp [Valued.toNormedField.norm_def, Valuation.RankOne.hom, HeightOneSpectrum.rankOne_hom'_def,
    valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective
      (valuedAdicCompletion_surjective K v)]

Depends on / 依赖: HeightOneSpectrum, HeightOneSpectrum.rankOne_hom, RankOne, Valuation, Valuation.RankOne.hom, Valued, Valued.toNormedField.norm_def, _def, norm_def, rankOne_hom, toNormedField, valuedAdicCompletion_surjective
-/
theorem FinitePlace.norm_def (x : v.adicCompletion K) :
    ‖x‖ = toNNReal (absNorm_ne_zero v) (Valued.v x) := by
  simp [Valued.toNormedField.norm_def, Valuation.RankOne.hom, HeightOneSpectrum.rankOne_hom'_def,
    valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective
      (valuedAdicCompletion_surjective K v)]

/--
theorem `FinitePlace.norm_embedding` / 定理 `FinitePlace.norm_embedding`

English:
theorem FinitePlace.norm_embedding
  given: (x : K)
  statement: ‖embedding v x‖ = adicAbv K v x
  proof: by
  simp [norm_def, embedding_apply, adicAbv_def]

中文:
定理 FinitePlace.norm_embedding
  条件: (x : K)
  结论: ‖embedding v x‖ = adicAbv K v x
  证明: by
  simp [norm_def, embedding_apply, adicAbv_def]

Depends on / 依赖: adicAbv_def, embedding_apply, norm_def
-/
theorem FinitePlace.norm_embedding (x : K) : ‖embedding v x‖ = adicAbv K v x := by
  simp [norm_def, embedding_apply, adicAbv_def]

/--
theorem `FinitePlace.norm_embedding'` / 定理 `FinitePlace.norm_embedding'`

English:
theorem FinitePlace.norm_embedding'
  given: (x : K)
  proof: by
  rw [norm_embedding]; rw [adicAbv_def]

中文:
定理 FinitePlace.norm_embedding'
  条件: (x : K)
  证明: by
  rw [norm_embedding]; rw [adicAbv_def]

Depends on / 依赖: adicAbv_def, norm_embedding
-/
theorem FinitePlace.norm_embedding' (x : K) :
    ‖embedding v x‖ = toNNReal (absNorm_ne_zero v) (v.valuation K x) := by
  rw [norm_embedding]; rw [adicAbv_def]

variable (K)

/--
theorem `FinitePlace.norm_embedding_int` / 定理 `FinitePlace.norm_embedding_int`

English:
theorem FinitePlace.norm_embedding_int
  given: (x : R)
  proof: by
  simp [norm_embedding, adicAbv_def, valuation_of_algebraMap]

@[deprecated (since := "2026-03-05")] alias FinitePlace.norm_def' := FinitePlace.norm_embedding'
@[deprecated (since := "2026-03-05")] alias FinitePlace.norm_def_int :=
  FinitePlace.norm_embedding_int

中文:
定理 FinitePlace.norm_embedding_int
  条件: (x : R)
  证明: by
  simp [norm_embedding, adicAbv_def, valuation_of_algebraMap]

@[deprecated (since := "2026-03-05")] alias FinitePlace.norm_def' := FinitePlace.norm_embedding'
@[deprecated (since := "2026-03-05")] alias FinitePlace.norm_def_int :=
  FinitePlace.norm_embedding_int

Depends on / 依赖: adicAbv_def, norm_embedding, valuation_of_algebraMap
-/
theorem FinitePlace.norm_embedding_int (x : R) :
    ‖embedding v (algebraMap _ K x)‖ = toNNReal (absNorm_ne_zero v) (v.intValuation x) := by
  simp [norm_embedding, adicAbv_def, valuation_of_algebraMap]

@[deprecated (since := "2026-03-05")] alias FinitePlace.norm_def' := FinitePlace.norm_embedding'
@[deprecated (since := "2026-03-05")] alias FinitePlace.norm_def_int :=
  FinitePlace.norm_embedding_int

open FinitePlace

/--
theorem `FinitePlace.norm_le_one` / 定理 `FinitePlace.norm_le_one`

English:
theorem FinitePlace.norm_le_one
  given: (x : R)
  statement: ‖embedding v (algebraMap _ K x)‖ <= 1
  proof: by
  rw [norm_embedding]
  exact v.adicAbv_coe_le_one (one_lt_absNorm_nnreal v) x

中文:
定理 FinitePlace.norm_le_one
  条件: (x : R)
  结论: ‖embedding v (algebraMap _ K x)‖ <= 1
  证明: by
  rw [norm_embedding]
  exact v.adicAbv_coe_le_one (one_lt_absNorm_nnreal v) x

Depends on / 依赖: adicAbv_coe_le_one, norm_embedding, one_lt_absNorm_nnreal, v.adicAbv_coe_le_one
-/
theorem FinitePlace.norm_le_one (x : R) : ‖embedding v (algebraMap _ K x)‖ <= 1 := by
  rw [norm_embedding]
  exact v.adicAbv_coe_le_one (one_lt_absNorm_nnreal v) x

/--
theorem `FinitePlace.norm_eq_one_iff_notMem` / 定理 `FinitePlace.norm_eq_one_iff_notMem`

English:
theorem FinitePlace.norm_eq_one_iff_notMem
  given: (x : R)
  proof: by
  rw [norm_embedding]
  exact v.adicAbv_coe_eq_one_iff (one_lt_absNorm_nnreal v) x

中文:
定理 FinitePlace.norm_eq_one_iff_notMem
  条件: (x : R)
  证明: by
  rw [norm_embedding]
  exact v.adicAbv_coe_eq_one_iff (one_lt_absNorm_nnreal v) x

Depends on / 依赖: adicAbv_coe_eq_one_iff, norm_embedding, one_lt_absNorm_nnreal, v.adicAbv_coe_eq_one_iff
-/
theorem FinitePlace.norm_eq_one_iff_notMem (x : R) :
    ‖embedding v (algebraMap _ K x)‖ = 1 ↔ x ∉ v.asIdeal := by
  rw [norm_embedding]
  exact v.adicAbv_coe_eq_one_iff (one_lt_absNorm_nnreal v) x

/--
theorem `FinitePlace.norm_lt_one_iff_mem` / 定理 `FinitePlace.norm_lt_one_iff_mem`

English:
theorem FinitePlace.norm_lt_one_iff_mem
  given: (x : R)
  proof: by
  rw [norm_embedding]
  exact v.adicAbv_coe_lt_one_iff (one_lt_absNorm_nnreal v) x

中文:
定理 FinitePlace.norm_lt_one_iff_mem
  条件: (x : R)
  证明: by
  rw [norm_embedding]
  exact v.adicAbv_coe_lt_one_iff (one_lt_absNorm_nnreal v) x

Depends on / 依赖: adicAbv_coe_lt_one_iff, norm_embedding, one_lt_absNorm_nnreal, v.adicAbv_coe_lt_one_iff
-/
theorem FinitePlace.norm_lt_one_iff_mem (x : R) :
    ‖embedding v (algebraMap _ K x)‖ < 1 ↔ x in v.asIdeal := by
  rw [norm_embedding]
  exact v.adicAbv_coe_lt_one_iff (one_lt_absNorm_nnreal v) x

set_option backward.isDefEq.respectTransparency false in
/--
lemma `HeightOneSpectrum.embedding_mul_absNorm` / 引理 `HeightOneSpectrum.embedding_mul_absNorm`

English:
lemma HeightOneSpectrum.embedding_mul_absNorm
  given: {x : R} (h_x_nezero : x != 0)
  proof: by
  rw [maxPowDividing]; rw [map_pow]; rw [Nat.cast_pow]; rw [norm_embedding]; rw [adicAbv_def]; rw [WithZeroMulInt.toNNReal_neg_apply _ ((v.valuation K).ne_zero_iff.mpr
      ((FaithfulSMul.algebraMap_eq_zero_iff R K).not.2 h_x_nezero))]
  push_cast
  rw [← zpow_natCast]; rw [← zpow_add₀ <| mod_cast (zero_lt_one.trans (one_lt_absNorm_nnreal v)).ne']
  norm_cast
  rw [zpow_eq_one_iff_right₀ (Nat.cast_nonneg' _) (mod_cast (one_lt_absNorm_nnreal v).ne')]
  simp [valuation_of_algebraMap, intValuation_if_neg, h_x_nezero]

中文:
引理 高一谱.embedding_mul_absNorm
  条件: {x : R} (h_x_nezero : x != 0)
  证明: by
  rw [maxPowDividing]; rw [map_pow]; rw [Nat.cast_pow]; rw [norm_embedding]; rw [adicAbv_def]; rw [WithZeroMulInt.toNNReal_neg_apply _ ((v.valuation K).ne_zero_iff.mpr
      ((FaithfulSMul.algebraMap_eq_zero_iff R K).not.2 h_x_nezero))]
  push_cast
  rw [← zpow_natCast]; rw [← zpow_add₀ <| mod_cast (zero_lt_one.trans (one_lt_absNorm_nnreal v)).ne']
  norm_cast
  rw [zpow_eq_one_iff_right₀ (Nat.cast_nonneg' _) (mod_cast (one_lt_absNorm_nnreal v).ne')]
  simp [valuation_of_algebraMap, intValuation_if_neg, h_x_nezero]

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_eq_zero_iff, Nat.cast_nonneg, Nat.cast_pow, WithZeroMulInt, WithZeroMulInt.toNNReal_neg_apply, adicAbv_def, algebraMap_eq_zero_iff, cast_nonneg, cast_pow, h_x_ne, h_x_nezero, intValuation_if_neg, map_pow, maxPowDividing, mod_cast, ne_zero_iff, ne_zero_iff.mpr, norm_embedding, one_lt_absNorm_nnreal
-/
lemma HeightOneSpectrum.embedding_mul_absNorm {x : R} (h_x_nezero : x != 0) :
    ‖embedding v (algebraMap _ K x)‖ * absNorm (v.maxPowDividing (span {x})) = 1 := by
  rw [maxPowDividing]; rw [map_pow]; rw [Nat.cast_pow]; rw [norm_embedding]; rw [adicAbv_def]; rw [WithZeroMulInt.toNNReal_neg_apply _ ((v.valuation K).ne_zero_iff.mpr
      ((FaithfulSMul.algebraMap_eq_zero_iff R K).not.2 h_x_nezero))]
  push_cast
  rw [← zpow_natCast]; rw [← zpow_add₀ <| mod_cast (zero_lt_one.trans (one_lt_absNorm_nnreal v)).ne']
  norm_cast
  rw [zpow_eq_one_iff_right₀ (Nat.cast_nonneg' _) (mod_cast (one_lt_absNorm_nnreal v).ne')]
  simp [valuation_of_algebraMap, intValuation_if_neg, h_x_nezero]

end FiniteFree

end AbsoluteValue

open HeightOneSpectrum

/--
Definition of `FinitePlace` / `FinitePlace` 的定义

English:
definition FinitePlace
  signature: (K : Type*) [Field K] [NumberField K]
  body: {w : AbsoluteValue K Real // exists v : HeightOneSpectrum (𝓞 K), place (FinitePlace.embedding v) = w}

中文:
定义 FinitePlace
  签名: (K : 类型) [域 K] [数域 K]
  定义体: {w : AbsoluteValue K Real // exists v : HeightOneSpectrum (𝓞 K), place (FinitePlace.embedding v) = w}

Depends on / 依赖: AbsoluteValue, FinitePlace, FinitePlace.embedding, HeightOneSpectrum, embedding
-/
def FinitePlace (K : Type*) [Field K] [NumberField K] :=
  {w : AbsoluteValue K Real // exists v : HeightOneSpectrum (𝓞 K), place (FinitePlace.embedding v) = w}

/--
Definition of `FinitePlace.mk` / `FinitePlace.mk` 的定义

English:
definition FinitePlace.mk
  signature: [NumberField K] (v : HeightOneSpectrum (𝓞 K))
  body: ⟨place (embedding v), ⟨v, rfl⟩⟩

中文:
定义 FinitePlace.mk
  签名: [数域 K] (v : 高一谱 (𝓞 K))
  定义体: ⟨place (embedding v), ⟨v, rfl⟩⟩

Depends on / 依赖: IsSuccArchimedean, embedding, isPredArchimedean_of_isSuccArchimedean
-/
noncomputable def FinitePlace.mk [NumberField K] (v : HeightOneSpectrum (𝓞 K)) : FinitePlace K :=
  ⟨place (embedding v), ⟨v, rfl⟩⟩

/--
Definition of `IsFinitePlace` / `IsFinitePlace` 的定义

English:
definition IsFinitePlace
  signature: [NumberField K] (w : AbsoluteValue K Real)
  body: exists v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), place (FinitePlace.embedding v) = w

中文:
定义 IsFinitePlace
  签名: [数域 K] (w : 绝对值 K 实数)
  定义体: exists v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), place (FinitePlace.embedding v) = w

Depends on / 依赖: FinitePlace, FinitePlace.embedding, HeightOneSpectrum, IsDedekindDomain, IsDedekindDomain.HeightOneSpectrum, embedding
-/
def IsFinitePlace [NumberField K] (w : AbsoluteValue K Real) : Prop :=
  exists v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), place (FinitePlace.embedding v) = w

/--
lemma `FinitePlace.isFinitePlace` / 引理 `FinitePlace.isFinitePlace`

English:
lemma FinitePlace.isFinitePlace
  given: [NumberField K] (v : FinitePlace K)
  statement: IsFinitePlace v.val
  proof: by
  simp [IsFinitePlace, v.prop]

中文:
引理 FinitePlace.isFinitePlace
  条件: [数域 K] (v : FinitePlace K)
  结论: IsFinitePlace v.val
  证明: by
  simp [IsFinitePlace, v.prop]

Depends on / 依赖: IsFinitePlace, v.prop
-/
lemma FinitePlace.isFinitePlace [NumberField K] (v : FinitePlace K) : IsFinitePlace v.val := by
  simp [IsFinitePlace, v.prop]

/--
lemma `isFinitePlace_iff` / 引理 `isFinitePlace_iff`

English:
lemma isFinitePlace_iff
  given: [NumberField K] (v : AbsoluteValue K Real)
  proof: ⟨fun H => ⟨⟨v, H⟩, rfl⟩, fun ⟨w, hw⟩ => hw ▸ w.isFinitePlace⟩

中文:
引理 isFinitePlace_iff
  条件: [数域 K] (v : 绝对值 K 实数)
  证明: ⟨fun H => ⟨⟨v, H⟩, rfl⟩, fun ⟨w, hw⟩ => hw ▸ w.isFinitePlace⟩

Depends on / 依赖: isFinitePlace, w.isFinitePlace
-/
lemma isFinitePlace_iff [NumberField K] (v : AbsoluteValue K Real) :
    IsFinitePlace v ↔ exists w : FinitePlace K, w.val = v :=
  ⟨fun H => ⟨⟨v, H⟩, rfl⟩, fun ⟨w, hw⟩ => hw ▸ w.isFinitePlace⟩

namespace FinitePlace

variable [NumberField K]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (FinitePlace K) K Real
  body: w.1 x
  coe_injective _ _ h := Subtype.ext (AbsoluteValue.ext <| congr_fun h)

中文:
实例 :
  签名: 函数状 (FinitePlace K) K 实数
  定义体: w.1 x
  coe_injective _ _ h := Subtype.ext (AbsoluteValue.ext <| congr_fun h)
-/
instance : FunLike (FinitePlace K) K Real where
  coe w x := w.1 x
  coe_injective _ _ h := Subtype.ext (AbsoluteValue.ext <| congr_fun h)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MonoidWithZeroHomClass (FinitePlace K) K Real
  body: w.1.map_mul
  map_one w := w.1.map_one
  map_zero w := w.1.map_zero

中文:
实例 :
  签名: 带零幺半群态射类 (FinitePlace K) K 实数
  定义体: w.1.map_mul
  map_one w := w.1.map_one
  map_zero w := w.1.map_zero

Depends on / 依赖: map_mul
-/
instance : MonoidWithZeroHomClass (FinitePlace K) K Real where
  map_mul w := w.1.map_mul
  map_one w := w.1.map_one
  map_zero w := w.1.map_zero

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NonnegHomClass (FinitePlace K) K Real
  body: w.1.nonneg

@[simp]

中文:
实例 :
  签名: Nonneg态射类 (FinitePlace K) K 实数
  定义体: w.1.nonneg

@[simp]

Depends on / 依赖: nonneg
-/
instance : NonnegHomClass (FinitePlace K) K Real where
  apply_nonneg w := w.1.nonneg

@[simp]
/--
theorem `mk_apply` / 定理 `mk_apply`

English:
theorem mk_apply
  given: (v : HeightOneSpectrum (𝓞 K)) (x : K)
  statement: mk v x = ‖embedding v x‖
  proof: rfl

中文:
定理 mk_apply
  条件: (v : 高一谱 (𝓞 K)) (x : K)
  结论: mk v x = ‖embedding v x‖
  证明: rfl
-/
theorem mk_apply (v : HeightOneSpectrum (𝓞 K)) (x : K) : mk v x = ‖embedding v x‖ := rfl

/--
lemma `coe_apply` / 引理 `coe_apply`

English:
lemma coe_apply
  given: (v : FinitePlace K) (x : K)
  statement: v x = v.val x
  proof: rfl

中文:
引理 coe_apply
  条件: (v : FinitePlace K) (x : K)
  结论: v x = v.val x
  证明: rfl
-/
lemma coe_apply (v : FinitePlace K) (x : K) : v x = v.val x := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulRingNormClass (FinitePlace K) K Real
  body: by simpa [coe_apply] using IsAbsoluteValue.abv_add' x y
  map_neg_eq_map v x := by simp [coe_apply]
  eq_zero_of_map_eq_zero v := by simp

中文:
实例 :
  签名: 乘法环范数类 (FinitePlace K) K 实数
  定义体: by simpa [coe_apply] using IsAbsoluteValue.abv_add' x y
  map_neg_eq_map v x := by simp [coe_apply]
  eq_zero_of_map_eq_zero v := by simp

Depends on / 依赖: IsAbsoluteValue, IsAbsoluteValue.abv_add, abv_add, coe_apply, eq_zero_of_map_eq_zero, map_neg_eq_map
-/
instance : MulRingNormClass (FinitePlace K) K Real where
  map_add_le_add v x y := by simpa [coe_apply] using IsAbsoluteValue.abv_add' x y
  map_neg_eq_map v x := by simp [coe_apply]
  eq_zero_of_map_eq_zero v := by simp

/--
Definition of `maximalIdeal` / `maximalIdeal` 的定义

English:
definition maximalIdeal
  signature: (w : FinitePlace K)
  body: w.2.choose

@[simp]

中文:
定义 maximalIdeal
  签名: (w : FinitePlace K)
  定义体: w.2.choose

@[simp]
-/
noncomputable def maximalIdeal (w : FinitePlace K) : HeightOneSpectrum (𝓞 K) := w.2.choose

@[simp]
/--
theorem `mk_maximalIdeal` / 定理 `mk_maximalIdeal`

English:
theorem mk_maximalIdeal
  given: (w : FinitePlace K)
  statement: mk (maximalIdeal w) = w
  proof: Subtype.ext w.2.choose_spec

@[simp]

中文:
定理 mk_maximalIdeal
  条件: (w : FinitePlace K)
  结论: mk (maximalIdeal w) = w
  证明: Subtype.ext w.2.choose_spec

@[simp]

Depends on / 依赖: Subtype, Subtype.ext, choose_spec
-/
theorem mk_maximalIdeal (w : FinitePlace K) : mk (maximalIdeal w) = w := Subtype.ext w.2.choose_spec

@[simp]
/--
theorem `norm_embedding_eq` / 定理 `norm_embedding_eq`

English:
theorem norm_embedding_eq
  given: (w : FinitePlace K) (x : K)
  proof: by
  conv_rhs => rw [← mk_maximalIdeal w, mk_apply]

中文:
定理 norm_embedding_eq
  条件: (w : FinitePlace K) (x : K)
  证明: by
  conv_rhs => rw [← mk_maximalIdeal w, mk_apply]

Depends on / 依赖: IsSuccArchimedean, LocallyFiniteOrder, SuccOrder, conv_rhs, mk_apply, mk_maximalIdeal
-/
theorem norm_embedding_eq (w : FinitePlace K) (x : K) :
    ‖embedding (maximalIdeal w) x‖ = w x := by
  conv_rhs => rw [← mk_maximalIdeal w, mk_apply]

/--
theorem `pos_iff` / 定理 `pos_iff`

English:
theorem pos_iff
  given: {w : FinitePlace K} {x : K}
  statement: 0 < w x ↔ x != 0
  proof: w.1.pos_iff

@[simp]

中文:
定理 pos_iff
  条件: {w : FinitePlace K} {x : K}
  结论: 0 < w x ↔ x != 0
  证明: w.1.pos_iff

@[simp]

Depends on / 依赖: IsPredArchimedean, LocallyFiniteOrder, PredOrder, pos_iff
-/
theorem pos_iff {w : FinitePlace K} {x : K} : 0 < w x ↔ x != 0 := w.1.pos_iff

@[simp]
/--
theorem `mk_eq_iff` / 定理 `mk_eq_iff`

English:
theorem mk_eq_iff
  given: {v₁ v₂ : HeightOneSpectrum (𝓞 K)}
  statement: mk v₁ = mk v₂ ↔ v₁ = v₂
  proof: by
  refine ⟨?_, fun a => by rw [a]⟩
  contrapose!
  intro h
  rw [DFunLike.ne_iff]
  have ⟨x, hx1, hx2⟩ : exists x : 𝓞 K, x in v₁.asIdeal ∧ x ∉ v₂.asIdeal := by
    by_contra! H
exact h HeightOneSpectrum.ext_iff.mpr IsMaximal.eq_of_le (isMaximal v₁) IsPrime.ne_top' H
  use x
  simp only [mk_apply]
  rw [← norm_lt_one_iff_mem K] at hx1
  rw [← norm_eq_one_iff_notMem K] at hx2
  linarith

中文:
定理 mk_eq_iff
  条件: {v₁ v₂ : 高一谱 (𝓞 K)}
  结论: mk v₁ = mk v₂ ↔ v₁ = v₂
  证明: by
  refine ⟨?_, fun a => by rw [a]⟩
  contrapose!
  intro h
  rw [DFunLike.ne_iff]
  have ⟨x, hx1, hx2⟩ : exists x : 𝓞 K, x in v₁.asIdeal ∧ x ∉ v₂.asIdeal := by
    by_contra! H
exact h HeightOneSpectrum.ext_iff.mpr IsMaximal.eq_of_le (isMaximal v₁) IsPrime.ne_top' H
  use x
  simp only [mk_apply]
  rw [← norm_lt_one_iff_mem K] at hx1
  rw [← norm_eq_one_iff_notMem K] at hx2
  linarith

Depends on / 依赖: DFunLike, DFunLike.ne_iff, HeightOneSpectrum, HeightOneSpectrum.ext_iff.mpr, IsMaximal, IsMaximal.eq_of_le, IsPrime, IsPrime.ne_top, asIdeal, contrapose, eq_of_le, ext_iff, isMaximal, mk_apply, ne_iff, ne_top, norm_eq_one_iff_notMem, norm_lt_one_iff_mem
-/
theorem mk_eq_iff {v₁ v₂ : HeightOneSpectrum (𝓞 K)} : mk v₁ = mk v₂ ↔ v₁ = v₂ := by
  refine ⟨?_, fun a => by rw [a]⟩
  contrapose!
  intro h
  rw [DFunLike.ne_iff]
  have ⟨x, hx1, hx2⟩ : exists x : 𝓞 K, x in v₁.asIdeal ∧ x ∉ v₂.asIdeal := by
    by_contra! H
exact h HeightOneSpectrum.ext_iff.mpr IsMaximal.eq_of_le (isMaximal v₁) IsPrime.ne_top' H
  use x
  simp only [mk_apply]
  rw [← norm_lt_one_iff_mem K] at hx1
  rw [← norm_eq_one_iff_notMem K] at hx2
  linarith

/--
theorem `maximalIdeal_mk` / 定理 `maximalIdeal_mk`

English:
theorem maximalIdeal_mk
  given: (v : HeightOneSpectrum (𝓞 K))
  statement: maximalIdeal (mk v) = v
  proof: by
  rw [← mk_eq_iff]; rw [mk_maximalIdeal]

中文:
定理 maximalIdeal_mk
  条件: (v : 高一谱 (𝓞 K))
  结论: maximalIdeal (mk v) = v
  证明: by
  rw [← mk_eq_iff]; rw [mk_maximalIdeal]

Depends on / 依赖: mk_eq_iff, mk_maximalIdeal
-/
theorem maximalIdeal_mk (v : HeightOneSpectrum (𝓞 K)) : maximalIdeal (mk v) = v := by
  rw [← mk_eq_iff]; rw [mk_maximalIdeal]

/-- The equivalence between finite places and maximal ideals. -/
@[simps apply]
/--
Definition of `equivHeightOneSpectrum` / `equivHeightOneSpectrum` 的定义

English:
definition equivHeightOneSpectrum
  signature: :
  body: maximalIdeal
  invFun := mk
  left_inv := mk_maximalIdeal
  right_inv := maximalIdeal_mk

中文:
定义 equivHeightOneSpectrum
  签名: :
  定义体: maximalIdeal
  invFun := mk
  left_inv := mk_maximalIdeal
  right_inv := maximalIdeal_mk

Depends on / 依赖: maximalIdeal
-/
noncomputable def equivHeightOneSpectrum :
    FinitePlace K ≃ HeightOneSpectrum (𝓞 K) where
  toFun := maximalIdeal
  invFun := mk
  left_inv := mk_maximalIdeal
  right_inv := maximalIdeal_mk

/--
lemma `maximalIdeal_injective` / 引理 `maximalIdeal_injective`

English:
lemma maximalIdeal_injective
  statement: (fun w : FinitePlace K => maximalIdeal w).Injective
  proof: equivHeightOneSpectrum.injective

中文:
引理 maximalIdeal_injective
  结论: (fun w : FinitePlace K => maximalIdeal w).单射
  证明: equivHeightOneSpectrum.injective

Depends on / 依赖: equivHeightOneSpectrum, equivHeightOneSpectrum.injective, injective
-/
lemma maximalIdeal_injective : (fun w : FinitePlace K => maximalIdeal w).Injective :=
  equivHeightOneSpectrum.injective

/--
lemma `maximalIdeal_inj` / 引理 `maximalIdeal_inj`

English:
lemma maximalIdeal_inj
  given: (w₁ w₂ : FinitePlace K)
  statement: maximalIdeal w₁ = maximalIdeal w₂ ↔ w₁ = w₂
  proof: equivHeightOneSpectrum.injective.eq_iff

@[fun_prop]

中文:
引理 maximalIdeal_inj
  条件: (w₁ w₂ : FinitePlace K)
  结论: maximalIdeal w₁ = maximalIdeal w₂ ↔ w₁ = w₂
  证明: equivHeightOneSpectrum.injective.eq_iff

@[fun_prop]

Depends on / 依赖: eq_iff, equivHeightOneSpectrum, equivHeightOneSpectrum.injective.eq_iff, injective
-/
lemma maximalIdeal_inj (w₁ w₂ : FinitePlace K) : maximalIdeal w₁ = maximalIdeal w₂ ↔ w₁ = w₂ :=
  equivHeightOneSpectrum.injective.eq_iff

@[fun_prop]
/--
theorem `hasFiniteMulSupport_int` / 定理 `hasFiniteMulSupport_int`

English:
theorem hasFiniteMulSupport_int
  given: {x : 𝓞 K} (h_x_nezero : x != 0)
  proof: by
  have (w : FinitePlace K) : w x != 1 ↔ w x < 1 :=
ne_iff_lt_iff_le.mpr norm_embedding_eq w x ▸ norm_le_one K w.maximalIdeal x
  simp_rw [Function.HasFiniteMulSupport, Function.mulSupport, this, ← norm_embedding_eq,
    norm_lt_one_iff_mem, ← Ideal.dvd_span_singleton]
  have h : {v : HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ span {x}}.Finite := by
    apply Ideal.finite_factors
    simp only [Submodule.zero_eq_bot, ne_eq, span_singleton_eq_bot, h_x_nezero, not_false_eq_true]
  have h_inj : Set.InjOn FinitePlace.maximalIdeal {w | w.maximalIdeal.asIdeal ∣ span {x}} :=
    Function.Injective.injOn maximalIdeal_injective
  refine (h.subset ?_).of_finite_image h_inj
  simp only [dvd_span_singleton, Set.image_subset_iff, Set.preimage_ofPred_eq, subset_refl]

@[deprecated (since := "2026-03-03")] alias mulSupport_finite_int := hasFiniteMulSupport_int

@[fun_prop]

中文:
定理 hasFiniteMulSupport_int
  条件: {x : 𝓞 K} (h_x_nezero : x != 0)
  证明: by
  have (w : FinitePlace K) : w x != 1 ↔ w x < 1 :=
ne_iff_lt_iff_le.mpr norm_embedding_eq w x ▸ norm_le_one K w.maximalIdeal x
  simp_rw [Function.HasFiniteMulSupport, Function.mulSupport, this, ← norm_embedding_eq,
    norm_lt_one_iff_mem, ← Ideal.dvd_span_singleton]
  have h : {v : HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ span {x}}.Finite := by
    apply Ideal.finite_factors
    simp only [Submodule.zero_eq_bot, ne_eq, span_singleton_eq_bot, h_x_nezero, not_false_eq_true]
  have h_inj : Set.InjOn FinitePlace.maximalIdeal {w | w.maximalIdeal.asIdeal ∣ span {x}} :=
    Function.Injective.injOn maximalIdeal_injective
  refine (h.subset ?_).of_finite_image h_inj
  simp only [dvd_span_singleton, Set.image_subset_iff, Set.preimage_ofPred_eq, subset_refl]

@[deprecated (since := "2026-03-03")] alias mulSupport_finite_int := hasFiniteMulSupport_int

@[fun_prop]

Depends on / 依赖: Finite, FinitePlace, FinitePlace.maxi, Function, Function.HasFiniteMulSupport, Function.mulSupport, HasFiniteMulSupport, HeightOneSpectrum, Ideal.dvd_span_singleton, Ideal.finite_factors, Set.InjOn, Submodule, Submodule.zero_eq_bot, asIdeal, dvd_span_singleton, finite_factors, h_inj, h_x_nezero, maximalIdeal, mulSupport
-/
theorem hasFiniteMulSupport_int {x : 𝓞 K} (h_x_nezero : x != 0) :
    (fun w : FinitePlace K => w x).HasFiniteMulSupport := by
  have (w : FinitePlace K) : w x != 1 ↔ w x < 1 :=
ne_iff_lt_iff_le.mpr norm_embedding_eq w x ▸ norm_le_one K w.maximalIdeal x
  simp_rw [Function.HasFiniteMulSupport, Function.mulSupport, this, ← norm_embedding_eq,
    norm_lt_one_iff_mem, ← Ideal.dvd_span_singleton]
  have h : {v : HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ span {x}}.Finite := by
    apply Ideal.finite_factors
    simp only [Submodule.zero_eq_bot, ne_eq, span_singleton_eq_bot, h_x_nezero, not_false_eq_true]
  have h_inj : Set.InjOn FinitePlace.maximalIdeal {w | w.maximalIdeal.asIdeal ∣ span {x}} :=
    Function.Injective.injOn maximalIdeal_injective
  refine (h.subset ?_).of_finite_image h_inj
  simp only [dvd_span_singleton, Set.image_subset_iff, Set.preimage_ofPred_eq, subset_refl]

@[deprecated (since := "2026-03-03")] alias mulSupport_finite_int := hasFiniteMulSupport_int

@[fun_prop]
/--
theorem `hasFiniteMulSupport` / 定理 `hasFiniteMulSupport`

English:
theorem hasFiniteMulSupport
  given: {x : K} (h_x_nezero : x != 0)
  proof: by
  rcases IsFractionRing.div_surjective (𝓞 K) x with ⟨a, b, hb, rfl⟩
  simp_all only [ne_eq, div_eq_zero_iff, FaithfulSMul.algebraMap_eq_zero_iff, not_or, map_div₀]
  obtain ⟨ha, hb⟩ := h_x_nezero
  simp_rw [← RingOfIntegers.coe_eq_algebraMap]
  fun_prop

@[deprecated (since := "2026-03-03")] alias mulSupport_finite := hasFiniteMulSupport

中文:
定理 hasFiniteMulSupport
  条件: {x : K} (h_x_nezero : x != 0)
  证明: by
  rcases IsFractionRing.div_surjective (𝓞 K) x with ⟨a, b, hb, rfl⟩
  simp_all only [ne_eq, div_eq_zero_iff, FaithfulSMul.algebraMap_eq_zero_iff, not_or, map_div₀]
  obtain ⟨ha, hb⟩ := h_x_nezero
  simp_rw [← RingOfIntegers.coe_eq_algebraMap]
  fun_prop

@[deprecated (since := "2026-03-03")] alias mulSupport_finite := hasFiniteMulSupport

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_eq_zero_iff, IsFractionRing, IsFractionRing.div_surjective, RingOfIntegers, RingOfIntegers.coe_eq_algebraMap, algebraMap_eq_zero_iff, coe_eq_algebraMap, div_eq_zero_iff, div_surjective, fun_prop, h_x_nezero, ne_eq, not_or, simp_rw
-/
theorem hasFiniteMulSupport {x : K} (h_x_nezero : x != 0) :
    (fun w : FinitePlace K => w x).HasFiniteMulSupport := by
  rcases IsFractionRing.div_surjective (𝓞 K) x with ⟨a, b, hb, rfl⟩
  simp_all only [ne_eq, div_eq_zero_iff, FaithfulSMul.algebraMap_eq_zero_iff, not_or, map_div₀]
  obtain ⟨ha, hb⟩ := h_x_nezero
  simp_rw [← RingOfIntegers.coe_eq_algebraMap]
  fun_prop

@[deprecated (since := "2026-03-03")] alias mulSupport_finite := hasFiniteMulSupport

/--
lemma `hasFiniteMulSupport_fun_pow_multiplicity` / 引理 `hasFiniteMulSupport_fun_pow_multiplicity`

English:
lemma hasFiniteMulSupport_fun_pow_multiplicity
  statement: {M : Type*} [CommMonoid M] {I : Ideal (𝓞 K)}
  proof: UniqueFactorizationMonoid.hasFiniteMulSupport_fun_pow_multiplicity _
    (asIdeal_injective.comp maximalIdeal_injective) (fun v => v.maximalIdeal.irreducible) hI

protected

中文:
引理 hasFiniteMulSupport_fun_pow_multiplicity
  结论: {M : 类型} [交换幺半群 M] {I : 理想 (𝓞 K)}
  证明: UniqueFactorizationMonoid.hasFiniteMulSupport_fun_pow_multiplicity _
    (asIdeal_injective.comp maximalIdeal_injective) (fun v => v.maximalIdeal.irreducible) hI

protected

Depends on / 依赖: UniqueFactorizationMonoid, UniqueFactorizationMonoid.hasFiniteMulSupport_fun_pow_multiplicity, asIdeal_injective, asIdeal_injective.comp, hasFiniteMulSupport_fun_pow_multiplicity, irreducible, maximalIdeal, maximalIdeal_injective, v.maximalIdeal.irreducible
-/
lemma hasFiniteMulSupport_fun_pow_multiplicity {M : Type*} [CommMonoid M] {I : Ideal (𝓞 K)}
    (hI : I != ⊥) (f : Ideal (𝓞 K) -> M) :
    (fun v : FinitePlace K =>
      f v.maximalIdeal.asIdeal ^ multiplicity v.maximalIdeal.asIdeal I).HasFiniteMulSupport :=
  UniqueFactorizationMonoid.hasFiniteMulSupport_fun_pow_multiplicity _
    (asIdeal_injective.comp maximalIdeal_injective) (fun v => v.maximalIdeal.irreducible) hI

protected
/--
lemma `add_le` / 引理 `add_le`

English:
lemma add_le
  given: (v : FinitePlace K) (x y : K)
  proof: by
  obtain ⟨w, hw⟩ := v.prop
  have H x : v x = NumberField.HeightOneSpectrum.adicAbv K w x := by
    rw [show v x = v.val x from rfl]
    grind only [place_apply, norm_embedding]
  simpa only [H] using adicAbv_add_le_max K w x y

中文:
引理 add_le
  条件: (v : FinitePlace K) (x y : K)
  证明: by
  obtain ⟨w, hw⟩ := v.prop
  have H x : v x = NumberField.HeightOneSpectrum.adicAbv K w x := by
    rw [show v x = v.val x from rfl]
    grind only [place_apply, norm_embedding]
  simpa only [H] using adicAbv_add_le_max K w x y

Depends on / 依赖: HeightOneSpectrum, NumberField, NumberField.HeightOneSpectrum.adicAbv, adicAbv, adicAbv_add_le_max, norm_embedding, place_apply, v.prop, v.val
-/
lemma add_le (v : FinitePlace K) (x y : K) :
    v (x + y) <= max (v x) (v y) := by
  obtain ⟨w, hw⟩ := v.prop
  have H x : v x = NumberField.HeightOneSpectrum.adicAbv K w x := by
    rw [show v x = v.val x from rfl]
    grind only [place_apply, norm_embedding]
  simpa only [H] using adicAbv_add_le_max K w x y

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NonarchimedeanHomClass (FinitePlace K) K Real
  body: FinitePlace.add_le v a b

中文:
实例 :
  签名: Nonarchimedean态射类 (FinitePlace K) K 实数
  定义体: FinitePlace.add_le v a b

Depends on / 依赖: FinitePlace, FinitePlace.add_le, add_le
-/
instance : NonarchimedeanHomClass (FinitePlace K) K Real where
  map_add_le_max v a b := FinitePlace.add_le v a b

/--
lemma `equivHeightOneSpectrum_symm_apply` / 引理 `equivHeightOneSpectrum_symm_apply`

English:
lemma equivHeightOneSpectrum_symm_apply
  given: (v : HeightOneSpectrum (𝓞 K)) (x : K)
  proof: rfl

@[deprecated (since := "2026-03-11")]
alias IsDedekindDomain.HeightOneSpectrum.equivHeightOneSpectrum_symm_apply :=
  equivHeightOneSpectrum_symm_apply
@[deprecated (since := "2026-03-11")]
alias IsDedekindDomain.HeightOneSpectrum.embedding_mul_absNorm := embedding_mul_absNorm

中文:
引理 equivHeightOneSpectrum_symm_apply
  条件: (v : 高一谱 (𝓞 K)) (x : K)
  证明: rfl

@[deprecated (since := "2026-03-11")]
alias IsDedekindDomain.HeightOneSpectrum.equivHeightOneSpectrum_symm_apply :=
  equivHeightOneSpectrum_symm_apply
@[deprecated (since := "2026-03-11")]
alias IsDedekindDomain.HeightOneSpectrum.embedding_mul_absNorm := embedding_mul_absNorm
-/
lemma equivHeightOneSpectrum_symm_apply (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    (equivHeightOneSpectrum.symm v) x = ‖embedding v x‖ := rfl

@[deprecated (since := "2026-03-11")]
alias IsDedekindDomain.HeightOneSpectrum.equivHeightOneSpectrum_symm_apply :=
  equivHeightOneSpectrum_symm_apply
@[deprecated (since := "2026-03-11")]
alias IsDedekindDomain.HeightOneSpectrum.embedding_mul_absNorm := embedding_mul_absNorm

/--
lemma `finprod_finitePlace_pow_multiplicity` / 引理 `finprod_finitePlace_pow_multiplicity`

English:
lemma finprod_finitePlace_pow_multiplicity
  given: {I : Ideal (𝓞 K)} (hI : I != ⊥)
  proof: by
  conv_rhs => rw [← finprod_heightOneSpectrum_pow_multiplicity hI]
  simp only [← finprod_comp_equiv (equivHeightOneSpectrum (K := K)), equivHeightOneSpectrum_apply]

中文:
引理 finprod_finitePlace_pow_multiplicity
  条件: {I : 理想 (𝓞 K)} (hI : I != ⊥)
  证明: by
  conv_rhs => rw [← finprod_heightOneSpectrum_pow_multiplicity hI]
  simp only [← finprod_comp_equiv (equivHeightOneSpectrum (K := K)), equivHeightOneSpectrum_apply]

Depends on / 依赖: conv_rhs, equivHeightOneSpectrum, equivHeightOneSpectrum_apply, finprod_comp_equiv, finprod_heightOneSpectrum_pow_multiplicity
-/
lemma finprod_finitePlace_pow_multiplicity {I : Ideal (𝓞 K)} (hI : I != ⊥) :
    ∏ᶠ v : FinitePlace K, v.maximalIdeal.asIdeal ^ multiplicity v.maximalIdeal.asIdeal I = I := by
  conv_rhs => rw [← finprod_heightOneSpectrum_pow_multiplicity hI]
  simp only [← finprod_comp_equiv (equivHeightOneSpectrum (K := K)), equivHeightOneSpectrum_apply]

/--
lemma `apply_mul_absNorm_pow_eq_one` / 引理 `apply_mul_absNorm_pow_eq_one`

English:
lemma apply_mul_absNorm_pow_eq_one
  given: (v : FinitePlace K) {x : 𝓞 K} (hx : x != 0)
  proof: by
  have hnz : span {x} != ⊥ := mt Submodule.span_singleton_eq_bot.mp hx
  rw [← norm_embedding_eq v x]; rw [← Nat.cast_pow]; rw [← map_pow]; rw [← maxPowDividing_eq_pow_multiplicity hnz]
  exact HeightOneSpectrum.embedding_mul_absNorm K v.maximalIdeal hx

中文:
引理 apply_mul_absNorm_pow_eq_one
  条件: (v : FinitePlace K) {x : 𝓞 K} (hx : x != 0)
  证明: by
  have hnz : span {x} != ⊥ := mt Submodule.span_singleton_eq_bot.mp hx
  rw [← norm_embedding_eq v x]; rw [← Nat.cast_pow]; rw [← map_pow]; rw [← maxPowDividing_eq_pow_multiplicity hnz]
  exact HeightOneSpectrum.embedding_mul_absNorm K v.maximalIdeal hx

Depends on / 依赖: HeightOneSpectrum, HeightOneSpectrum.embedding_mul_absNorm, Nat.cast_pow, Submodule, Submodule.span_singleton_eq_bot.mp, cast_pow, embedding_mul_absNorm, map_pow, maxPowDividing_eq_pow_multiplicity, maximalIdeal, norm_embedding_eq, span_singleton_eq_bot, v.maximalIdeal
-/
lemma apply_mul_absNorm_pow_eq_one (v : FinitePlace K) {x : 𝓞 K} (hx : x != 0) :
    v x * v.maximalIdeal.asIdeal.absNorm ^ multiplicity v.maximalIdeal.asIdeal (span {x}) = 1 := by
  have hnz : span {x} != ⊥ := mt Submodule.span_singleton_eq_bot.mp hx
  rw [← norm_embedding_eq v x]; rw [← Nat.cast_pow]; rw [← map_pow]; rw [← maxPowDividing_eq_pow_multiplicity hnz]
  exact HeightOneSpectrum.embedding_mul_absNorm K v.maximalIdeal hx

end FinitePlace

section LiesOver

namespace HeightOneSpectrum

variable {L : Type*} [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
variable [Algebra (v.adicCompletion K) (w.adicCompletion L)]
    [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
    [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)]

local notation "Kv" => v.adicCompletion K
local notation "Lw" => w.adicCompletion L

open scoped TensorProduct Valued in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module.Finite Kv Lw
  body: let Φ : Kv otimes[K] L ->ₗ[Kv] Lw := Algebra.TensorProduct.lift (Algebra.algHom Kv Kv Lw)
.toLinearMap (Algebra.algHom K L Lw) (fun _ _ => mul_comm ..)
  have h_dense : DenseRange Φ := by
    apply (w.denseRange_algebraMap L).mono
    rintro _ ⟨l, rfl⟩
    exact ⟨1 otimesₜ l, by simp [Φ, Algebra.algHom]⟩
  .of_surjective Φ (by
    rw [← Set.range_eq_univ]; rw [← Φ.coe_range]; rw [← Φ.range.closed_of_finiteDimensional.closure_eq]
    exact h_dense.closure_range)

中文:
实例 :
  签名: 模.有限 Kv Lw
  定义体: let Φ : Kv otimes[K] L ->ₗ[Kv] Lw := Algebra.TensorProduct.lift (Algebra.algHom Kv Kv Lw)
.toLinearMap (Algebra.algHom K L Lw) (fun _ _ => mul_comm ..)
  have h_dense : DenseRange Φ := by
    apply (w.denseRange_algebraMap L).mono
    rintro _ ⟨l, rfl⟩
    exact ⟨1 otimesₜ l, by simp [Φ, Algebra.algHom]⟩
  .of_surjective Φ (by
    rw [← Set.range_eq_univ]; rw [← Φ.coe_range]; rw [← Φ.range.closed_of_finiteDimensional.closure_eq]
    exact h_dense.closure_range)

Depends on / 依赖: Algebra, Algebra.TensorProduct.lift, Algebra.algHom, DenseRange, Set.range_eq_univ, TensorProduct, algHom, closed_of_finiteDimensional, closure_eq, closure_range, coe_range, denseRange_algebraMap, h_dense, h_dense.closure_range, mul_comm, of_surjective, otimes, range.closed_of_finiteDimensional.closure_eq, range_eq_univ, toLinearMap
-/
instance : Module.Finite Kv Lw :=
  let Φ : Kv otimes[K] L ->ₗ[Kv] Lw := Algebra.TensorProduct.lift (Algebra.algHom Kv Kv Lw)
.toLinearMap (Algebra.algHom K L Lw) (fun _ _ => mul_comm ..)
  have h_dense : DenseRange Φ := by
    apply (w.denseRange_algebraMap L).mono
    rintro _ ⟨l, rfl⟩
    exact ⟨1 otimesₜ l, by simp [Φ, Algebra.algHom]⟩
  .of_surjective Φ (by
    rw [← Set.range_eq_univ]; rw [← Φ.coe_range]; rw [← Φ.range.closed_of_finiteDimensional.closure_eq]
    exact h_dense.closure_range)

end HeightOneSpectrum

end LiesOver

end NumberField
