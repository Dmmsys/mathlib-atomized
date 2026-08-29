/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.Algebra.Order.Hom.Units
public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.Valuation.Discrete.RankOne
public import Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology
public import Mathlib.RingTheory.DedekindDomain.AdicValuation


/-!
# Ramification theory for valuations

- `A` is a Dedekind domain with field of fractions `K`.
- `B` is a Dedekind domain with field of fractions `L`.
- `L` is a field extension of `K`.
- `v` is a height one prime ideal of `A`.
- `w` is a height one prime ideal of `B` lying over `v`.

This file establishes the relationship between the adic valuation on `K` associated to `v` and the
adic valuation on `L` associated to `w`, in terms of the ramification index.
-/

@[expose] public section

namespace IsDedekindDomain.HeightOneSpectrum

open WithZero Ideal.IsDedekindDomain Valuation.IsRankOneDiscrete

section AKLB

variable {A K : Type*} (L : Type*) {B : Type*}
variable [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B] [Algebra A B]
  [Module.IsTorsionFree A B]
variable [Field K] [Field L] [Algebra K L]
variable [Algebra A K] [IsFractionRing A K] [Algebra A L] [IsScalarTower A K L]
variable [Algebra B L] [IsFractionRing B L] [IsScalarTower A B L]
variable (v : HeightOneSpectrum A) (w : HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal]

/--
theorem `intValuation_liesOver` / 定理 `intValuation_liesOver`

English:
theorem intValuation_liesOver
  given: (x : A)
  proof: by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [ramificationIdx'_ne_zero_of_liesOver w.asIdeal v.ne_bot]
  rw [intValuation_eq_exp_neg_multiplicity v hx]; rw [intValuation_eq_exp_neg_multiplicity w (by simpa)]; rw [← Set.image_singleton]; rw [← Ideal.map_span]; rw [exp_neg]; rw [exp_neg]; rw [inv_pow]; rw [← exp_nsmul]; rw [Int.nsmul_eq_mul]; rw [inv_inj]; rw [exp_inj]; rw [← Nat.cast_mul]; rw [Nat.cast_inj]
.symm refine multiplicity_eq_of_emultiplicity_eq_some ?_
  replace hx : Ideal.span {x} != ⊥ := by simp [hx]
  rw [emultiplicity_map_eq_ramificationIdx'_mul hx v.irreducible w.irreducible w.ne_bot]; rw [Nat.cast_mul]; rw [(FiniteMultiplicity.of_prime_left v.prime hx).emultiplicity_eq_multiplicity]

中文:
定理 intValuation_liesOver
  条件: (x : A)
  证明: by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [ramificationIdx'_ne_zero_of_liesOver w.asIdeal v.ne_bot]
  rw [intValuation_eq_exp_neg_multiplicity v hx]; rw [intValuation_eq_exp_neg_multiplicity w (by simpa)]; rw [← Set.image_singleton]; rw [← Ideal.map_span]; rw [exp_neg]; rw [exp_neg]; rw [inv_pow]; rw [← exp_nsmul]; rw [Int.nsmul_eq_mul]; rw [inv_inj]; rw [exp_inj]; rw [← Nat.cast_mul]; rw [Nat.cast_inj]
.symm refine multiplicity_eq_of_emultiplicity_eq_some ?_
  replace hx : Ideal.span {x} != ⊥ := by simp [hx]
  rw [emultiplicity_map_eq_ramificationIdx'_mul hx v.irreducible w.irreducible w.ne_bot]; rw [Nat.cast_mul]; rw [(FiniteMultiplicity.of_prime_left v.prime hx).emultiplicity_eq_multiplicity]

Depends on / 依赖: Ideal.map_span, Ideal.span, Int.nsmul_eq_mul, Nat.cast_inj, Nat.cast_mul, Set.image_singleton, _ne_zero_of_liesOver, asIdeal, cast_inj, cast_mul, eq_or_ne, exp_inj, exp_neg, exp_nsmul, image_singleton, intValuation_eq_exp_neg_multiplicity, inv_inj, inv_pow, map_span, multiplicity_eq_of_emultiplicity_eq_some
-/
theorem intValuation_liesOver (x : A) :
    v.intValuation x ^ (v.asIdeal.ramificationIdx' w.asIdeal) =
      w.intValuation (algebraMap A B x) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [ramificationIdx'_ne_zero_of_liesOver w.asIdeal v.ne_bot]
  rw [intValuation_eq_exp_neg_multiplicity v hx]; rw [intValuation_eq_exp_neg_multiplicity w (by simpa)]; rw [← Set.image_singleton]; rw [← Ideal.map_span]; rw [exp_neg]; rw [exp_neg]; rw [inv_pow]; rw [← exp_nsmul]; rw [Int.nsmul_eq_mul]; rw [inv_inj]; rw [exp_inj]; rw [← Nat.cast_mul]; rw [Nat.cast_inj]
.symm refine multiplicity_eq_of_emultiplicity_eq_some ?_
  replace hx : Ideal.span {x} != ⊥ := by simp [hx]
  rw [emultiplicity_map_eq_ramificationIdx'_mul hx v.irreducible w.irreducible w.ne_bot]; rw [Nat.cast_mul]; rw [(FiniteMultiplicity.of_prime_left v.prime hx).emultiplicity_eq_multiplicity]

/--
theorem `valuation_liesOver` / 定理 `valuation_liesOver`

English:
theorem valuation_liesOver
  given: (x : K)
  proof: by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  simp [valuation_of_algebraMap, div_pow, ← IsScalarTower.algebraMap_apply A K L,
    IsScalarTower.algebraMap_apply A B L, intValuation_liesOver v w]

中文:
定理 valuation_liesOver
  条件: (x : K)
  证明: by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  simp [valuation_of_algebraMap, div_pow, ← IsScalarTower.algebraMap_apply A K L,
    IsScalarTower.algebraMap_apply A B L, intValuation_liesOver v w]

Depends on / 依赖: IsFractionRing, IsFractionRing.div_surjective, IsScalarTower, IsScalarTower.algebraMap_apply, algebraMap_apply, div_pow, div_surjective, intValuation_liesOver, valuation_of_algebraMap
-/
theorem valuation_liesOver (x : K) :
    v.valuation K x ^ v.asIdeal.ramificationIdx' w.asIdeal =
      w.valuation L (algebraMap K L x) := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  simp [valuation_of_algebraMap, div_pow, ← IsScalarTower.algebraMap_apply A K L,
    IsScalarTower.algebraMap_apply A B L, intValuation_liesOver v w]

variable (K)

/--
theorem `uniformContinuous_algebraMap_liesOver` / 定理 `uniformContinuous_algebraMap_liesOver`

English:
theorem uniformContinuous_algebraMap_liesOver
  proof: by
  refine uniformContinuous_of_continuousAt_zero _ ?_
  rw [ContinuousAt]; rw [map_zero]; rw [(IsValuativeTopology.hasBasis_nhds_zero _).tendsto_iff
    (IsValuativeTopology.hasBasis_nhds_zero _)]
  intro γL _
  /-
  `ValueGroup₀ (w.valuation L)` <--------> `ℤᵐ⁰` <--------> `ValueGroup₀ (v.valuation K)`
            ^ ^
            | |
            | |
            v v
  `ValueGroup₀ (WithVal.valuation _)` `ValueGroup₀ (WithVal.valuation _)`
            ^ ^
            | |
            | |
            v v
  `γL : ValuativeRel.ValueGroupWithZero Lʷ` `γK: ValuativeRel.ValueGroupWithZero Kᵛ`
  -/
  let e := v.asIdeal.ramificationIdx' w.asIdeal
  -- push `γL` to `ℤᵐ⁰`
  let σL := WithVal.valueGroupOrderIso₀ (w.valuation L)
  let σw := valueGroup₀_equiv_withZeroMulInt (w.valuation L)
  let σwV := ValuativeRel.ValueGroupWithZero.orderMonoidIso (WithVal.valuation (w.valuation L))
  let m : Intᵐ⁰ := σw (σL (σwV γL))
  -- `ℤᵐ⁰` values in `K` exponentiate by `e` in `L` so take the `e`th root and pull back to `γK`
  let σvV := ValuativeRel.ValueGroupWithZero.orderMonoidIso (WithVal.valuation (v.valuation K))
  let σv := valueGroup₀_equiv_withZeroMulInt (v.valuation K)
  let σK := WithVal.valueGroupOrderIso₀ (v.valuation K)
  let γK := σvV.symm (σK.symm (σv.symm (exp (m.log / e))))
  have hγK : γK != 0 := by simp [γK, EmbeddingLike.map_eq_zero_iff (f := σK.symm)]
  use .mk0 _ hγK
  simp only [Units.val_mk0, Set.mem_ofPred_eq, true_and]
  intro x hx
  rcases eq_or_ne x 0 with rfl | hx₀; · simp
  rw [σvV.lt_symm_apply]; rw [σK.lt_symm_apply]; rw [σv.lt_symm_apply]; rw [ValuativeRel.ValueGroupWithZero.orderMonoidIso_valuation_eq_restrict₀]; rw [← Valuation.restrict_def]; rw [WithVal.valueGroupOrderIso₀_restrict]; rw [valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective (v.valuation_surjective K)]; rw [← log_lt_log (by simp_all) (by simp)] at hx
  rw [← σwV.strictMono.lt_iff_lt]; rw [← σL.strictMono.lt_iff_lt]; rw [ValuativeRel.ValueGroupWithZero.orderMonoidIso_valuation_eq_restrict₀]; rw [← Valuation.restrict_def]; rw [WithVal.valueGroupOrderIso₀_restrict]; rw [← σw.strictMono.lt_iff_lt]; rw [valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective (w.valuation_surjective L)]; rw [WithVal.algebraMap_left_apply]; rw [WithVal.algebraMap_right_apply]; rw [← valuation_liesOver L v]; rw [← log_lt_log (by simp_all) (by simp [EmbeddingLike.map_eq_zero_iff (f := σwV)]), log_pow,
    nsmul_eq_mul, mul_comm]
  exact Int.mul_lt_of_lt_ediv
    (mod_cast pos_of_ne_zero (ramificationIdx'_ne_zero_of_liesOver w.asIdeal v.ne_bot)) hx

中文:
定理 uniformContinuous_algebraMap_liesOver
  证明: by
  refine uniformContinuous_of_continuousAt_zero _ ?_
  rw [ContinuousAt]; rw [map_zero]; rw [(IsValuativeTopology.hasBasis_nhds_zero _).tendsto_iff
    (IsValuativeTopology.hasBasis_nhds_zero _)]
  intro γL _
  /-
  `ValueGroup₀ (w.valuation L)` <--------> `ℤᵐ⁰` <--------> `ValueGroup₀ (v.valuation K)`
            ^ ^
            | |
            | |
            v v
  `ValueGroup₀ (WithVal.valuation _)` `ValueGroup₀ (WithVal.valuation _)`
            ^ ^
            | |
            | |
            v v
  `γL : ValuativeRel.ValueGroupWithZero Lʷ` `γK: ValuativeRel.ValueGroupWithZero Kᵛ`
  -/
  let e := v.asIdeal.ramificationIdx' w.asIdeal
  -- push `γL` to `ℤᵐ⁰`
  let σL := WithVal.valueGroupOrderIso₀ (w.valuation L)
  let σw := valueGroup₀_equiv_withZeroMulInt (w.valuation L)
  let σwV := ValuativeRel.ValueGroupWithZero.orderMonoidIso (WithVal.valuation (w.valuation L))
  let m : Intᵐ⁰ := σw (σL (σwV γL))
  -- `ℤᵐ⁰` values in `K` exponentiate by `e` in `L` so take the `e`th root and pull back to `γK`
  let σvV := ValuativeRel.ValueGroupWithZero.orderMonoidIso (WithVal.valuation (v.valuation K))
  let σv := valueGroup₀_equiv_withZeroMulInt (v.valuation K)
  let σK := WithVal.valueGroupOrderIso₀ (v.valuation K)
  let γK := σvV.symm (σK.symm (σv.symm (exp (m.log / e))))
  have hγK : γK != 0 := by simp [γK, EmbeddingLike.map_eq_zero_iff (f := σK.symm)]
  use .mk0 _ hγK
  simp only [Units.val_mk0, Set.mem_ofPred_eq, true_and]
  intro x hx
  rcases eq_or_ne x 0 with rfl | hx₀; · simp
  rw [σvV.lt_symm_apply]; rw [σK.lt_symm_apply]; rw [σv.lt_symm_apply]; rw [ValuativeRel.ValueGroupWithZero.orderMonoidIso_valuation_eq_restrict₀]; rw [← Valuation.restrict_def]; rw [WithVal.valueGroupOrderIso₀_restrict]; rw [valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective (v.valuation_surjective K)]; rw [← log_lt_log (by simp_all) (by simp)] at hx
  rw [← σwV.strictMono.lt_iff_lt]; rw [← σL.strictMono.lt_iff_lt]; rw [ValuativeRel.ValueGroupWithZero.orderMonoidIso_valuation_eq_restrict₀]; rw [← Valuation.restrict_def]; rw [WithVal.valueGroupOrderIso₀_restrict]; rw [← σw.strictMono.lt_iff_lt]; rw [valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective (w.valuation_surjective L)]; rw [WithVal.algebraMap_left_apply]; rw [WithVal.algebraMap_right_apply]; rw [← valuation_liesOver L v]; rw [← log_lt_log (by simp_all) (by simp [EmbeddingLike.map_eq_zero_iff (f := σwV)]), log_pow,
    nsmul_eq_mul, mul_comm]
  exact Int.mul_lt_of_lt_ediv
    (mod_cast pos_of_ne_zero (ramificationIdx'_ne_zero_of_liesOver w.asIdeal v.ne_bot)) hx

Depends on / 依赖: ContinuousAt, IsValuativeTopology, IsValuativeTopology.hasBasis_nhds_zero, hasBasis_nhds_zero, map_zero, tendsto_iff, uniformContinuous_of_continuousAt_zero
-/
theorem uniformContinuous_algebraMap_liesOver :
    UniformContinuous (algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation L))) := by
  refine uniformContinuous_of_continuousAt_zero _ ?_
  rw [ContinuousAt]; rw [map_zero]; rw [(IsValuativeTopology.hasBasis_nhds_zero _).tendsto_iff
    (IsValuativeTopology.hasBasis_nhds_zero _)]
  intro γL _
  /-
  `ValueGroup₀ (w.valuation L)` <--------> `ℤᵐ⁰` <--------> `ValueGroup₀ (v.valuation K)`
            ^ ^
            | |
            | |
            v v
  `ValueGroup₀ (WithVal.valuation _)` `ValueGroup₀ (WithVal.valuation _)`
            ^ ^
            | |
            | |
            v v
  `γL : ValuativeRel.ValueGroupWithZero Lʷ` `γK: ValuativeRel.ValueGroupWithZero Kᵛ`
  -/
  let e := v.asIdeal.ramificationIdx' w.asIdeal
  -- push `γL` to `ℤᵐ⁰`
  let σL := WithVal.valueGroupOrderIso₀ (w.valuation L)
  let σw := valueGroup₀_equiv_withZeroMulInt (w.valuation L)
  let σwV := ValuativeRel.ValueGroupWithZero.orderMonoidIso (WithVal.valuation (w.valuation L))
  let m : Intᵐ⁰ := σw (σL (σwV γL))
  -- `ℤᵐ⁰` values in `K` exponentiate by `e` in `L` so take the `e`th root and pull back to `γK`
  let σvV := ValuativeRel.ValueGroupWithZero.orderMonoidIso (WithVal.valuation (v.valuation K))
  let σv := valueGroup₀_equiv_withZeroMulInt (v.valuation K)
  let σK := WithVal.valueGroupOrderIso₀ (v.valuation K)
  let γK := σvV.symm (σK.symm (σv.symm (exp (m.log / e))))
  have hγK : γK != 0 := by simp [γK, EmbeddingLike.map_eq_zero_iff (f := σK.symm)]
  use .mk0 _ hγK
  simp only [Units.val_mk0, Set.mem_ofPred_eq, true_and]
  intro x hx
  rcases eq_or_ne x 0 with rfl | hx₀; · simp
  rw [σvV.lt_symm_apply]; rw [σK.lt_symm_apply]; rw [σv.lt_symm_apply]; rw [ValuativeRel.ValueGroupWithZero.orderMonoidIso_valuation_eq_restrict₀]; rw [← Valuation.restrict_def]; rw [WithVal.valueGroupOrderIso₀_restrict]; rw [valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective (v.valuation_surjective K)]; rw [← log_lt_log (by simp_all) (by simp)] at hx
  rw [← σwV.strictMono.lt_iff_lt]; rw [← σL.strictMono.lt_iff_lt]; rw [ValuativeRel.ValueGroupWithZero.orderMonoidIso_valuation_eq_restrict₀]; rw [← Valuation.restrict_def]; rw [WithVal.valueGroupOrderIso₀_restrict]; rw [← σw.strictMono.lt_iff_lt]; rw [valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective (w.valuation_surjective L)]; rw [WithVal.algebraMap_left_apply]; rw [WithVal.algebraMap_right_apply]; rw [← valuation_liesOver L v]; rw [← log_lt_log (by simp_all) (by simp [EmbeddingLike.map_eq_zero_iff (f := σwV)]), log_pow,
    nsmul_eq_mul, mul_comm]
  exact Int.mul_lt_of_lt_ediv
    (mod_cast pos_of_ne_zero (ramificationIdx'_ne_zero_of_liesOver w.asIdeal v.ne_bot)) hx

end AKLB

end IsDedekindDomain.HeightOneSpectrum
