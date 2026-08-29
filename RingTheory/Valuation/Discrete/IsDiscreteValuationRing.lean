/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-!
# Valuations associated to discrete valuation rings

Given a discrete valuation ring `A` with field of fractions `K`, the maximal ideal of `A`
is a height-one prime, and the associated valuation `(maximalIdeal A).valuation K` is
a rank-one discrete valuation on `K`.

## Main Definitions

* `IsDiscreteValuationRing.maximalIdeal`: The maximal ideal of `A` (as an element of
  `HeightOneSpectrum A`).
* `IsDiscreteValuationRing.equivValuationSubring`: The ring isomorphism between a DVR and the
  unit ball in its field of fractions endowed with the adic valuation of the maximal ideal.

## Main Results

* `IsDiscreteValuationRing.isRankOneDiscrete`: Given a DVR `A` and a field `K` satisfying
  `IsFractionRing A K`, the valuation induced on `K` is discrete.
-/

@[expose] public section

namespace IsDiscreteValuationRing

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsDiscreteValuationRing
  IsLocalRing MonoidWithZeroHom Multiplicative Subring Valuation

variable (A K : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field K]
  [Algebra A K] [IsFractionRing A K]

/--
Definition of `maximalIdeal` / `maximalIdeal` 的定义

English:
definition maximalIdeal
  signature: : HeightOneSpectrum A where
  body: IsLocalRing.maximalIdeal A
  isPrime := Ideal.IsMaximal.isPrime (maximalIdeal.isMaximal A)
  ne_bot := by simpa [ne_eq, ← isField_iff_maximalIdeal_eq] using not_isField A

中文:
定义 maximalIdeal
  签名: : HeightOneSpectrum A where
  定义体: IsLocalRing.maximalIdeal A
  isPrime := Ideal.IsMaximal.isPrime (maximalIdeal.isMaximal A)
  ne_bot := by simpa [ne_eq, ← isField_iff_maximalIdeal_eq] using not_isField A

Depends on / 依赖: IsLocalRing, IsLocalRing.maximalIdeal, maximalIdeal
-/
def maximalIdeal : HeightOneSpectrum A where
  asIdeal := IsLocalRing.maximalIdeal A
  isPrime := Ideal.IsMaximal.isPrime (maximalIdeal.isMaximal A)
  ne_bot := by simpa [ne_eq, ← isField_iff_maximalIdeal_eq] using not_isField A

/--
Instance `isRankOneDiscrete` / 实例 `isRankOneDiscrete`

English:
instance isRankOneDiscrete
  signature: :
  body: by
  have : Nontrivial (valueGroup
      (.ofClass (valuation K (maximalIdeal A)))) := by
    let v := (maximalIdeal A).valuation K
.choose let π := valuation_exists_uniformizer K (maximalIdeal A)
    have hπ : v π = ↑(ofAdd (-1 : Int)) :=
.choose_spec valuation_exists_uniformizer K (maximalIdeal A)

中文:
实例 isRankOneDiscrete
  签名: :
  定义体: by
  have : Nontrivial (valueGroup
      (.ofClass (valuation K (maximalIdeal A)))) := by
    let v := (maximalIdeal A).valuation K
.choose let π := valuation_exists_uniformizer K (maximalIdeal A)
    have hπ : v π = ↑(ofAdd (-1 : Int)) :=
.choose_spec valuation_exists_uniformizer K (maximalIdeal A)

Depends on / 依赖: Nontrivial, Subgroup, Subgroup.nontrivial_iff_exists_ne_one, Units.mk0, choose_spec, infer_instance, maximalIdeal, mem_valueGroup, nontrivial_iff_exists_ne_one, not_eq_of_beq_eq_false, ofClass, valuation, valuation_exists_uniformizer, valueGroup
-/
instance isRankOneDiscrete :
    IsRankOneDiscrete ((maximalIdeal A).valuation K) := by
  have : Nontrivial (valueGroup
      (.ofClass (valuation K (maximalIdeal A)))) := by
    let v := (maximalIdeal A).valuation K
.choose let π := valuation_exists_uniformizer K (maximalIdeal A)
    have hπ : v π = ↑(ofAdd (-1 : Int)) :=
.choose_spec valuation_exists_uniformizer K (maximalIdeal A)
    rw [Subgroup.nontrivial_iff_exists_ne_one]
    use Units.mk0 (v π) (by simp [hπ])
    constructor
    · apply mem_valueGroup
      use π
      simp [v]
    · simpa [hπ] using not_eq_of_beq_eq_false rfl
  infer_instance

variable {A K}

open scoped WithZero

/--
theorem `exists_lift_of_le_one` / 定理 `exists_lift_of_le_one`

English:
theorem exists_lift_of_le_one
  given: {x : K} (H : ((maximalIdeal A).valuation K) x <= (1 : Intᵐ⁰))
  proof: by
  obtain ⟨π, hπ⟩ := exists_irreducible A
  obtain ⟨a, b, hb, h_frac⟩ := IsFractionRing.div_surjective A x
  by_cases ha : a = 0
  · rw [← h_frac]
    use 0
    rw [ha]; rw [map_zero]; rw [zero_div]
  · rw [← h_frac] at H
    obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible ha hπ
    obtain ⟨m, w

中文:
定理 exists_lift_of_le_one
  条件: {x : K} (H : ((maximalIdeal A).valuation K) x <= (1 : 整数ᵐ⁰))
  证明: by
  obtain ⟨π, hπ⟩ := exists_irreducible A
  obtain ⟨a, b, hb, h_frac⟩ := IsFractionRing.div_surjective A x
  by_cases ha : a = 0
  · rw [← h_frac]
    use 0
    rw [ha]; rw [map_zero]; rw [zero_div]
  · rw [← h_frac] at H
    obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible ha hπ
    obtain ⟨m, w

Depends on / 依赖: IsFractionRing, IsFractionRing.div_surjective, div_eq_mul_inv, div_surjective, eq_unit_mul_pow_irreducible, exists_irreducible, h_frac, map_mul, map_zero, mul_as, mul_comm, mul_mem_nonZeroDivisors, mul_mem_nonZeroDivisors.mp, ne_zero, nonZeroDivisors, nonZeroDivisors.ne_zero, replace, zero_div
-/
theorem exists_lift_of_le_one {x : K} (H : ((maximalIdeal A).valuation K) x <= (1 : Intᵐ⁰)) :
    exists a : A, algebraMap A K a = x := by
  obtain ⟨π, hπ⟩ := exists_irreducible A
  obtain ⟨a, b, hb, h_frac⟩ := IsFractionRing.div_surjective A x
  by_cases ha : a = 0
  · rw [← h_frac]
    use 0
    rw [ha]; rw [map_zero]; rw [zero_div]
  · rw [← h_frac] at H
    obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible ha hπ
    obtain ⟨m, w, rfl⟩ := eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero hb) hπ
    replace hb := (mul_mem_nonZeroDivisors.mp hb).2
    rw [mul_comm (w : A) _]; rw [map_mul _ (u : A) _]; rw [map_mul _ _ (w : A)]; rw [div_eq_mul_inv]; rw [mul_assoc]; rw [Valuation.map_mul]; rw [Integers.one_of_isUnit' u.isUnit (valuation_le_one _)]; rw [one_mul]; rw [mul_inv]; rw [← mul_assoc]; rw [Valuation.map_mul]; rw [map_mul]; rw [map_inv₀]; rw [map_inv₀]; rw [Integers.one_of_isUnit' w.isUnit (valuation_le_one _)]; rw [inv_one]; rw [mul_one]; rw [← div_eq_mul_inv]; rw [← map_div₀]; rw [← IsFractionRing.mk'_mk_eq_div hb]; rw [valuation_of_mk']; rw [map_pow]; rw [map_pow] at H
    have h_mn : m <= n := by
      have v_π_lt_one := (intValuation_lt_one_iff_dvd (maximalIdeal A) π).mpr
          (dvd_of_eq ((irreducible_iff_uniformizer _).mp hπ))
      have v_π_ne_zero : (maximalIdeal A).intValuation π != 0 := intValuation_ne_zero _ _ hπ.ne_zero
      zify
      rw [← WithZero.coe_one]; rw [div_eq_mul_inv]; rw [← zpow_natCast]; rw [← zpow_natCast]; rw [← ofAdd_zero]; rw [← zpow_neg]; rw [← zpow_add₀ v_π_ne_zero]; rw [← sub_eq_add_neg] at H
      rwa [← sub_nonneg, ← zpow_le_one_iff_right_of_lt_one₀ (zero_lt_iff.mpr v_π_ne_zero)
        v_π_lt_one]
    use u * π ^ (n - m) * w.2
    simp only [← h_frac, Units.inv_eq_val_inv, _root_.map_mul, _root_.map_pow, map_units_inv,
      mul_assoc, mul_div_assoc ((algebraMap A _) ↑u) _ _]
    congr 1
    rw [div_eq_mul_inv]; rw [mul_inv]; rw [mul_comm ((algebraMap A _) ↑w)⁻¹ _]; rw [←
      mul_assoc _ _ ((algebraMap A _) ↑w)⁻¹]
    congr
    rw [pow_sub₀ _ _ h_mn]
    apply IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
    rw [mem_nonZeroDivisors_iff_ne_zero]
    exact hπ.ne_zero

/--
lemma `mker_valuation_eq_isUnitSubmonoid` / 引理 `mker_valuation_eq_isUnitSubmonoid`

English:
lemma mker_valuation_eq_isUnitSubmonoid
  proof: by
  ext a
  simp only [MonoidHom.mem_mker, Submonoid.mem_map]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨b, rfl⟩ := IsDiscreteValuationRing.exists_lift_of_le_one h.le
    rw [valuation_eq_one_iff_notMem] at h
    simp only [IsDiscreteValuationRing.maximalIdeal, IsLocalRing.mem_maximalIdeal, me

中文:
引理 mker_valuation_eq_isUnitSubmonoid
  证明: by
  ext a
  simp only [MonoidHom.mem_mker, Submonoid.mem_map]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨b, rfl⟩ := IsDiscreteValuationRing.exists_lift_of_le_one h.le
    rw [valuation_eq_one_iff_notMem] at h
    simp only [IsDiscreteValuationRing.maximalIdeal, IsLocalRing.mem_maximalIdeal, me

Depends on / 依赖: IsDiscreteValuationRing, IsDiscreteValuationRing.exists_lift_of_le_one, IsDiscreteValuationRing.maximalIdeal, IsLocalRing, IsLocalRing.mem_maximalIdeal, MonoidHom, MonoidHom.mem_mker, Submonoid, Submonoid.mem_map, exists_lift_of_le_one, h.le, maximalIdeal, mem_map, mem_maximalIdeal, mem_mker, mem_nonunits_iff, not_not, valuation_eq_one_iff_notMem
-/
lemma mker_valuation_eq_isUnitSubmonoid :
    MonoidHom.mker ((IsDiscreteValuationRing.maximalIdeal A).valuation K) =
    (IsUnit.submonoid A).map (algebraMap A K) := by
  ext a
  simp only [MonoidHom.mem_mker, Submonoid.mem_map]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨b, rfl⟩ := IsDiscreteValuationRing.exists_lift_of_le_one h.le
    rw [valuation_eq_one_iff_notMem] at h
    simp only [IsDiscreteValuationRing.maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      not_not] at h
    use b, h
  · obtain ⟨x, h, rfl⟩ := h
    simpa [IsDiscreteValuationRing.maximalIdeal] using! h

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `associated_of_valuation_eq` / 定理 `associated_of_valuation_eq`

English:
theorem associated_of_valuation_eq
  statement: (x y : K)
  proof: by
  by_cases hx : x = 0
  · rw [eq_comm] at h
    simp_all
  by_cases hy : y = 0
  · simp_all
  have : (y / x) in MonoidHom.mker (((maximalIdeal A).valuation K)) := by simp_all
  rw [mker_valuation_eq_isUnitSubmonoid] at this
  obtain ⟨u, h⟩ := this
  use IsUnit.unit h.1
  simp only [Units.smul_def

中文:
定理 associated_of_valuation_eq
  结论: (x y : K)
  证明: by
  by_cases hx : x = 0
  · rw [eq_comm] at h
    simp_all
  by_cases hy : y = 0
  · simp_all
  have : (y / x) in MonoidHom.mker (((maximalIdeal A).valuation K)) := by simp_all
  rw [mker_valuation_eq_isUnitSubmonoid] at this
  obtain ⟨u, h⟩ := this
  use IsUnit.unit h.1
  simp only [Units.smul_def

Depends on / 依赖: Algebra, Algebra.smul_def, IsUnit, IsUnit.unit, IsUnit.unit_spec, MonoidHom, MonoidHom.mker, Units.smul_def, eq_comm, maximalIdeal, mker_valuation_eq_isUnitSubmonoid, smul_def, unit_spec, valuation
-/
theorem associated_of_valuation_eq (x y : K)
    (h : ((maximalIdeal A).valuation K) x =
    ((maximalIdeal A).valuation K) y) : exists u : Aˣ, u • x = y := by
  by_cases hx : x = 0
  · rw [eq_comm] at h
    simp_all
  by_cases hy : y = 0
  · simp_all
  have : (y / x) in MonoidHom.mker (((maximalIdeal A).valuation K)) := by simp_all
  rw [mker_valuation_eq_isUnitSubmonoid] at this
  obtain ⟨u, h⟩ := this
  use IsUnit.unit h.1
  simp only [Units.smul_def, Algebra.smul_def, IsUnit.unit_spec, h.2]
  field_simp

/--
theorem `map_algebraMap_eq_valuationSubring` / 定理 `map_algebraMap_eq_valuationSubring`

English:
theorem map_algebraMap_eq_valuationSubring
  statement: Subring.map (algebraMap A K) ⊤ =
  proof: by
  ext
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨_, _, rfl⟩ := Subring.mem_map.mp h
    apply valuation_le_one
  · obtain ⟨y, rfl⟩ := exists_lift_of_le_one h
    rw [Subring.mem_map]
    exact ⟨y, mem_top _, rfl⟩

中文:
定理 map_algebraMap_eq_valuationSubring
  结论: Subring.map (algebraMap A K) ⊤ =
  证明: by
  ext
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨_, _, rfl⟩ := Subring.mem_map.mp h
    apply valuation_le_one
  · obtain ⟨y, rfl⟩ := exists_lift_of_le_one h
    rw [Subring.mem_map]
    exact ⟨y, mem_top _, rfl⟩

Depends on / 依赖: Subring, Subring.mem_map, Subring.mem_map.mp, exists_lift_of_le_one, mem_map, mem_top, valuation_le_one
-/
theorem map_algebraMap_eq_valuationSubring : Subring.map (algebraMap A K) ⊤ =
    ((maximalIdeal A).valuation K).valuationSubring.toSubring := by
  ext
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨_, _, rfl⟩ := Subring.mem_map.mp h
    apply valuation_le_one
  · obtain ⟨y, rfl⟩ := exists_lift_of_le_one h
    rw [Subring.mem_map]
    exact ⟨y, mem_top _, rfl⟩

/--
Definition of `equivValuationSubring` / `equivValuationSubring` 的定义

English:
definition equivValuationSubring
  signature: :
  body: (topEquiv.symm.trans (equivMapOfInjective ⊤ (algebraMap A K)
    (IsFractionRing.injective A _))).trans
      (RingEquiv.subringCongr map_algebraMap_eq_valuationSubring)

中文:
定义 equivValuationSubring
  签名: :
  定义体: (topEquiv.symm.trans (equivMapOfInjective ⊤ (algebraMap A K)
    (IsFractionRing.injective A _))).trans
      (RingEquiv.subringCongr map_algebraMap_eq_valuationSubring)

Depends on / 依赖: IsFractionRing, IsFractionRing.injective, RingEquiv, RingEquiv.subringCongr, algebraMap, equivMapOfInjective, injective, map_algebraMap_eq_valuationSubring, subringCongr, topEquiv, topEquiv.symm.trans
-/
noncomputable def equivValuationSubring :
    A ≃+* ((maximalIdeal A).valuation K).valuationSubring :=
  (topEquiv.symm.trans (equivMapOfInjective ⊤ (algebraMap A K)
    (IsFractionRing.injective A _))).trans
      (RingEquiv.subringCongr map_algebraMap_eq_valuationSubring)

/--
lemma `intValuation_maximalIdeal` / 引理 `intValuation_maximalIdeal`

English:
lemma intValuation_maximalIdeal
  given: (x : A)
  proof: by
  by_cases hx : x = 0
  · simp [hx]
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible A
  obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible hx hϖ
  have : (maximalIdeal A).intValuation ↑u = 1 := by simp [maximalIdeal]
  simp [(maximalIdeal A).intValuation_singleton hϖ.ne_zero
    hϖ.maximalIdeal_eq, hϖ, thi

中文:
引理 intValuation_maximalIdeal
  条件: (x : A)
  证明: by
  by_cases hx : x = 0
  · simp [hx]
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible A
  obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible hx hϖ
  have : (maximalIdeal A).intValuation ↑u = 1 := by simp [maximalIdeal]
  simp [(maximalIdeal A).intValuation_singleton hϖ.ne_zero
    hϖ.maximalIdeal_eq, hϖ, thi

Depends on / 依赖: WithZero, WithZero.exp_eq_coe_ofAdd, eq_unit_mul_pow_irreducible, exists_irreducible, exp_eq_coe_ofAdd, intValuation, intValuation_singleton, maximalIdeal, maximalIdeal_eq, ne_zero
-/
lemma intValuation_maximalIdeal (x : A) :
    (maximalIdeal A).intValuation x =
      (ENat.recTopCoe 0 (WithZero.coe <| Multiplicative.ofAdd <| Nat.cast · ) (addVal A x))⁻¹ := by
  by_cases hx : x = 0
  · simp [hx]
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible A
  obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible hx hϖ
  have : (maximalIdeal A).intValuation ↑u = 1 := by simp [maximalIdeal]
  simp [(maximalIdeal A).intValuation_singleton hϖ.ne_zero
    hϖ.maximalIdeal_eq, hϖ, this, WithZero.exp_eq_coe_ofAdd (n : Int)]

end IsDiscreteValuationRing

end
