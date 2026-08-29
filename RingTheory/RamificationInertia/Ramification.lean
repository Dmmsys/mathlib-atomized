/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.LocalRing.Length
public import Mathlib.RingTheory.LocalRing.ResidueField.Instances
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.Unramified.LocalRing

/-!
# Ramification index

Let `S/R` be an extension of rings, and let `q` be a prime ideal of `S` lying over a prime ideal
`p` of `R`. Let `Sq` be the localization of `S` and `q`, and let `pSq` be the image of `p` in `Sq`.
Then the ramification index of `q` over `R` is defined to be the length of the quotient `Sq/pSq` as
an `Sq`-module.

## Main definitions

* `Ideal.ramificationIdx q R`: The ramification index of `q` over `R`.

## Main statements

* `ramificationIdx'_eq_ramificationIdx`: The ramification index agrees with the usual definition in
  the case of Dedekind domains.
* `ramificationIdx_tower`: Ramification index is multiplicative in towers.

-/

@[expose] public section

namespace Ideal

section

variable {S : Type*} [CommRing S] (q : Ideal S) (R : Type*) [CommRing R] [Algebra R S]

open scoped Classical in
/--
Definition of `ramificationIdx` / `ramificationIdx` 的定义

English:
definition ramificationIdx
  signature: : Nat
  body: if _ : q.IsPrime then
    letI Sq := Localization.AtPrime q
    (Module.length Sq (Sq ⧸ (q.under R).map (algebraMap R Sq))).toNat
  else 0

中文:
定义 ramificationIdx
  签名: : 自然数
  定义体: if _ : q.IsPrime then
    letI Sq := Localization.AtPrime q
    (Module.length Sq (Sq ⧸ (q.under R).map (algebraMap R Sq))).toNat
  else 0

Depends on / 依赖: AtPrime, IsPrime, Localization, Localization.AtPrime, Module, Module.length, algebraMap, length, q.IsPrime, q.under
-/
noncomputable def ramificationIdx : Nat :=
  if _ : q.IsPrime then
    letI Sq := Localization.AtPrime q
    (Module.length Sq (Sq ⧸ (q.under R).map (algebraMap R Sq))).toNat
  else 0

/--
theorem `ramificationIdx_def` / 定理 `ramificationIdx_def`

English:
theorem ramificationIdx_def
  given: [q.IsPrime]
  proof: Localization.AtPrime q
    q.ramificationIdx R = (Module.length Sq (Sq ⧸ (q.under R).map (algebraMap R Sq))).toNat :=
  dif_pos _

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_def := ramificationIdx_def

中文:
定理 ramificationIdx_def
  条件: [q.是素]
  证明: Localization.AtPrime q
    q.ramificationIdx R = (Module.length Sq (Sq ⧸ (q.under R).map (algebraMap R Sq))).toNat :=
  dif_pos _

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_def := ramificationIdx_def

Depends on / 依赖: AtPrime, Localization, Localization.AtPrime
-/
theorem ramificationIdx_def [q.IsPrime] :
    letI Sq := Localization.AtPrime q
    q.ramificationIdx R = (Module.length Sq (Sq ⧸ (q.under R).map (algebraMap R Sq))).toNat :=
  dif_pos _

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_def := ramificationIdx_def

/--
theorem `ramificationIdx_of_not_isPrime` / 定理 `ramificationIdx_of_not_isPrime`

English:
theorem ramificationIdx_of_not_isPrime
  given: (hq : ¬ q.IsPrime)
  statement: q.ramificationIdx R = 0
  proof: dif_neg hq

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_of_not_isPrime :=
  ramificationIdx_of_not_isPrime

中文:
定理 ramificationIdx_of_not_isPrime
  条件: (hq : ¬ q.是素)
  结论: q.ramificationIdx R = 0
  证明: dif_neg hq

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_of_not_isPrime :=
  ramificationIdx_of_not_isPrime

Depends on / 依赖: dif_neg
-/
theorem ramificationIdx_of_not_isPrime (hq : ¬ q.IsPrime) : q.ramificationIdx R = 0 :=
  dif_neg hq

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_of_not_isPrime :=
  ramificationIdx_of_not_isPrime

/--
theorem `ramificationIdx_pos` / 定理 `ramificationIdx_pos`

English:
theorem ramificationIdx_pos
  given: [q.IsPrime] [Module.Finite R S]
  statement: 0 < q.ramificationIdx R
  proof: by
  let p := q.under R
  let Sq := Localization.AtPrime q
  rw [ramificationIdx_def]
  apply ENat.toNat_pos
  · rw [← pos_iff_ne_zero, Module.length_pos_iff, Submodule.Quotient.nontrivial_iff,
      IsScalarTower.algebraMap_eq R S, ← map_map, ← lt_top_iff_ne_top]
    grw [map_mono map_comap_le, Localization.AtPrime.map_eq_maximalIdeal]
    exact (IsLocalRing.maximalIdeal.isMaximal _).lt_top
  · let r := PrimeSpectrum.primesOverOrderIsoFiber R S p (primesOver.mk p q)
    have : q = r.1.comap Algebra.TensorProduct.includeRight := by
      rw [← PrimeSpectrum.coe_primesOverOrderIsoFiber_symm_apply]; rw [OrderIso.symm_apply_apply]
    let := Localization.AtPrime.algebraOfLiesOver p (r.1.comap Algebra.TensorProduct.includeRight)
    have : IsArtinianRing (Sq ⧸ map (algebraMap R Sq) p) := by
      convert (Fiber.localizationAlgEquivQuotient p r.1).toRingEquiv.isArtinianRing
    rwa [Module.length_eq_of_surjective (R := Sq ⧸ p.map (algebraMap R Sq)) Quotient.mk_surjective,
      Module.length_ne_top_iff, ← isArtinianRing_iff_isFiniteLength]

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_pos := ramificationIdx_pos

中文:
定理 ramificationIdx_pos
  条件: [q.是素] [模.有限 R S]
  结论: 0 < q.ramificationIdx R
  证明: by
  let p := q.under R
  let Sq := Localization.AtPrime q
  rw [ramificationIdx_def]
  apply ENat.toNat_pos
  · rw [← pos_iff_ne_zero, Module.length_pos_iff, Submodule.Quotient.nontrivial_iff,
      IsScalarTower.algebraMap_eq R S, ← map_map, ← lt_top_iff_ne_top]
    grw [map_mono map_comap_le, Localization.AtPrime.map_eq_maximalIdeal]
    exact (IsLocalRing.maximalIdeal.isMaximal _).lt_top
  · let r := PrimeSpectrum.primesOverOrderIsoFiber R S p (primesOver.mk p q)
    have : q = r.1.comap Algebra.TensorProduct.includeRight := by
      rw [← PrimeSpectrum.coe_primesOverOrderIsoFiber_symm_apply]; rw [OrderIso.symm_apply_apply]
    let := Localization.AtPrime.algebraOfLiesOver p (r.1.comap Algebra.TensorProduct.includeRight)
    have : IsArtinianRing (Sq ⧸ map (algebraMap R Sq) p) := by
      convert (Fiber.localizationAlgEquivQuotient p r.1).toRingEquiv.isArtinianRing
    rwa [Module.length_eq_of_surjective (R := Sq ⧸ p.map (algebraMap R Sq)) Quotient.mk_surjective,
      Module.length_ne_top_iff, ← isArtinianRing_iff_isFiniteLength]

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_pos := ramificationIdx_pos

Depends on / 依赖: Algebra, Algebra.TensorProduct.includeRigh, AtPrime, ENat.toNat_pos, IsLocalRing, IsLocalRing.maximalIdeal.isMaximal, IsScalarTower, IsScalarTower.algebraMap_eq, Localization, Localization.AtPrime, Localization.AtPrime.map_eq_maximalIdeal, Module, Module.length_pos_iff, PrimeSpectrum, PrimeSpectrum.primesOverOrderIsoFiber, Quotient, Submodule, Submodule.Quotient.nontrivial_iff, TensorProduct, algebraMap_eq
-/
theorem ramificationIdx_pos [q.IsPrime] [Module.Finite R S] : 0 < q.ramificationIdx R := by
  let p := q.under R
  let Sq := Localization.AtPrime q
  rw [ramificationIdx_def]
  apply ENat.toNat_pos
  · rw [← pos_iff_ne_zero, Module.length_pos_iff, Submodule.Quotient.nontrivial_iff,
      IsScalarTower.algebraMap_eq R S, ← map_map, ← lt_top_iff_ne_top]
    grw [map_mono map_comap_le, Localization.AtPrime.map_eq_maximalIdeal]
    exact (IsLocalRing.maximalIdeal.isMaximal _).lt_top
  · let r := PrimeSpectrum.primesOverOrderIsoFiber R S p (primesOver.mk p q)
    have : q = r.1.comap Algebra.TensorProduct.includeRight := by
      rw [← PrimeSpectrum.coe_primesOverOrderIsoFiber_symm_apply]; rw [OrderIso.symm_apply_apply]
    let := Localization.AtPrime.algebraOfLiesOver p (r.1.comap Algebra.TensorProduct.includeRight)
    have : IsArtinianRing (Sq ⧸ map (algebraMap R Sq) p) := by
      convert (Fiber.localizationAlgEquivQuotient p r.1).toRingEquiv.isArtinianRing
    rwa [Module.length_eq_of_surjective (R := Sq ⧸ p.map (algebraMap R Sq)) Quotient.mk_surjective,
      Module.length_ne_top_iff, ← isArtinianRing_iff_isFiniteLength]

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_pos := ramificationIdx_pos

/--
theorem `ramificationIdx_eq_one` / 定理 `ramificationIdx_eq_one`

English:
theorem ramificationIdx_eq_one
  statement: [q.IsPrime] [Algebra.EssFiniteType R S]
  proof: by
  let p := q.under R
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime q
  let : Algebra Rp Sq := Localization.AtPrime.algebraOfLiesOver p q
  have : Algebra.EssFiniteType Rp Sq := Algebra.EssFiniteType.of_comp R Rp Sq
  rw [ramificationIdx_def]; rw [ENat.toNat_eq_iff_eq_natCast]; rw [Nat.cast_one]; rw [Module.length_eq_one_iff]; rw [isSimpleModule_iff_isCoatom]; rw [← Ideal.isMaximal_def]; rw [IsLocalRing.isMaximal_iff]; rw [IsScalarTower.algebraMap_eq R Rp Sq]; rw [← map_map]; rw [Localization.AtPrime.map_eq_maximalIdeal]
  exact Algebra.FormallyUnramified.map_maximalIdeal

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_eq_one := ramificationIdx_eq_one

中文:
定理 ramificationIdx_eq_one
  结论: [q.是素] [代数.EssFiniteType R S]
  证明: by
  let p := q.under R
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime q
  let : Algebra Rp Sq := Localization.AtPrime.algebraOfLiesOver p q
  have : Algebra.EssFiniteType Rp Sq := Algebra.EssFiniteType.of_comp R Rp Sq
  rw [ramificationIdx_def]; rw [ENat.toNat_eq_iff_eq_natCast]; rw [Nat.cast_one]; rw [Module.length_eq_one_iff]; rw [isSimpleModule_iff_isCoatom]; rw [← Ideal.isMaximal_def]; rw [IsLocalRing.isMaximal_iff]; rw [IsScalarTower.algebraMap_eq R Rp Sq]; rw [← map_map]; rw [Localization.AtPrime.map_eq_maximalIdeal]
  exact Algebra.FormallyUnramified.map_maximalIdeal

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_eq_one := ramificationIdx_eq_one

Depends on / 依赖: Algebra, Algebra.EssFiniteType, Algebra.EssFiniteType.of_comp, AtPrime, ENat.toNat_eq_iff_eq_natCast, EssFiniteType, Ideal.isMaximal_def, IsLocalRing, IsLocalRing.isMaximal_iff, IsScalarTower, IsScalarTower.algebraMap_eq, Localization, Localization.AtPrime, Localization.AtPrime.algebraOfLiesOver, Module, Module.length_eq_one_iff, Nat.cast_one, algebraMap_eq, algebraOfLiesOver, cast_one
-/
theorem ramificationIdx_eq_one [q.IsPrime] [Algebra.EssFiniteType R S]
    [Algebra.IsUnramifiedAt R q] : q.ramificationIdx R = 1 := by
  let p := q.under R
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime q
  let : Algebra Rp Sq := Localization.AtPrime.algebraOfLiesOver p q
  have : Algebra.EssFiniteType Rp Sq := Algebra.EssFiniteType.of_comp R Rp Sq
  rw [ramificationIdx_def]; rw [ENat.toNat_eq_iff_eq_natCast]; rw [Nat.cast_one]; rw [Module.length_eq_one_iff]; rw [isSimpleModule_iff_isCoatom]; rw [← Ideal.isMaximal_def]; rw [IsLocalRing.isMaximal_iff]; rw [IsScalarTower.algebraMap_eq R Rp Sq]; rw [← map_map]; rw [Localization.AtPrime.map_eq_maximalIdeal]
  exact Algebra.FormallyUnramified.map_maximalIdeal

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_eq_one := ramificationIdx_eq_one

variable {q R} in
/--
theorem `ramificationIdx_eq_one_iff` / 定理 `ramificationIdx_eq_one_iff`

English:
theorem ramificationIdx_eq_one_iff
  statement: [q.IsPrime] [Algebra.EssFiniteType R S]
  proof: by
  refine ⟨fun h => ?_, fun _ => ramificationIdx_eq_one q R⟩
  rw [ramificationIdx_def]; rw [ENat.toNat_eq_iff_eq_natCast]; rw [Nat.cast_one]; rw [Module.length_eq_one_iff]; rw [isSimpleModule_iff_isCoatom]; rw [← Ideal.isMaximal_def]; rw [IsLocalRing.isMaximal_iff] at h
  let p := q.under R
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime q
  let := Localization.AtPrime.algebraOfLiesOver p q
  have := Algebra.EssFiniteType.of_comp R Rp Sq
  suffices Algebra.FormallyUnramified Rp Sq from Algebra.FormallyUnramified.comp R Rp Sq
  rw [Algebra.FormallyUnramified.iff_map_maximalIdeal_eq]; rw [← Localization.AtPrime.map_eq_maximalIdeal]; rw [map_map]; rw [← IsScalarTower.algebraMap_eq]
  exact ⟨Algebra.IsAlgebraic.isSeparable_of_perfectField, h⟩

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_eq_one_iff :=
  ramificationIdx_eq_one_iff

中文:
定理 ramificationIdx_eq_one_iff
  结论: [q.是素] [代数.EssFiniteType R S]
  证明: by
  refine ⟨fun h => ?_, fun _ => ramificationIdx_eq_one q R⟩
  rw [ramificationIdx_def]; rw [ENat.toNat_eq_iff_eq_natCast]; rw [Nat.cast_one]; rw [Module.length_eq_one_iff]; rw [isSimpleModule_iff_isCoatom]; rw [← Ideal.isMaximal_def]; rw [IsLocalRing.isMaximal_iff] at h
  let p := q.under R
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime q
  let := Localization.AtPrime.algebraOfLiesOver p q
  have := Algebra.EssFiniteType.of_comp R Rp Sq
  suffices Algebra.FormallyUnramified Rp Sq from Algebra.FormallyUnramified.comp R Rp Sq
  rw [Algebra.FormallyUnramified.iff_map_maximalIdeal_eq]; rw [← Localization.AtPrime.map_eq_maximalIdeal]; rw [map_map]; rw [← IsScalarTower.algebraMap_eq]
  exact ⟨Algebra.IsAlgebraic.isSeparable_of_perfectField, h⟩

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_eq_one_iff :=
  ramificationIdx_eq_one_iff

Depends on / 依赖: Algebra, Algebra.EssFiniteType.of_comp, Algebra.FormallyUnramified, AtPrime, ENat.toNat_eq_iff_eq_natCast, EssFiniteType, FormallyUnramified, Ideal.isMaximal_def, IsLocalRing, IsLocalRing.isMaximal_iff, Localization, Localization.AtPrime, Localization.AtPrime.algebraOfLiesOver, Module, Module.length_eq_one_iff, Nat.cast_one, algebraOfLiesOver, cast_one, isMaximal_def, isMaximal_iff
-/
theorem ramificationIdx_eq_one_iff [q.IsPrime] [Algebra.EssFiniteType R S]
    [Algebra.IsIntegral R S] [PerfectField (q.under R).ResidueField] :
    q.ramificationIdx R = 1 ↔ Algebra.IsUnramifiedAt R q := by
  refine ⟨fun h => ?_, fun _ => ramificationIdx_eq_one q R⟩
  rw [ramificationIdx_def]; rw [ENat.toNat_eq_iff_eq_natCast]; rw [Nat.cast_one]; rw [Module.length_eq_one_iff]; rw [isSimpleModule_iff_isCoatom]; rw [← Ideal.isMaximal_def]; rw [IsLocalRing.isMaximal_iff] at h
  let p := q.under R
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime q
  let := Localization.AtPrime.algebraOfLiesOver p q
  have := Algebra.EssFiniteType.of_comp R Rp Sq
  suffices Algebra.FormallyUnramified Rp Sq from Algebra.FormallyUnramified.comp R Rp Sq
  rw [Algebra.FormallyUnramified.iff_map_maximalIdeal_eq]; rw [← Localization.AtPrime.map_eq_maximalIdeal]; rw [map_map]; rw [← IsScalarTower.algebraMap_eq]
  exact ⟨Algebra.IsAlgebraic.isSeparable_of_perfectField, h⟩

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_eq_one_iff :=
  ramificationIdx_eq_one_iff

end

section

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  (p : Ideal R) (q : Ideal S) (r : Ideal T)

/--
theorem `ramificationIdx_eq` / 定理 `ramificationIdx_eq`

English:
theorem ramificationIdx_eq
  given: [q.LiesOver p] [q.IsPrime]
  proof: Localization.AtPrime q
    q.ramificationIdx R = (Module.length Sq (Sq ⧸ p.map (algebraMap R Sq))).toNat := by
  rw [ramificationIdx_def]; rw [over_def q p]

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_eq := ramificationIdx_eq

中文:
定理 ramificationIdx_eq
  条件: [q.LiesOver p] [q.是素]
  证明: Localization.AtPrime q
    q.ramificationIdx R = (Module.length Sq (Sq ⧸ p.map (algebraMap R Sq))).toNat := by
  rw [ramificationIdx_def]; rw [over_def q p]

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_eq := ramificationIdx_eq

Depends on / 依赖: AtPrime, Localization, Localization.AtPrime
-/
theorem ramificationIdx_eq [q.LiesOver p] [q.IsPrime] :
    letI Sq := Localization.AtPrime q
    q.ramificationIdx R = (Module.length Sq (Sq ⧸ p.map (algebraMap R Sq))).toNat := by
  rw [ramificationIdx_def]; rw [over_def q p]

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_eq := ramificationIdx_eq

open Localization IsLocalization.AtPrime in
/--
theorem `ramificationIdx'_eq_ramificationIdx'` / 定理 `ramificationIdx'_eq_ramificationIdx'`

English:
theorem ramificationIdx'_eq_ramificationIdx'
  statement: [IsDedekindDomain S]
  proof: by
  have hq' : q != ⊥ := ne_bot_of_le_ne_bot hpS (map_le_of_le_comap (q.over_def p).le)
  have : q.IsMaximal := hq.isMaximal hq'
  obtain ⟨I, hqI, h⟩ := Ideal.eq_prime_pow_mul_coprime hpS q
  replace hqI : ¬ I <= q := by
    contrapose! hqI
    rw [sup_of_le_left hqI]
    exact hq.ne_top
  rw [← IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hpS hq hq'] at h
  apply_fun (map (algebraMap S (Localization.AtPrime q))) at h
  rw [map_map]; rw [← IsScalarTower.algebraMap_eq]; rw [Ideal.map_mul]; rw [Ideal.map_pow]; rw [map_eq_top_of_not_le (Localization.AtPrime q) hqI]; rw [mul_top]; rw [AtPrime.map_eq_maximalIdeal] at h
  have hSq := isDiscreteValuationRing_of_dedekind_domain S hq' (Localization.AtPrime q)
  rw [ramificationIdx_eq p q]; rw [h]; rw [hSq.length_quotient_pow_maximalIdeal]; rw [ENat.toNat_natCast]

@[deprecated (since := "2026-07-01")] alias ramificationIdx_eq_ramificationIdx'' :=
  ramificationIdx'_eq_ramificationIdx'

中文:
定理 ramificationIdx'_eq_ramificationIdx'
  结论: [是Dedekind整环 S]
  证明: by
  have hq' : q != ⊥ := ne_bot_of_le_ne_bot hpS (map_le_of_le_comap (q.over_def p).le)
  have : q.IsMaximal := hq.isMaximal hq'
  obtain ⟨I, hqI, h⟩ := Ideal.eq_prime_pow_mul_coprime hpS q
  replace hqI : ¬ I <= q := by
    contrapose! hqI
    rw [sup_of_le_left hqI]
    exact hq.ne_top
  rw [← IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hpS hq hq'] at h
  apply_fun (map (algebraMap S (Localization.AtPrime q))) at h
  rw [map_map]; rw [← IsScalarTower.algebraMap_eq]; rw [Ideal.map_mul]; rw [Ideal.map_pow]; rw [map_eq_top_of_not_le (Localization.AtPrime q) hqI]; rw [mul_top]; rw [AtPrime.map_eq_maximalIdeal] at h
  have hSq := isDiscreteValuationRing_of_dedekind_domain S hq' (Localization.AtPrime q)
  rw [ramificationIdx_eq p q]; rw [h]; rw [hSq.length_quotient_pow_maximalIdeal]; rw [ENat.toNat_natCast]

@[deprecated (since := "2026-07-01")] alias ramificationIdx_eq_ramificationIdx'' :=
  ramificationIdx'_eq_ramificationIdx'
-/
theorem ramificationIdx'_eq_ramificationIdx' [IsDedekindDomain S]
    [q.LiesOver p] [hq : q.IsPrime] (hpS : p.map (algebraMap R S) != ⊥) :
    p.ramificationIdx' q = q.ramificationIdx R := by
  have hq' : q != ⊥ := ne_bot_of_le_ne_bot hpS (map_le_of_le_comap (q.over_def p).le)
  have : q.IsMaximal := hq.isMaximal hq'
  obtain ⟨I, hqI, h⟩ := Ideal.eq_prime_pow_mul_coprime hpS q
  replace hqI : ¬ I <= q := by
    contrapose! hqI
    rw [sup_of_le_left hqI]
    exact hq.ne_top
  rw [← IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hpS hq hq'] at h
  apply_fun (map (algebraMap S (Localization.AtPrime q))) at h
  rw [map_map]; rw [← IsScalarTower.algebraMap_eq]; rw [Ideal.map_mul]; rw [Ideal.map_pow]; rw [map_eq_top_of_not_le (Localization.AtPrime q) hqI]; rw [mul_top]; rw [AtPrime.map_eq_maximalIdeal] at h
  have hSq := isDiscreteValuationRing_of_dedekind_domain S hq' (Localization.AtPrime q)
  rw [ramificationIdx_eq p q]; rw [h]; rw [hSq.length_quotient_pow_maximalIdeal]; rw [ENat.toNat_natCast]

@[deprecated (since := "2026-07-01")] alias ramificationIdx_eq_ramificationIdx'' :=
  ramificationIdx'_eq_ramificationIdx'

/--
theorem `ramificationIdx'_eq_ramificationIdx` / 定理 `ramificationIdx'_eq_ramificationIdx`

English:
theorem ramificationIdx'_eq_ramificationIdx
  statement: [IsDomain R] [IsDedekindDomain S]
  proof: by
  have hpS : p.map (algebraMap R S) != ⊥ := map_ne_bot_of_ne_bot hp
  exact ramificationIdx'_eq_ramificationIdx' p q hpS

@[deprecated (since := "2026-07-01")] alias ramificationIdx_eq_ramificationIdx' :=
  ramificationIdx'_eq_ramificationIdx

中文:
定理 ramificationIdx'_eq_ramificationIdx
  结论: [是整环 R] [是Dedekind整环 S]
  证明: by
  have hpS : p.map (algebraMap R S) != ⊥ := map_ne_bot_of_ne_bot hp
  exact ramificationIdx'_eq_ramificationIdx' p q hpS

@[deprecated (since := "2026-07-01")] alias ramificationIdx_eq_ramificationIdx' :=
  ramificationIdx'_eq_ramificationIdx
-/
theorem ramificationIdx'_eq_ramificationIdx [IsDomain R] [IsDedekindDomain S]
    [Module.IsTorsionFree R S] [q.LiesOver p] [hq : q.IsPrime] (hp : p != ⊥) :
    p.ramificationIdx' q = q.ramificationIdx R := by
  have hpS : p.map (algebraMap R S) != ⊥ := map_ne_bot_of_ne_bot hp
  exact ramificationIdx'_eq_ramificationIdx' p q hpS

@[deprecated (since := "2026-07-01")] alias ramificationIdx_eq_ramificationIdx' :=
  ramificationIdx'_eq_ramificationIdx

namespace IsDedekindDomain

open UniqueFactorizationMonoid

/--
theorem `ramificationIdx_eq_factors_count` / 定理 `ramificationIdx_eq_factors_count`

English:
theorem ramificationIdx_eq_factors_count
  statement: [IsDedekindDomain S]
  proof: by
  by_cases hq : q.IsPrime; swap
  · rw [ramificationIdx_of_not_isPrime q R hq, eq_comm, Multiset.count_eq_zero]
    contrapose! hq
    exact isPrime_of_prime (prime_of_factor q hq)
  have hq0 : q != ⊥ := ne_bot_of_le_ne_bot hp0 (map_le_of_le_comap (q.over_def p).le)
  rw [← ramificationIdx'_eq_ramificationIdx' p q hp0]; rw [ramificationIdx'_eq_factors_count hp0 ‹_› hq0]

中文:
定理 ramificationIdx_eq_factors_count
  结论: [是Dedekind整环 S]
  证明: by
  by_cases hq : q.IsPrime; swap
  · rw [ramificationIdx_of_not_isPrime q R hq, eq_comm, Multiset.count_eq_zero]
    contrapose! hq
    exact isPrime_of_prime (prime_of_factor q hq)
  have hq0 : q != ⊥ := ne_bot_of_le_ne_bot hp0 (map_le_of_le_comap (q.over_def p).le)
  rw [← ramificationIdx'_eq_ramificationIdx' p q hp0]; rw [ramificationIdx'_eq_factors_count hp0 ‹_› hq0]

Depends on / 依赖: IsPrime, Multiset, Multiset.count_eq_zero, _eq_factors_count, _eq_ramificationIdx, contrapose, count_eq_zero, eq_comm, isPrime_of_prime, map_le_of_le_comap, ne_bot_of_le_ne_bot, over_def, prime_of_factor, q.IsPrime, q.over_def, ramificationIdx, ramificationIdx_of_not_isPrime
-/
theorem ramificationIdx_eq_factors_count [IsDedekindDomain S]
    [q.LiesOver p] (hp0 : p.map (algebraMap R S) != ⊥) :
    q.ramificationIdx R = (factors (p.map (algebraMap R S))).count q := by
  by_cases hq : q.IsPrime; swap
  · rw [ramificationIdx_of_not_isPrime q R hq, eq_comm, Multiset.count_eq_zero]
    contrapose! hq
    exact isPrime_of_prime (prime_of_factor q hq)
  have hq0 : q != ⊥ := ne_bot_of_le_ne_bot hp0 (map_le_of_le_comap (q.over_def p).le)
  rw [← ramificationIdx'_eq_ramificationIdx' p q hp0]; rw [ramificationIdx'_eq_factors_count hp0 ‹_› hq0]

open UniqueFactorizationMonoid in
/--
theorem `ramificationIdx_eq_normalizedFactors_count` / 定理 `ramificationIdx_eq_normalizedFactors_count`

English:
theorem ramificationIdx_eq_normalizedFactors_count
  statement: [IsDedekindDomain S]
  proof: by
  rw [← factors_eq_normalizedFactors]; rw [← ramificationIdx_eq_factors_count p q hp0]

中文:
定理 ramificationIdx_eq_normalizedFactors_count
  结论: [是Dedekind整环 S]
  证明: by
  rw [← factors_eq_normalizedFactors]; rw [← ramificationIdx_eq_factors_count p q hp0]

Depends on / 依赖: factors_eq_normalizedFactors, ramificationIdx_eq_factors_count
-/
theorem ramificationIdx_eq_normalizedFactors_count [IsDedekindDomain S]
    [q.LiesOver p] (hp0 : p.map (algebraMap R S) != ⊥) :
    q.ramificationIdx R = (normalizedFactors (p.map (algebraMap R S))).count q := by
  rw [← factors_eq_normalizedFactors]; rw [← ramificationIdx_eq_factors_count p q hp0]

open UniqueFactorizationMonoid in
/--
theorem `ramificationIdx_eq_multiplicity` / 定理 `ramificationIdx_eq_multiplicity`

English:
theorem ramificationIdx_eq_multiplicity
  statement: [IsDedekindDomain S]
  proof: by
  have hq : q != ⊥ := ne_bot_of_le_ne_bot hp (map_le_of_le_comap (q.over_def p).le)
  rw [ramificationIdx_eq_normalizedFactors_count p q hp]; rw [multiplicity_eq_of_emultiplicity_eq_some (emultiplicity_eq_count_normalizedFactors
      (prime_of_isPrime hq inferInstance).irreducible hp)]; rw [normalize_eq]

中文:
定理 ramificationIdx_eq_multiplicity
  结论: [是Dedekind整环 S]
  证明: by
  have hq : q != ⊥ := ne_bot_of_le_ne_bot hp (map_le_of_le_comap (q.over_def p).le)
  rw [ramificationIdx_eq_normalizedFactors_count p q hp]; rw [multiplicity_eq_of_emultiplicity_eq_some (emultiplicity_eq_count_normalizedFactors
      (prime_of_isPrime hq inferInstance).irreducible hp)]; rw [normalize_eq]

Depends on / 依赖: emultiplicity_eq_count_normalizedFactors, irreducible, map_le_of_le_comap, multiplicity_eq_of_emultiplicity_eq_some, ne_bot_of_le_ne_bot, normalize_eq, over_def, prime_of_isPrime, q.over_def, ramificationIdx_eq_normalizedFactors_count
-/
theorem ramificationIdx_eq_multiplicity [IsDedekindDomain S]
    [q.IsPrime] [q.LiesOver p] (hp : p.map (algebraMap R S) != ⊥) :
    q.ramificationIdx R = multiplicity q (p.map (algebraMap R S)) := by
  have hq : q != ⊥ := ne_bot_of_le_ne_bot hp (map_le_of_le_comap (q.over_def p).le)
  rw [ramificationIdx_eq_normalizedFactors_count p q hp]; rw [multiplicity_eq_of_emultiplicity_eq_some (emultiplicity_eq_count_normalizedFactors
      (prime_of_isPrime hq inferInstance).irreducible hp)]; rw [normalize_eq]

end IsDedekindDomain

/--
theorem `ramificationIdx_tower'` / 定理 `ramificationIdx_tower'`

English:
theorem ramificationIdx_tower'
  statement: [q.IsPrime] [r.IsPrime] [r.LiesOver q]
  proof: by
  have : q.LiesOver (r.under R) := LiesOver.tower_bot r q (r.under R)
  let f := (Ideal.quotientEquivAlgOfEq (Localization.AtPrime r)
    (by rw [map_map, ← IsScalarTower.algebraMap_eq])).trans
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (Localization.AtPrime r)
        ((r.under R).map (algebraMap R (Localization.AtPrime q))))
  rw [ramificationIdx_def]; rw [ramificationIdx_eq (r.under R)]; rw [ramificationIdx_eq q]; rw [f.toLinearEquiv.length_eq]; rw [IsLocalRing.length_baseChange]; rw [ENat.toNat_mul]; rw [← Localization.AtPrime.map_eq_maximalIdeal]; rw [map_map]; rw [← IsScalarTower.algebraMap_eq]

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_tower' := ramificationIdx_tower'

中文:
定理 ramificationIdx_tower'
  结论: [q.是素] [r.是素] [r.LiesOver q]
  证明: by
  have : q.LiesOver (r.under R) := LiesOver.tower_bot r q (r.under R)
  let f := (Ideal.quotientEquivAlgOfEq (Localization.AtPrime r)
    (by rw [map_map, ← IsScalarTower.algebraMap_eq])).trans
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (Localization.AtPrime r)
        ((r.under R).map (algebraMap R (Localization.AtPrime q))))
  rw [ramificationIdx_def]; rw [ramificationIdx_eq (r.under R)]; rw [ramificationIdx_eq q]; rw [f.toLinearEquiv.length_eq]; rw [IsLocalRing.length_baseChange]; rw [ENat.toNat_mul]; rw [← Localization.AtPrime.map_eq_maximalIdeal]; rw [map_map]; rw [← IsScalarTower.algebraMap_eq]

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_tower' := ramificationIdx_tower'

Depends on / 依赖: Algebra, Algebra.TensorProduct.quotIdealMapEquivTensorQuot, AtPrime, ENat.toNat_mul, Ideal.quotientEquivAlgOfEq, IsLocalRing, IsLocalRing.length_baseChange, IsScalarTower, IsScalarTower.algebraMap_eq, LiesOver, LiesOver.tower_bot, Localization, Localization.AtPrime, TensorProduct, algebraMap, algebraMap_eq, f.toLinearEquiv.length_eq, length_baseChange, length_eq, map_map
-/
theorem ramificationIdx_tower' [q.IsPrime] [r.IsPrime] [r.LiesOver q]
    [Algebra (Localization.AtPrime q) (Localization.AtPrime r)]
    [Localization.AtPrime.IsLiesOverAlgebra q r]
    [Module.Flat (Localization.AtPrime q) (Localization.AtPrime r)] :
    r.ramificationIdx R = q.ramificationIdx R * r.ramificationIdx S := by
  have : q.LiesOver (r.under R) := LiesOver.tower_bot r q (r.under R)
  let f := (Ideal.quotientEquivAlgOfEq (Localization.AtPrime r)
    (by rw [map_map, ← IsScalarTower.algebraMap_eq])).trans
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (Localization.AtPrime r)
        ((r.under R).map (algebraMap R (Localization.AtPrime q))))
  rw [ramificationIdx_def]; rw [ramificationIdx_eq (r.under R)]; rw [ramificationIdx_eq q]; rw [f.toLinearEquiv.length_eq]; rw [IsLocalRing.length_baseChange]; rw [ENat.toNat_mul]; rw [← Localization.AtPrime.map_eq_maximalIdeal]; rw [map_map]; rw [← IsScalarTower.algebraMap_eq]

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_tower' := ramificationIdx_tower'

/--
theorem `ramificationIdx_tower` / 定理 `ramificationIdx_tower`

English:
theorem ramificationIdx_tower
  given: [r.LiesOver q] [Module.Flat S T]
  proof: by
  by_cases hr : r.IsPrime
  · have : q.IsPrime := isPrime_of_liesOver r q
    let := Localization.AtPrime.algebraOfLiesOver q r
    apply ramificationIdx_tower'
  · rw [ramificationIdx_of_not_isPrime r R hr, ramificationIdx_of_not_isPrime r S hr, mul_zero]

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_tower := ramificationIdx_tower

中文:
定理 ramificationIdx_tower
  条件: [r.LiesOver q] [模.平坦 S T]
  证明: by
  by_cases hr : r.IsPrime
  · have : q.IsPrime := isPrime_of_liesOver r q
    let := Localization.AtPrime.algebraOfLiesOver q r
    apply ramificationIdx_tower'
  · rw [ramificationIdx_of_not_isPrime r R hr, ramificationIdx_of_not_isPrime r S hr, mul_zero]

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_tower := ramificationIdx_tower

Depends on / 依赖: AtPrime, IsPrime, Localization, Localization.AtPrime.algebraOfLiesOver, algebraOfLiesOver, isPrime_of_liesOver, mul_zero, q.IsPrime, r.IsPrime, ramificationIdx_of_not_isPrime, ramificationIdx_tower
-/
theorem ramificationIdx_tower [r.LiesOver q] [Module.Flat S T] :
    r.ramificationIdx R = q.ramificationIdx R * r.ramificationIdx S := by
  by_cases hr : r.IsPrime
  · have : q.IsPrime := isPrime_of_liesOver r q
    let := Localization.AtPrime.algebraOfLiesOver q r
    apply ramificationIdx_tower'
  · rw [ramificationIdx_of_not_isPrime r R hr, ramificationIdx_of_not_isPrime r S hr, mul_zero]

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_tower := ramificationIdx_tower

/--
theorem `ramificationIdx_below_dvd` / 定理 `ramificationIdx_below_dvd`

English:
theorem ramificationIdx_below_dvd
  given: [r.LiesOver q] [Module.Flat S T]
  proof: by
  use r.ramificationIdx S
  rw [← ramificationIdx_tower]

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_below_dvd := ramificationIdx_below_dvd

中文:
定理 ramificationIdx_below_dvd
  条件: [r.LiesOver q] [模.平坦 S T]
  证明: by
  use r.ramificationIdx S
  rw [← ramificationIdx_tower]

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_below_dvd := ramificationIdx_below_dvd

Depends on / 依赖: r.ramificationIdx, ramificationIdx, ramificationIdx_tower
-/
theorem ramificationIdx_below_dvd [r.LiesOver q] [Module.Flat S T] :
    q.ramificationIdx R ∣ r.ramificationIdx R := by
  use r.ramificationIdx S
  rw [← ramificationIdx_tower]

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_below_dvd := ramificationIdx_below_dvd

/--
theorem `ramificationIdx_above_dvd` / 定理 `ramificationIdx_above_dvd`

English:
theorem ramificationIdx_above_dvd
  given: [r.LiesOver q] [Module.Flat S T]
  proof: by
  use q.ramificationIdx R
  rw [mul_comm]; rw [← ramificationIdx_tower]

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_above_dvd := ramificationIdx_above_dvd

中文:
定理 ramificationIdx_above_dvd
  条件: [r.LiesOver q] [模.平坦 S T]
  证明: by
  use q.ramificationIdx R
  rw [mul_comm]; rw [← ramificationIdx_tower]

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_above_dvd := ramificationIdx_above_dvd

Depends on / 依赖: mul_comm, q.ramificationIdx, ramificationIdx, ramificationIdx_tower
-/
theorem ramificationIdx_above_dvd [r.LiesOver q] [Module.Flat S T] :
    r.ramificationIdx S ∣ r.ramificationIdx R := by
  use q.ramificationIdx R
  rw [mul_comm]; rw [← ramificationIdx_tower]

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_above_dvd := ramificationIdx_above_dvd

/--
theorem `ramificationIdx_below_le` / 定理 `ramificationIdx_below_le`

English:
theorem ramificationIdx_below_le
  given: [r.IsPrime] [r.LiesOver q] [Module.Finite R T] [Module.Flat S T]
  proof: Nat.le_of_dvd (r.ramificationIdx_pos R) (q.ramificationIdx_below_dvd r)

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_below_le :=
  ramificationIdx_below_le

中文:
定理 ramificationIdx_below_le
  条件: [r.是素] [r.LiesOver q] [模.有限 R T] [模.平坦 S T]
  证明: Nat.le_of_dvd (r.ramificationIdx_pos R) (q.ramificationIdx_below_dvd r)

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_below_le :=
  ramificationIdx_below_le

Depends on / 依赖: Nat.le_of_dvd, le_of_dvd, q.ramificationIdx_below_dvd, r.ramificationIdx_pos, ramificationIdx_below_dvd, ramificationIdx_pos
-/
theorem ramificationIdx_below_le [r.IsPrime] [r.LiesOver q] [Module.Finite R T] [Module.Flat S T] :
    q.ramificationIdx R <= r.ramificationIdx R :=
  Nat.le_of_dvd (r.ramificationIdx_pos R) (q.ramificationIdx_below_dvd r)

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_below_le :=
  ramificationIdx_below_le

/--
theorem `ramificationIdx_above_le` / 定理 `ramificationIdx_above_le`

English:
theorem ramificationIdx_above_le
  given: [r.IsPrime] [r.LiesOver q] [Module.Finite R T] [Module.Flat S T]
  proof: Nat.le_of_dvd (r.ramificationIdx_pos R) (q.ramificationIdx_above_dvd r)

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_above_le := ramificationIdx_above_le

中文:
定理 ramificationIdx_above_le
  条件: [r.是素] [r.LiesOver q] [模.有限 R T] [模.平坦 S T]
  证明: Nat.le_of_dvd (r.ramificationIdx_pos R) (q.ramificationIdx_above_dvd r)

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_above_le := ramificationIdx_above_le

Depends on / 依赖: Nat.le_of_dvd, le_of_dvd, q.ramificationIdx_above_dvd, r.ramificationIdx_pos, ramificationIdx_above_dvd, ramificationIdx_pos
-/
theorem ramificationIdx_above_le [r.IsPrime] [r.LiesOver q] [Module.Finite R T] [Module.Flat S T] :
    r.ramificationIdx S <= r.ramificationIdx R :=
  Nat.le_of_dvd (r.ramificationIdx_pos R) (q.ramificationIdx_above_dvd r)

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_above_le := ramificationIdx_above_le

set_option backward.isDefEq.respectTransparency.types false in
variable (R) in
open Pointwise in
@[simp]
/--
theorem `ramificationIdx_smul` / 定理 `ramificationIdx_smul`

English:
theorem ramificationIdx_smul
  statement: {G : Type*} [Group G] [MulSemiringAction G S] [SMulCommClass G R S]
  proof: by
  by_cases hq : q.IsPrime; swap
  · rw [ramificationIdx_of_not_isPrime, ramificationIdx_of_not_isPrime] <;> simpa
  · let p := q.under R
    let f₀ := MulSemiringAction.toAlgAut G R S g
    have hg : g • q = q.map f₀ := q.pointwise_smul_def
    let Sq := Localization.AtPrime q
    let Sq' := Localization.AtPrime (q.map f₀)
    let f : Sq ≃ₐ[R] Sq' :=
      Localization.localAlgEquiv q (q.map f₀) f₀ (comap_map_of_bijective f₀ f₀.bijective).symm
    let : Algebra Sq Sq' := f.toRingHom.toAlgebra
    have : IsScalarTower R Sq Sq' := IsScalarTower.of_algHom f.toAlgHom
    let e : (Sq ⧸ p.map (algebraMap R Sq)) ≃ₐ[Sq] Sq' ⧸ p.map (algebraMap R Sq') :=
      Ideal.quotientEquivAlg _ _ (AlgEquiv.ofBijective (Algebra.ofId Sq Sq') f.bijective)
        (by rw [IsScalarTower.algebraMap_eq R Sq Sq', Ideal.map_map,
          ← AlgEquiv.toAlgHom_toRingHom, AlgEquiv.toAlgHom_ofBijective, Algebra.toRingHom_ofId])
    rw [hg]; rw [ramificationIdx_eq p q]; rw [ramificationIdx_eq p (q.map f₀)]; rw [e.toLinearEquiv.length_eq]; rw [Module.length_eq_of_surjective f.surjective]

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_smul := ramificationIdx_smul

中文:
定理 ramificationIdx_smul
  结论: {G : 类型} [群 G] [MulSemiring作用 G S] [标量交换类 G R S]
  证明: by
  by_cases hq : q.IsPrime; swap
  · rw [ramificationIdx_of_not_isPrime, ramificationIdx_of_not_isPrime] <;> simpa
  · let p := q.under R
    let f₀ := MulSemiringAction.toAlgAut G R S g
    have hg : g • q = q.map f₀ := q.pointwise_smul_def
    let Sq := Localization.AtPrime q
    let Sq' := Localization.AtPrime (q.map f₀)
    let f : Sq ≃ₐ[R] Sq' :=
      Localization.localAlgEquiv q (q.map f₀) f₀ (comap_map_of_bijective f₀ f₀.bijective).symm
    let : Algebra Sq Sq' := f.toRingHom.toAlgebra
    have : IsScalarTower R Sq Sq' := IsScalarTower.of_algHom f.toAlgHom
    let e : (Sq ⧸ p.map (algebraMap R Sq)) ≃ₐ[Sq] Sq' ⧸ p.map (algebraMap R Sq') :=
      Ideal.quotientEquivAlg _ _ (AlgEquiv.ofBijective (Algebra.ofId Sq Sq') f.bijective)
        (by rw [IsScalarTower.algebraMap_eq R Sq Sq', Ideal.map_map,
          ← AlgEquiv.toAlgHom_toRingHom, AlgEquiv.toAlgHom_ofBijective, Algebra.toRingHom_ofId])
    rw [hg]; rw [ramificationIdx_eq p q]; rw [ramificationIdx_eq p (q.map f₀)]; rw [e.toLinearEquiv.length_eq]; rw [Module.length_eq_of_surjective f.surjective]

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_smul := ramificationIdx_smul

Depends on / 依赖: Algebra, AtPrime, IsPrime, IsScalarTower, Localization, Localization.AtPrime, Localization.localAlgEquiv, MulSemiringAction, MulSemiringAction.toAlgAut, bijective, comap_map_of_bijective, f.toRingHom.toAlgebra, localAlgEquiv, pointwise_smul_def, q.IsPrime, q.map, q.pointwise_smul_def, q.under, ramificationIdx_of_not_isPrime, toAlgAut
-/
theorem ramificationIdx_smul {G : Type*} [Group G] [MulSemiringAction G S] [SMulCommClass G R S]
    (g : G) : (g • q).ramificationIdx R = q.ramificationIdx R := by
  by_cases hq : q.IsPrime; swap
  · rw [ramificationIdx_of_not_isPrime, ramificationIdx_of_not_isPrime] <;> simpa
  · let p := q.under R
    let f₀ := MulSemiringAction.toAlgAut G R S g
    have hg : g • q = q.map f₀ := q.pointwise_smul_def
    let Sq := Localization.AtPrime q
    let Sq' := Localization.AtPrime (q.map f₀)
    let f : Sq ≃ₐ[R] Sq' :=
      Localization.localAlgEquiv q (q.map f₀) f₀ (comap_map_of_bijective f₀ f₀.bijective).symm
    let : Algebra Sq Sq' := f.toRingHom.toAlgebra
    have : IsScalarTower R Sq Sq' := IsScalarTower.of_algHom f.toAlgHom
    let e : (Sq ⧸ p.map (algebraMap R Sq)) ≃ₐ[Sq] Sq' ⧸ p.map (algebraMap R Sq') :=
      Ideal.quotientEquivAlg _ _ (AlgEquiv.ofBijective (Algebra.ofId Sq Sq') f.bijective)
        (by rw [IsScalarTower.algebraMap_eq R Sq Sq', Ideal.map_map,
          ← AlgEquiv.toAlgHom_toRingHom, AlgEquiv.toAlgHom_ofBijective, Algebra.toRingHom_ofId])
    rw [hg]; rw [ramificationIdx_eq p q]; rw [ramificationIdx_eq p (q.map f₀)]; rw [e.toLinearEquiv.length_eq]; rw [Module.length_eq_of_surjective f.surjective]

@[deprecated (since := "2026-07-01")] alias ramificationIdx'_smul := ramificationIdx_smul

end

end Ideal
