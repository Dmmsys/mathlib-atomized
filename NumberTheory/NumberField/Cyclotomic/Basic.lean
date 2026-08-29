/-
Copyright (c) 2022 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
public import Mathlib.NumberTheory.Cyclotomic.Discriminant
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
public import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
public import Mathlib.RingTheory.Prime

/-!
# Ring of integers of cyclotomic fields

We gather results about cyclotomic extensions of `ℚ`. In particular, we compute the ring of
integers of a cyclotomic extension of `ℚ`.

## Main results
* `IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton`: if `K` is a cyclotomic
  extension of `ℚ`, then `adjoin ℤ {ζ}` is the integral closure of `ℤ` in `K`.
* `IsCyclotomicExtension.Rat.cyclotomicRing_isIntegralClosure`: the integral
  closure of `ℤ` inside `CyclotomicField n ℚ` is `CyclotomicRing n ℤ ℚ`.
* `IsCyclotomicExtension.Rat.discr` and related results: the absolute discriminant
  of cyclotomic fields.
-/

@[expose] public section

universe u

open Algebra IsCyclotomicExtension Polynomial NumberField

open scoped Cyclotomic Nat

variable {p k n : Nat} {K : Type u} [Field K] {ζ : K} [hp : Fact p.Prime]

namespace IsCyclotomicExtension.Rat

variable [CharZero K]

variable (k K) in
/--
theorem `finrank` / 定理 `finrank`

English:
theorem finrank
  given: [NeZero k] [IsCyclotomicExtension {k} Rat K]
  statement: Module.finrank Rat K = k.totient
  proof: IsCyclotomicExtension.finrank K Polynomial.cyclotomic.irreducible_rat (NeZero.pos _)

中文:
定理 finrank
  条件: [NeZero k] [IsCyclotomicExtension {k} Rat K]
  结论: Module.finrank Rat K = k.totient
  证明: IsCyclotomicExtension.finrank K Polynomial.cyclotomic.irreducible_rat (NeZero.pos _)

Depends on / 依赖: IsCyclotomicExtension, IsCyclotomicExtension.finrank, NeZero, NeZero.pos, Polynomial, Polynomial.cyclotomic.irreducible_rat, cyclotomic, finrank, irreducible_rat
-/
theorem finrank [NeZero k] [IsCyclotomicExtension {k} Rat K] : Module.finrank Rat K = k.totient :=
IsCyclotomicExtension.finrank K Polynomial.cyclotomic.irreducible_rat (NeZero.pos _)

/--
theorem `discr_prime_pow_ne_two'` / 定理 `discr_prime_pow_ne_two'`

English:
theorem discr_prime_pow_ne_two'
  statement: [IsCyclotomicExtension {p ^ (k + 1)} Rat K]
  proof: by
  rw [← discr_prime_pow_ne_two hζ (cyclotomic.irreducible_rat (NeZero.pos _)) hk]
  exact hζ.discr_zeta_eq_discr_zeta_sub_one.symm

中文:
定理 discr_prime_pow_ne_two'
  结论: [IsCyclotomicExtension {p ^ (k + 1)} Rat K]
  证明: by
  rw [← discr_prime_pow_ne_two hζ (cyclotomic.irreducible_rat (NeZero.pos _)) hk]
  exact hζ.discr_zeta_eq_discr_zeta_sub_one.symm

Depends on / 依赖: NeZero, NeZero.pos, cyclotomic, cyclotomic.irreducible_rat, discr_prime_pow_ne_two, discr_zeta_eq_discr_zeta_sub_one, discr_zeta_eq_discr_zeta_sub_one.symm, irreducible_rat
-/
theorem discr_prime_pow_ne_two' [IsCyclotomicExtension {p ^ (k + 1)} Rat K]
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) (hk : p ^ (k + 1) != 2) :
    discr Rat (hζ.subOnePowerBasis Rat).basis =
      (-1) ^ ((p ^ (k + 1)).totient / 2) * p ^ (p ^ k * ((p - 1) * (k + 1) - 1)) := by
  rw [← discr_prime_pow_ne_two hζ (cyclotomic.irreducible_rat (NeZero.pos _)) hk]
  exact hζ.discr_zeta_eq_discr_zeta_sub_one.symm

/--
theorem `discr_odd_prime'` / 定理 `discr_odd_prime'`

English:
theorem discr_odd_prime'
  given: [IsCyclotomicExtension {p} Rat K] (hζ : IsPrimitiveRoot ζ p) (hodd : p != 2)
  proof: by
  rw [← discr_odd_prime hζ (cyclotomic.irreducible_rat hp.out.pos) hodd]
  exact hζ.discr_zeta_eq_discr_zeta_sub_one.symm

中文:
定理 discr_odd_prime'
  条件: [IsCyclotomicExtension {p} Rat K] (hζ : IsPrimitiveRoot ζ p) (hodd : p != 2)
  证明: by
  rw [← discr_odd_prime hζ (cyclotomic.irreducible_rat hp.out.pos) hodd]
  exact hζ.discr_zeta_eq_discr_zeta_sub_one.symm

Depends on / 依赖: cyclotomic, cyclotomic.irreducible_rat, discr_odd_prime, discr_zeta_eq_discr_zeta_sub_one, discr_zeta_eq_discr_zeta_sub_one.symm, hp.out.pos, irreducible_rat
-/
theorem discr_odd_prime' [IsCyclotomicExtension {p} Rat K] (hζ : IsPrimitiveRoot ζ p) (hodd : p != 2) :
    discr Rat (hζ.subOnePowerBasis Rat).basis = (-1) ^ ((p - 1) / 2) * p ^ (p - 2) := by
  rw [← discr_odd_prime hζ (cyclotomic.irreducible_rat hp.out.pos) hodd]
  exact hζ.discr_zeta_eq_discr_zeta_sub_one.symm

/--
theorem `discr_prime_pow'` / 定理 `discr_prime_pow'`

English:
theorem discr_prime_pow'
  given: [IsCyclotomicExtension {p ^ k} Rat K] (hζ : IsPrimitiveRoot ζ (p ^ k))
  proof: by
  rw [← discr_prime_pow hζ (cyclotomic.irreducible_rat (NeZero.pos _))]
  exact hζ.discr_zeta_eq_discr_zeta_sub_one.symm

中文:
定理 discr_prime_pow'
  条件: [IsCyclotomicExtension {p ^ k} Rat K] (hζ : IsPrimitiveRoot ζ (p ^ k))
  证明: by
  rw [← discr_prime_pow hζ (cyclotomic.irreducible_rat (NeZero.pos _))]
  exact hζ.discr_zeta_eq_discr_zeta_sub_one.symm

Depends on / 依赖: NeZero, NeZero.pos, cyclotomic, cyclotomic.irreducible_rat, discr_prime_pow, discr_zeta_eq_discr_zeta_sub_one, discr_zeta_eq_discr_zeta_sub_one.symm, irreducible_rat
-/
theorem discr_prime_pow' [IsCyclotomicExtension {p ^ k} Rat K] (hζ : IsPrimitiveRoot ζ (p ^ k)) :
    discr Rat (hζ.subOnePowerBasis Rat).basis =
      (-1) ^ ((p ^ k).totient / 2) * p ^ (p ^ (k - 1) * ((p - 1) * k - 1)) := by
  rw [← discr_prime_pow hζ (cyclotomic.irreducible_rat (NeZero.pos _))]
  exact hζ.discr_zeta_eq_discr_zeta_sub_one.symm

/--
theorem `discr_prime_pow_eq_unit_mul_pow'` / 定理 `discr_prime_pow_eq_unit_mul_pow'`

English:
theorem discr_prime_pow_eq_unit_mul_pow'
  statement: [IsCyclotomicExtension {p ^ k} Rat K]
  proof: by
  rw [hζ.discr_zeta_eq_discr_zeta_sub_one.symm]
  exact discr_prime_pow_eq_unit_mul_pow hζ (cyclotomic.irreducible_rat (NeZero.pos _))

中文:
定理 discr_prime_pow_eq_unit_mul_pow'
  结论: [IsCyclotomicExtension {p ^ k} Rat K]
  证明: by
  rw [hζ.discr_zeta_eq_discr_zeta_sub_one.symm]
  exact discr_prime_pow_eq_unit_mul_pow hζ (cyclotomic.irreducible_rat (NeZero.pos _))

Depends on / 依赖: NeZero, NeZero.pos, cyclotomic, cyclotomic.irreducible_rat, discr_prime_pow_eq_unit_mul_pow, discr_zeta_eq_discr_zeta_sub_one, discr_zeta_eq_discr_zeta_sub_one.symm, irreducible_rat
-/
theorem discr_prime_pow_eq_unit_mul_pow' [IsCyclotomicExtension {p ^ k} Rat K]
    (hζ : IsPrimitiveRoot ζ (p ^ k)) :
    exists (u : Intˣ) (n : Nat), discr Rat (hζ.subOnePowerBasis Rat).basis = u * p ^ n := by
  rw [hζ.discr_zeta_eq_discr_zeta_sub_one.symm]
  exact discr_prime_pow_eq_unit_mul_pow hζ (cyclotomic.irreducible_rat (NeZero.pos _))

/--
theorem `isIntegralClosure_adjoin_singleton_of_prime_pow` / 定理 `isIntegralClosure_adjoin_singleton_of_prime_pow`

English:
theorem isIntegralClosure_adjoin_singleton_of_prime_pow
  statement: [hcycl : IsCyclotomicExtension {p ^ k} Rat K]
  proof: by
  refine ⟨Subtype.val_injective, @fun x => ⟨fun h => ⟨⟨x, ?_⟩, rfl⟩, ?_⟩⟩
  swap
  · rintro ⟨y, rfl⟩
    exact
      IsIntegral.algebraMap
        ((le_integralClosure_iff_isIntegral.1
          (adjoin_le_integralClosure (hζ.isIntegral (NeZero.pos _)))).isIntegral _)
  let B := hζ.subOnePowerBas

中文:
定理 isIntegralClosure_adjoin_singleton_of_prime_pow
  结论: [hcycl : IsCyclotomicExtension {p ^ k} Rat K]
  证明: by
  refine ⟨Subtype.val_injective, @fun x => ⟨fun h => ⟨⟨x, ?_⟩, rfl⟩, ?_⟩⟩
  swap
  · rintro ⟨y, rfl⟩
    exact
      IsIntegral.algebraMap
        ((le_integralClosure_iff_isIntegral.1
          (adjoin_le_integralClosure (hζ.isIntegral (NeZero.pos _)))).isIntegral _)
  let B := hζ.subOnePowerBas

Depends on / 依赖: B.gen, IsIntegral, IsIntegral.algebraMap, NeZero, NeZero.pos, Subtype, Subtype.val_injective, adjoin_le_integralClosure, algebraMap, isIntegral, isIntegral_one, le_integralClosure_iff_isIntegral, subOnePowerBasis, val_injective
-/
theorem isIntegralClosure_adjoin_singleton_of_prime_pow [hcycl : IsCyclotomicExtension {p ^ k} Rat K]
    (hζ : IsPrimitiveRoot ζ (p ^ k)) : IsIntegralClosure (adjoin Int ({ζ} : Set K)) Int K := by
  refine ⟨Subtype.val_injective, @fun x => ⟨fun h => ⟨⟨x, ?_⟩, rfl⟩, ?_⟩⟩
  swap
  · rintro ⟨y, rfl⟩
    exact
      IsIntegral.algebraMap
        ((le_integralClosure_iff_isIntegral.1
          (adjoin_le_integralClosure (hζ.isIntegral (NeZero.pos _)))).isIntegral _)
  let B := hζ.subOnePowerBasis Rat
  have hint : IsIntegral Int B.gen := (hζ.isIntegral (NeZero.pos _)).sub isIntegral_one
  -- This can't be a `local instance` because it has metavariables.
  let := IsCyclotomicExtension.finiteDimensional {p ^ k} Rat K
  have H := discr_mul_isIntegral_mem_adjoin Rat hint h
  obtain ⟨u, n, hun⟩ := discr_prime_pow_eq_unit_mul_pow' hζ
  rw [hun] at H
  replace H := Subalgebra.smul_mem _ H u.inv
  rw [← smul_assoc]; rw [← smul_mul_assoc]; rw [Units.inv_eq_val_inv]; rw [zsmul_eq_mul]; rw [← Int.cast_mul]; rw [Units.inv_mul]; rw [Int.cast_one]; rw [one_mul]; rw [smul_def]; rw [map_pow] at H
  cases k
  · have : IsCyclotomicExtension {1} Rat K := by simpa using hcycl
    have : x in (⊥ : Subalgebra Rat K) := by
      rw [singleton_one Rat K]
      exact mem_top
    obtain ⟨y, rfl⟩ := mem_bot.1 this
    replace h := (isIntegral_algebraMap_iff (algebraMap Rat K).injective).1 h
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
    rw [← hz]; rw [← IsScalarTower.algebraMap_apply]
    exact Subalgebra.algebraMap_mem _ _
  · have hmin : (minpoly Int B.gen).IsEisensteinAt (Submodule.span Int {(p : Int)}) := by
      have h₁ := minpoly.isIntegrallyClosed_eq_field_fractions' Rat hint
      have h₂ := hζ.minpoly_sub_one_eq_cyclotomic_comp (cyclotomic.irreducible_rat (NeZero.pos _))
      rw [IsPrimitiveRoot.subOnePowerBasis_gen] at h₁
      rw [h₁]; rw [← map_cyclotomic_int]; rw [← algebraMap_int_eq]; rw [show X + 1 = map (algebraMap Int Rat) (X + 1) by simp]; rw [← map_comp] at h₂
      rw [IsPrimitiveRoot.subOnePowerBasis_gen]; rw [map_injective (algebraMap Int Rat) (algebraMap Int Rat).injective_int h₂]
      exact cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt p _
    refine
      adjoin_le ?_
        (mem_adjoin_of_smul_prime_pow_smul_of_minpoly_isEisensteinAt (n := n)
          (Nat.prime_iff_prime_int.1 hp.out) hint h (by simpa using H) hmin)
    simp only [Set.singleton_subset_iff, SetLike.mem_coe]
    exact Subalgebra.sub_mem _ (self_mem_adjoin_singleton Int _) (Subalgebra.one_mem _)

/--
theorem `isIntegralClosure_adjoin_singleton_of_prime` / 定理 `isIntegralClosure_adjoin_singleton_of_prime`

English:
theorem isIntegralClosure_adjoin_singleton_of_prime
  statement: [hcycl : IsCyclotomicExtension {p} Rat K]
  proof: by
  rw [← pow_one p] at hζ hcycl
  exact isIntegralClosure_adjoin_singleton_of_prime_pow hζ

中文:
定理 isIntegralClosure_adjoin_singleton_of_prime
  结论: [hcycl : IsCyclotomicExtension {p} Rat K]
  证明: by
  rw [← pow_one p] at hζ hcycl
  exact isIntegralClosure_adjoin_singleton_of_prime_pow hζ

Depends on / 依赖: isIntegralClosure_adjoin_singleton_of_prime_pow, pow_one
-/
theorem isIntegralClosure_adjoin_singleton_of_prime [hcycl : IsCyclotomicExtension {p} Rat K]
    (hζ : IsPrimitiveRoot ζ p) : IsIntegralClosure (adjoin Int ({ζ} : Set K)) Int K := by
  rw [← pow_one p] at hζ hcycl
  exact isIntegralClosure_adjoin_singleton_of_prime_pow hζ

set_option backward.isDefEq.respectTransparency false in
/--
theorem `cyclotomicRing_isIntegralClosure_of_prime_pow` / 定理 `cyclotomicRing_isIntegralClosure_of_prime_pow`

English:
theorem cyclotomicRing_isIntegralClosure_of_prime_pow
  proof: by
  have hζ := zeta_spec (p ^ k) Rat (CyclotomicField (p ^ k) Rat)
  refine ⟨IsFractionRing.injective _ _, @fun x => ⟨fun h => ⟨⟨x, ?_⟩, rfl⟩, ?_⟩⟩
  · obtain ⟨y, rfl⟩ := (isIntegralClosure_adjoin_singleton_of_prime_pow hζ).isIntegral_iff.1 h
    refine adjoin_mono ?_ y.2
    simp only [Set.singlet

中文:
定理 cyclotomicRing_isIntegralClosure_of_prime_pow
  证明: by
  have hζ := zeta_spec (p ^ k) Rat (CyclotomicField (p ^ k) Rat)
  refine ⟨IsFractionRing.injective _ _, @fun x => ⟨fun h => ⟨⟨x, ?_⟩, rfl⟩, ?_⟩⟩
  · obtain ⟨y, rfl⟩ := (isIntegralClosure_adjoin_singleton_of_prime_pow hζ).isIntegral_iff.1 h
    refine adjoin_mono ?_ y.2
    simp only [Set.singlet

Depends on / 依赖: CyclotomicField, IsCyclotomicExtension, IsCyclotomicExtension.integral, IsFractionRing, IsFractionRing.injective, IsIntegral, IsIntegral.algebraMap, Set.mem_ofPred_eq, Set.singleton_subset_iff, adjoin_mono, algebraMap, injective, integral, isIntegral, isIntegralClosure_adjoin_singleton_of_prime_pow, isIntegral_iff, mem_ofPred_eq, pow_eq_one, singleton_subset_iff, zeta_spec
-/
theorem cyclotomicRing_isIntegralClosure_of_prime_pow :
    IsIntegralClosure (CyclotomicRing (p ^ k) Int Rat) Int (CyclotomicField (p ^ k) Rat) := by
  have hζ := zeta_spec (p ^ k) Rat (CyclotomicField (p ^ k) Rat)
  refine ⟨IsFractionRing.injective _ _, @fun x => ⟨fun h => ⟨⟨x, ?_⟩, rfl⟩, ?_⟩⟩
  · obtain ⟨y, rfl⟩ := (isIntegralClosure_adjoin_singleton_of_prime_pow hζ).isIntegral_iff.1 h
    refine adjoin_mono ?_ y.2
    simp only [Set.singleton_subset_iff, Set.mem_ofPred_eq]
    exact hζ.pow_eq_one
  · rintro ⟨y, rfl⟩
    exact IsIntegral.algebraMap ((IsCyclotomicExtension.integral {p ^ k} Int _).isIntegral _)

/--
theorem `cyclotomicRing_isIntegralClosure_of_prime` / 定理 `cyclotomicRing_isIntegralClosure_of_prime`

English:
theorem cyclotomicRing_isIntegralClosure_of_prime
  proof: by
  rw [← pow_one p]
  exact cyclotomicRing_isIntegralClosure_of_prime_pow

中文:
定理 cyclotomicRing_isIntegralClosure_of_prime
  证明: by
  rw [← pow_one p]
  exact cyclotomicRing_isIntegralClosure_of_prime_pow

Depends on / 依赖: cyclotomicRing_isIntegralClosure_of_prime_pow, pow_one
-/
theorem cyclotomicRing_isIntegralClosure_of_prime :
    IsIntegralClosure (CyclotomicRing p Int Rat) Int (CyclotomicField p Rat) := by
  rw [← pow_one p]
  exact cyclotomicRing_isIntegralClosure_of_prime_pow

end IsCyclotomicExtension.Rat

section PowerBasis

open IsCyclotomicExtension.Rat

namespace IsPrimitiveRoot

section CharZero

variable [CharZero K]

/-- The algebra isomorphism `adjoin ℤ {ζ} ≃ₐ[ℤ] (𝓞 K)`, where `ζ` is a primitive `p ^ k`-th root of
unity and `K` is a `p ^ k`-th cyclotomic extension of `ℚ`. -/
@[simps!]
/--
Definition of `_root_.IsPrimitiveRoot.adjoinEquivRingOfIntegersOfPrimePow` / `_root_.IsPrimitiveRoot.adjoinEquivRingOfIntegersOfPrimePow` 的定义

English:
definition _root_.IsPrimitiveRoot.adjoinEquivRingOfIntegersOfPrimePow
  body: let _ := isIntegralClosure_adjoin_singleton_of_prime_pow hζ
  IsIntegralClosure.equiv Int (adjoin Int ({ζ} : Set K)) K (𝓞 K)

中文:
定义 _root_.IsPrimitiveRoot.adjoinEquivRingOfIntegersOfPrimePow
  定义体: let _ := isIntegralClosure_adjoin_singleton_of_prime_pow hζ
  IsIntegralClosure.equiv Int (adjoin Int ({ζ} : Set K)) K (𝓞 K)

Depends on / 依赖: IsIntegralClosure, IsIntegralClosure.equiv, adjoin, isIntegralClosure_adjoin_singleton_of_prime_pow
-/
noncomputable def _root_.IsPrimitiveRoot.adjoinEquivRingOfIntegersOfPrimePow
    [IsCyclotomicExtension {p ^ k} Rat K] (hζ : IsPrimitiveRoot ζ (p ^ k)) :
    adjoin Int ({ζ} : Set K) ≃ₐ[Int] 𝓞 K :=
  let _ := isIntegralClosure_adjoin_singleton_of_prime_pow hζ
  IsIntegralClosure.equiv Int (adjoin Int ({ζ} : Set K)) K (𝓞 K)

/--
Instance `IsCyclotomicExtension.ringOfIntegersOfPrimePow` / 实例 `IsCyclotomicExtension.ringOfIntegersOfPrimePow`

English:
instance IsCyclotomicExtension.ringOfIntegersOfPrimePow
  signature: [IsCyclotomicExtension {p ^ k} Rat K]
  body: let _ := (zeta_spec (p ^ k) Rat K).adjoin_isCyclotomicExtension Int
  IsCyclotomicExtension.equiv _ Int _ (zeta_spec (p ^ k) Rat K).adjoinEquivRingOfIntegersOfPrimePow

中文:
实例 IsCyclotomicExtension.ringOfIntegersOfPrimePow
  签名: [IsCyclotomicExtension {p ^ k} Rat K]
  定义体: let _ := (zeta_spec (p ^ k) Rat K).adjoin_isCyclotomicExtension Int
  IsCyclotomicExtension.equiv _ Int _ (zeta_spec (p ^ k) Rat K).adjoinEquivRingOfIntegersOfPrimePow

Depends on / 依赖: IsCyclotomicExtension, IsCyclotomicExtension.equiv, adjoinEquivRingOfIntegersOfPrimePow, adjoin_isCyclotomicExtension, zeta_spec
-/
instance IsCyclotomicExtension.ringOfIntegersOfPrimePow [IsCyclotomicExtension {p ^ k} Rat K] :
    IsCyclotomicExtension {p ^ k} Int (𝓞 K) :=
  let _ := (zeta_spec (p ^ k) Rat K).adjoin_isCyclotomicExtension Int
  IsCyclotomicExtension.equiv _ Int _ (zeta_spec (p ^ k) Rat K).adjoinEquivRingOfIntegersOfPrimePow

/--
Definition of `integralPowerBasisOfPrimePow` / `integralPowerBasisOfPrimePow` 的定义

English:
definition integralPowerBasisOfPrimePow
  signature: [IsCyclotomicExtension {p ^ k} Rat K]
  body: (Algebra.adjoin.powerBasis' (hζ.isIntegral (NeZero.pos _))).map
    hζ.adjoinEquivRingOfIntegersOfPrimePow

中文:
定义 integralPowerBasisOfPrimePow
  签名: [IsCyclotomicExtension {p ^ k} Rat K]
  定义体: (Algebra.adjoin.powerBasis' (hζ.isIntegral (NeZero.pos _))).map
    hζ.adjoinEquivRingOfIntegersOfPrimePow

Depends on / 依赖: Algebra, Algebra.adjoin.powerBasis, NeZero, NeZero.pos, adjoin, adjoinEquivRingOfIntegersOfPrimePow, isIntegral, powerBasis
-/
noncomputable def integralPowerBasisOfPrimePow [IsCyclotomicExtension {p ^ k} Rat K]
    (hζ : IsPrimitiveRoot ζ (p ^ k)) : PowerBasis Int (𝓞 K) :=
  (Algebra.adjoin.powerBasis' (hζ.isIntegral (NeZero.pos _))).map
    hζ.adjoinEquivRingOfIntegersOfPrimePow

/--
Definition of `toInteger` / `toInteger` 的定义

English:
abbreviation toInteger
  signature: {k : Nat} [NeZero k] (hζ : IsPrimitiveRoot ζ k)
  body: ⟨ζ, hζ.isIntegral (NeZero.pos _)⟩

中文:
缩写 toInteger
  签名: {k : 自然数} [NeZero k] (hζ : IsPrimitiveRoot ζ k)
  定义体: ⟨ζ, hζ.isIntegral (NeZero.pos _)⟩

Depends on / 依赖: NeZero, NeZero.pos, isIntegral
-/
abbrev toInteger {k : Nat} [NeZero k] (hζ : IsPrimitiveRoot ζ k) : 𝓞 K :=
  ⟨ζ, hζ.isIntegral (NeZero.pos _)⟩

end CharZero

/--
lemma `coe_toInteger` / 引理 `coe_toInteger`

English:
lemma coe_toInteger
  given: {k : Nat} [NeZero k] (hζ : IsPrimitiveRoot ζ k)
  statement: hζ.toInteger.1 = ζ
  proof: rfl

@[simp]

中文:
引理 coe_toInteger
  条件: {k : 自然数} [NeZero k] (hζ : IsPrimitiveRoot ζ k)
  结论: hζ.to整数eger.1 = ζ
  证明: rfl

@[simp]
-/
lemma coe_toInteger {k : Nat} [NeZero k] (hζ : IsPrimitiveRoot ζ k) : hζ.toInteger.1 = ζ := rfl

@[simp]
/--
lemma `toInteger_coe` / 引理 `toInteger_coe`

English:
lemma toInteger_coe
  given: {k : Nat} [NeZero k] {x : 𝓞 K} (hx : IsPrimitiveRoot (x : K) k)
  proof: rfl

中文:
引理 toInteger_coe
  条件: {k : 自然数} [NeZero k] {x : 𝓞 K} (hx : IsPrimitiveRoot (x : K) k)
  证明: rfl
-/
lemma toInteger_coe {k : Nat} [NeZero k] {x : 𝓞 K} (hx : IsPrimitiveRoot (x : K) k) :
    hx.toInteger = x := rfl

/--
lemma `finite_quotient_toInteger_sub_one` / 引理 `finite_quotient_toInteger_sub_one`

English:
lemma finite_quotient_toInteger_sub_one
  statement: [NumberField K] {k : Nat} (hk : 1 < k)
  proof: NeZero.of_gt hk
    Finite (𝓞 K ⧸ Ideal.span {hζ.toInteger - 1}) := by
  refine Ideal.finiteQuotientOfFreeOfNeBot _ (fun h => ?_)
  simp only [Ideal.span_singleton_eq_bot, sub_eq_zero] at h
  exact hζ.ne_one hk (RingOfIntegers.ext_iff.1 h)

中文:
引理 finite_quotient_toInteger_sub_one
  结论: [NumberField K] {k : 自然数} (hk : 1 < k)
  证明: NeZero.of_gt hk
    Finite (𝓞 K ⧸ Ideal.span {hζ.toInteger - 1}) := by
  refine Ideal.finiteQuotientOfFreeOfNeBot _ (fun h => ?_)
  simp only [Ideal.span_singleton_eq_bot, sub_eq_zero] at h
  exact hζ.ne_one hk (RingOfIntegers.ext_iff.1 h)

Depends on / 依赖: NeZero, NeZero.of_gt, of_gt
-/
lemma finite_quotient_toInteger_sub_one [NumberField K] {k : Nat} (hk : 1 < k)
    (hζ : IsPrimitiveRoot ζ k) :
    haveI : NeZero k := NeZero.of_gt hk
    Finite (𝓞 K ⧸ Ideal.span {hζ.toInteger - 1}) := by
  refine Ideal.finiteQuotientOfFreeOfNeBot _ (fun h => ?_)
  simp only [Ideal.span_singleton_eq_bot, sub_eq_zero] at h
  exact hζ.ne_one hk (RingOfIntegers.ext_iff.1 h)

/--
lemma `card_quotient_toInteger_sub_one` / 引理 `card_quotient_toInteger_sub_one`

English:
lemma card_quotient_toInteger_sub_one
  statement: [NumberField K] {k : Nat} [NeZero k]
  proof: by
  rw [← Submodule.cardQuot_apply]; rw [← Ideal.absNorm_apply]; rw [Ideal.absNorm_span_singleton]

中文:
引理 card_quotient_toInteger_sub_one
  结论: [NumberField K] {k : 自然数} [NeZero k]
  证明: by
  rw [← Submodule.cardQuot_apply]; rw [← Ideal.absNorm_apply]; rw [Ideal.absNorm_span_singleton]

Depends on / 依赖: Ideal.absNorm_apply, Ideal.absNorm_span_singleton, Submodule, Submodule.cardQuot_apply, absNorm_apply, absNorm_span_singleton, cardQuot_apply
-/
lemma card_quotient_toInteger_sub_one [NumberField K] {k : Nat} [NeZero k]
    (hζ : IsPrimitiveRoot ζ k) :
    Nat.card (𝓞 K ⧸ Ideal.span {hζ.toInteger - 1}) =
      (Algebra.norm Int (hζ.toInteger - 1)).natAbs := by
  rw [← Submodule.cardQuot_apply]; rw [← Ideal.absNorm_apply]; rw [Ideal.absNorm_span_singleton]

/--
lemma `toInteger_isPrimitiveRoot` / 引理 `toInteger_isPrimitiveRoot`

English:
lemma toInteger_isPrimitiveRoot
  given: {k : Nat} [NeZero k] (hζ : IsPrimitiveRoot ζ k)
  proof: IsPrimitiveRoot.of_map_of_injective (by exact hζ) RingOfIntegers.coe_injective

中文:
引理 toInteger_isPrimitiveRoot
  条件: {k : 自然数} [NeZero k] (hζ : IsPrimitiveRoot ζ k)
  证明: IsPrimitiveRoot.of_map_of_injective (by exact hζ) RingOfIntegers.coe_injective

Depends on / 依赖: IsPrimitiveRoot, IsPrimitiveRoot.of_map_of_injective, RingOfIntegers, RingOfIntegers.coe_injective, coe_injective, of_map_of_injective
-/
lemma toInteger_isPrimitiveRoot {k : Nat} [NeZero k] (hζ : IsPrimitiveRoot ζ k) :
    IsPrimitiveRoot hζ.toInteger k :=
  IsPrimitiveRoot.of_map_of_injective (by exact hζ) RingOfIntegers.coe_injective

variable [CharZero K]

@[simp]
/--
theorem `integralPowerBasisOfPrimePow_gen` / 定理 `integralPowerBasisOfPrimePow_gen`

English:
theorem integralPowerBasisOfPrimePow_gen
  statement: [hcycl : IsCyclotomicExtension {p ^ k} Rat K]
  proof: Subtype.ext show algebraMap _ K hζ.integralPowerBasisOfPrimePow.gen = _ by
    rw [integralPowerBasisOfPrimePow]; rw [PowerBasis.map_gen]; rw [adjoin.powerBasis'_gen]
    simp only [adjoinEquivRingOfIntegersOfPrimePow_apply, IsIntegralClosure.algebraMap_lift]
    rfl

中文:
定理 integralPowerBasisOfPrimePow_gen
  结论: [hcycl : IsCyclotomicExtension {p ^ k} Rat K]
  证明: Subtype.ext show algebraMap _ K hζ.integralPowerBasisOfPrimePow.gen = _ by
    rw [integralPowerBasisOfPrimePow]; rw [PowerBasis.map_gen]; rw [adjoin.powerBasis'_gen]
    simp only [adjoinEquivRingOfIntegersOfPrimePow_apply, IsIntegralClosure.algebraMap_lift]
    rfl

Depends on / 依赖: IsIntegralClosure, IsIntegralClosure.algebraMap_lift, PowerBasis, PowerBasis.map_gen, Subtype, Subtype.ext, _gen, adjoin, adjoin.powerBasis, adjoinEquivRingOfIntegersOfPrimePow_apply, algebraMap, algebraMap_lift, integralPowerBasisOfPrimePow, integralPowerBasisOfPrimePow.gen, map_gen, powerBasis
-/
theorem integralPowerBasisOfPrimePow_gen [hcycl : IsCyclotomicExtension {p ^ k} Rat K]
    (hζ : IsPrimitiveRoot ζ (p ^ k)) :
    hζ.integralPowerBasisOfPrimePow.gen = hζ.toInteger :=
Subtype.ext show algebraMap _ K hζ.integralPowerBasisOfPrimePow.gen = _ by
    rw [integralPowerBasisOfPrimePow]; rw [PowerBasis.map_gen]; rw [adjoin.powerBasis'_gen]
    simp only [adjoinEquivRingOfIntegersOfPrimePow_apply, IsIntegralClosure.algebraMap_lift]
    rfl

/- We name `hcycl` so it can be used as a named argument. -/
@[simp]
/--
theorem `integralPowerBasisOfPrimePow_dim` / 定理 `integralPowerBasisOfPrimePow_dim`

English:
theorem integralPowerBasisOfPrimePow_dim
  statement: [hcycl : IsCyclotomicExtension {p ^ k} Rat K]
  proof: by
  simp [integralPowerBasisOfPrimePow, ← cyclotomic_eq_minpoly hζ (NeZero.pos _),
    natDegree_cyclotomic]

中文:
定理 integralPowerBasisOfPrimePow_dim
  结论: [hcycl : IsCyclotomicExtension {p ^ k} Rat K]
  证明: by
  simp [integralPowerBasisOfPrimePow, ← cyclotomic_eq_minpoly hζ (NeZero.pos _),
    natDegree_cyclotomic]

Depends on / 依赖: NeZero, NeZero.pos, cyclotomic_eq_minpoly, integralPowerBasisOfPrimePow, natDegree_cyclotomic
-/
theorem integralPowerBasisOfPrimePow_dim [hcycl : IsCyclotomicExtension {p ^ k} Rat K]
    (hζ : IsPrimitiveRoot ζ (p ^ k)) : hζ.integralPowerBasisOfPrimePow.dim = φ (p ^ k) := by
  simp [integralPowerBasisOfPrimePow, ← cyclotomic_eq_minpoly hζ (NeZero.pos _),
    natDegree_cyclotomic]

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `subOneIntegralPowerBasisOfPrimePow` / `subOneIntegralPowerBasisOfPrimePow` 的定义

English:
definition subOneIntegralPowerBasisOfPrimePow
  signature: [IsCyclotomicExtension {p ^ k} Rat K]
  body: PowerBasis.ofAdjoinEqTop'
    (RingOfIntegers.isIntegral ⟨ζ- 1, (hζ.isIntegral (NeZero.pos _)).sub isIntegral_one⟩) (by
    refine hζ.integralPowerBasisOfPrimePow.adjoin_eq_top_of_gen_mem_adjoin ?_
    convert! Subalgebra.add_mem _ (self_mem_adjoin_singleton Int _) (Subalgebra.one_mem _)
    simp [R

中文:
定义 subOneIntegralPowerBasisOfPrimePow
  签名: [IsCyclotomicExtension {p ^ k} Rat K]
  定义体: PowerBasis.ofAdjoinEqTop'
    (RingOfIntegers.isIntegral ⟨ζ- 1, (hζ.isIntegral (NeZero.pos _)).sub isIntegral_one⟩) (by
    refine hζ.integralPowerBasisOfPrimePow.adjoin_eq_top_of_gen_mem_adjoin ?_
    convert! Subalgebra.add_mem _ (self_mem_adjoin_singleton Int _) (Subalgebra.one_mem _)
    simp [R

Depends on / 依赖: NeZero, NeZero.pos, PowerBasis, PowerBasis.ofAdjoinEqTop, RingOfIntegers, RingOfIntegers.ext_iff, RingOfIntegers.isIntegral, Subalgebra, Subalgebra.add_mem, Subalgebra.one_mem, add_mem, adjoin_eq_top_of_gen_mem_adjoin, convert, ext_iff, integralPowerBasisOfPrimePow, integralPowerBasisOfPrimePow.adjoin_eq_top_of_gen_mem_adjoin, integralPowerBasisOfPrimePow_gen, isIntegral, isIntegral_one, ofAdjoinEqTop
-/
noncomputable def subOneIntegralPowerBasisOfPrimePow [IsCyclotomicExtension {p ^ k} Rat K]
    (hζ : IsPrimitiveRoot ζ (p ^ k)) : PowerBasis Int (𝓞 K) :=
  PowerBasis.ofAdjoinEqTop'
    (RingOfIntegers.isIntegral ⟨ζ- 1, (hζ.isIntegral (NeZero.pos _)).sub isIntegral_one⟩) (by
    refine hζ.integralPowerBasisOfPrimePow.adjoin_eq_top_of_gen_mem_adjoin ?_
    convert! Subalgebra.add_mem _ (self_mem_adjoin_singleton Int _) (Subalgebra.one_mem _)
    simp [RingOfIntegers.ext_iff, integralPowerBasisOfPrimePow_gen, toInteger])

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `subOneIntegralPowerBasisOfPrimePow_gen` / 定理 `subOneIntegralPowerBasisOfPrimePow_gen`

English:
theorem subOneIntegralPowerBasisOfPrimePow_gen
  statement: [IsCyclotomicExtension {p ^ k} Rat K]
  proof: by
  simp [subOneIntegralPowerBasisOfPrimePow]

中文:
定理 subOneIntegralPowerBasisOfPrimePow_gen
  结论: [IsCyclotomicExtension {p ^ k} Rat K]
  证明: by
  simp [subOneIntegralPowerBasisOfPrimePow]

Depends on / 依赖: subOneIntegralPowerBasisOfPrimePow
-/
theorem subOneIntegralPowerBasisOfPrimePow_gen [IsCyclotomicExtension {p ^ k} Rat K]
    (hζ : IsPrimitiveRoot ζ (p ^ k)) :
    hζ.subOneIntegralPowerBasisOfPrimePow.gen =
      ⟨ζ - 1, Subalgebra.sub_mem _ (hζ.isIntegral (NeZero.pos _)) (Subalgebra.one_mem _)⟩ := by
  simp [subOneIntegralPowerBasisOfPrimePow]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `zeta_sub_one_prime_of_ne_two` / 定理 `zeta_sub_one_prime_of_ne_two`

English:
theorem zeta_sub_one_prime_of_ne_two
  statement: [IsCyclotomicExtension {p ^ (k + 1)} Rat K]
  proof: by
  let := IsCyclotomicExtension.numberField {p ^ (k + 1)} Rat K
  refine Ideal.prime_of_irreducible_absNorm_span (fun h => ?_) ?_
  · apply hζ.pow_ne_one_of_pos_of_lt one_ne_zero (one_lt_pow₀ hp.out.one_lt (by simp))
    rw [sub_eq_zero] at h
    simpa using congrArg (algebraMap _ K) h
  rw [Nat.i

中文:
定理 zeta_sub_one_prime_of_ne_two
  结论: [IsCyclotomicExtension {p ^ (k + 1)} Rat K]
  证明: by
  let := IsCyclotomicExtension.numberField {p ^ (k + 1)} Rat K
  refine Ideal.prime_of_irreducible_absNorm_span (fun h => ?_) ?_
  · apply hζ.pow_ne_one_of_pos_of_lt one_ne_zero (one_lt_pow₀ hp.out.one_lt (by simp))
    rw [sub_eq_zero] at h
    simpa using congrArg (algebraMap _ K) h
  rw [Nat.i

Depends on / 依赖: Ideal.absNorm_span_singleton, Ideal.prime_of_irreducible_absNorm_span, Int.prime_iff_natAbs_prime, IsCyclotomicExtension, IsCyclotomicExtension.numberField, Nat.irreducible_iff_prime, Nat.prime_iff, Nat.prime_iff_prime_int, RingHom, RingHom.injective_int, absNorm_span_singleton, algebraMap, convert, hp.out, hp.out.one_lt, injective_int, irreducible_iff_prime, numberField, one_lt, one_ne_zero
-/
theorem zeta_sub_one_prime_of_ne_two [IsCyclotomicExtension {p ^ (k + 1)} Rat K]
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) (hodd : p != 2) :
    Prime (hζ.toInteger - 1) := by
  let := IsCyclotomicExtension.numberField {p ^ (k + 1)} Rat K
  refine Ideal.prime_of_irreducible_absNorm_span (fun h => ?_) ?_
  · apply hζ.pow_ne_one_of_pos_of_lt one_ne_zero (one_lt_pow₀ hp.out.one_lt (by simp))
    rw [sub_eq_zero] at h
    simpa using congrArg (algebraMap _ K) h
  rw [Nat.irreducible_iff_prime]; rw [Ideal.absNorm_span_singleton]; rw [← Nat.prime_iff]; rw [← Int.prime_iff_natAbs_prime]
  convert! Nat.prime_iff_prime_int.1 hp.out
  apply RingHom.injective_int (algebraMap Int Rat)
  rw [← Algebra.norm_localization (Sₘ := K) Int (nonZeroDivisors Int)]
  simp only [algebraMap_int_eq, map_natCast]
  exact hζ.norm_sub_one_of_prime_ne_two (Polynomial.cyclotomic.irreducible_rat (NeZero.pos _)) hodd

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `zeta_sub_one_prime_of_two_pow` / 定理 `zeta_sub_one_prime_of_two_pow`

English:
theorem zeta_sub_one_prime_of_two_pow
  statement: [IsCyclotomicExtension {2 ^ (k + 1)} Rat K]
  proof: by
  have := IsCyclotomicExtension.numberField {2 ^ (k + 1)} Rat K
  refine Ideal.prime_of_irreducible_absNorm_span (fun h => ?_) ?_
  · apply hζ.pow_ne_one_of_pos_of_lt one_ne_zero (one_lt_pow₀ (by decide) (by simp))
    rw [sub_eq_zero] at h
    simpa using! congrArg (algebraMap _ K) h
  rw [Nat.i

中文:
定理 zeta_sub_one_prime_of_two_pow
  结论: [IsCyclotomicExtension {2 ^ (k + 1)} Rat K]
  证明: by
  have := IsCyclotomicExtension.numberField {2 ^ (k + 1)} Rat K
  refine Ideal.prime_of_irreducible_absNorm_span (fun h => ?_) ?_
  · apply hζ.pow_ne_one_of_pos_of_lt one_ne_zero (one_lt_pow₀ (by decide) (by simp))
    rw [sub_eq_zero] at h
    simpa using! congrArg (algebraMap _ K) h
  rw [Nat.i

Depends on / 依赖: Ideal.absNorm_span_singleton, Ideal.prime_of_irreducible_absNorm_span, Int.prime_iff_natAbs_prime, Int.prime_two, IsCyclotomicExtension, IsCyclotomicExtension.numberField, Nat.irreducible_iff_prime, Nat.prime_iff, Prime.neg, RingHom, RingHom.injective_int, absNorm_span_singleton, algebraMap, convert, injective_int, irreducible_iff_prime, numberField, one_ne_zero, pow_ne_one_of_pos_of_lt, prime_iff
-/
theorem zeta_sub_one_prime_of_two_pow [IsCyclotomicExtension {2 ^ (k + 1)} Rat K]
    (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1))) :
    Prime (hζ.toInteger - 1) := by
  have := IsCyclotomicExtension.numberField {2 ^ (k + 1)} Rat K
  refine Ideal.prime_of_irreducible_absNorm_span (fun h => ?_) ?_
  · apply hζ.pow_ne_one_of_pos_of_lt one_ne_zero (one_lt_pow₀ (by decide) (by simp))
    rw [sub_eq_zero] at h
    simpa using! congrArg (algebraMap _ K) h
  rw [Nat.irreducible_iff_prime]; rw [Ideal.absNorm_span_singleton]; rw [← Nat.prime_iff]; rw [← Int.prime_iff_natAbs_prime]
  cases k
  · convert! Prime.neg Int.prime_two
    apply RingHom.injective_int (algebraMap Int Rat)
    rw [← Algebra.norm_localization (Sₘ := K) Int (nonZeroDivisors Int)]
    simp only [algebraMap_int_eq, map_neg, map_ofNat]
    simpa only [zero_add, pow_one, AddSubgroupClass.coe_sub, OneMemClass.coe_one,
        pow_zero]
      using! hζ.norm_pow_sub_one_two (cyclotomic.irreducible_rat
        (by simp only [zero_add, pow_one, Nat.ofNat_pos]))
  convert! Int.prime_two
  apply RingHom.injective_int (algebraMap Int Rat)
  rw [← Algebra.norm_localization (Sₘ := K) Int (nonZeroDivisors Int)]; rw [algebraMap_int_eq]
  exact hζ.norm_sub_one_two Nat.AtLeastTwo.prop (cyclotomic.irreducible_rat (by simp))

/--
theorem `zeta_sub_one_prime` / 定理 `zeta_sub_one_prime`

English:
theorem zeta_sub_one_prime
  statement: [IsCyclotomicExtension {p ^ (k + 1)} Rat K]
  proof: by
  by_cases htwo : p = 2
  · subst htwo
    apply hζ.zeta_sub_one_prime_of_two_pow
  · apply hζ.zeta_sub_one_prime_of_ne_two htwo

中文:
定理 zeta_sub_one_prime
  结论: [IsCyclotomicExtension {p ^ (k + 1)} Rat K]
  证明: by
  by_cases htwo : p = 2
  · subst htwo
    apply hζ.zeta_sub_one_prime_of_two_pow
  · apply hζ.zeta_sub_one_prime_of_ne_two htwo

Depends on / 依赖: zeta_sub_one_prime_of_ne_two, zeta_sub_one_prime_of_two_pow
-/
theorem zeta_sub_one_prime [IsCyclotomicExtension {p ^ (k + 1)} Rat K]
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) : Prime (hζ.toInteger - 1) := by
  by_cases htwo : p = 2
  · subst htwo
    apply hζ.zeta_sub_one_prime_of_two_pow
  · apply hζ.zeta_sub_one_prime_of_ne_two htwo

/--
theorem `zeta_sub_one_prime'` / 定理 `zeta_sub_one_prime'`

English:
theorem zeta_sub_one_prime'
  given: [h : IsCyclotomicExtension {p} Rat K] (hζ : IsPrimitiveRoot ζ p)
  proof: by
  convert! zeta_sub_one_prime (k := 0) (by simpa only [zero_add, pow_one])
  simpa only [zero_add, pow_one]

中文:
定理 zeta_sub_one_prime'
  条件: [h : IsCyclotomicExtension {p} Rat K] (hζ : IsPrimitiveRoot ζ p)
  证明: by
  convert! zeta_sub_one_prime (k := 0) (by simpa only [zero_add, pow_one])
  simpa only [zero_add, pow_one]

Depends on / 依赖: convert, pow_one, zero_add, zeta_sub_one_prime
-/
theorem zeta_sub_one_prime' [h : IsCyclotomicExtension {p} Rat K] (hζ : IsPrimitiveRoot ζ p) :
    Prime ((hζ.toInteger - 1)) := by
  convert! zeta_sub_one_prime (k := 0) (by simpa only [zero_add, pow_one])
  simpa only [zero_add, pow_one]

/--
theorem `subOneIntegralPowerBasisOfPrimePow_gen_prime` / 定理 `subOneIntegralPowerBasisOfPrimePow_gen_prime`

English:
theorem subOneIntegralPowerBasisOfPrimePow_gen_prime
  statement: [IsCyclotomicExtension {p ^ (k + 1)} Rat K]
  proof: by
  simpa only [subOneIntegralPowerBasisOfPrimePow_gen] using! hζ.zeta_sub_one_prime

中文:
定理 subOneIntegralPowerBasisOfPrimePow_gen_prime
  结论: [IsCyclotomicExtension {p ^ (k + 1)} Rat K]
  证明: by
  simpa only [subOneIntegralPowerBasisOfPrimePow_gen] using! hζ.zeta_sub_one_prime

Depends on / 依赖: subOneIntegralPowerBasisOfPrimePow_gen, zeta_sub_one_prime
-/
theorem subOneIntegralPowerBasisOfPrimePow_gen_prime [IsCyclotomicExtension {p ^ (k + 1)} Rat K]
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) :
    Prime hζ.subOneIntegralPowerBasisOfPrimePow.gen := by
  simpa only [subOneIntegralPowerBasisOfPrimePow_gen] using! hζ.zeta_sub_one_prime

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `norm_toInteger_sub_one_eq_one` / 定理 `norm_toInteger_sub_one_eq_one`

English:
theorem norm_toInteger_sub_one_eq_one
  statement: {n : Nat} [IsCyclotomicExtension {n} Rat K]
  proof: NeZero.of_gt h₁
    norm Int (hζ.toInteger - 1) = 1 := by
  have : NumberField K := IsCyclotomicExtension.numberField {n} Rat K
  have : NeZero n := NeZero.of_gt h₁
  dsimp only
  rw [norm_eq_iff Int (Sₘ := K) (Rₘ := Rat) le_rfl]; rw [map_sub]; rw [map_one]; rw [map_one]; rw [RingOfIntegers.map_mk];

中文:
定理 norm_toInteger_sub_one_eq_one
  结论: {n : 自然数} [IsCyclotomicExtension {n} Rat K]
  证明: NeZero.of_gt h₁
    norm Int (hζ.toInteger - 1) = 1 := by
  have : NumberField K := IsCyclotomicExtension.numberField {n} Rat K
  have : NeZero n := NeZero.of_gt h₁
  dsimp only
  rw [norm_eq_iff Int (Sₘ := K) (Rₘ := Rat) le_rfl]; rw [map_sub]; rw [map_one]; rw [map_one]; rw [RingOfIntegers.map_mk];

Depends on / 依赖: NeZero, NeZero.of_gt, of_gt
-/
theorem norm_toInteger_sub_one_eq_one {n : Nat} [IsCyclotomicExtension {n} Rat K]
    (hζ : IsPrimitiveRoot ζ n) (h₁ : 2 < n) (h₂ : forall {p : Nat}, Nat.Prime p -> forall (k : Nat), p ^ k != n) :
    have : NeZero n := NeZero.of_gt h₁
    norm Int (hζ.toInteger - 1) = 1 := by
  have : NumberField K := IsCyclotomicExtension.numberField {n} Rat K
  have : NeZero n := NeZero.of_gt h₁
  dsimp only
  rw [norm_eq_iff Int (Sₘ := K) (Rₘ := Rat) le_rfl]; rw [map_sub]; rw [map_one]; rw [map_one]; rw [RingOfIntegers.map_mk]; rw [sub_one_norm_eq_eval_cyclotomic hζ h₁ (cyclotomic.irreducible_rat (NeZero.pos _))]; rw [eval_one_cyclotomic_not_prime_pow h₂]; rw [Int.cast_one]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `norm_toInteger_pow_sub_one_of_prime_pow_ne_two` / 引理 `norm_toInteger_pow_sub_one_of_prime_pow_ne_two`

English:
lemma norm_toInteger_pow_sub_one_of_prime_pow_ne_two
  statement: [IsCyclotomicExtension {p ^ (k + 1)} Rat K]
  proof: by
  have : NumberField K := IsCyclotomicExtension.numberField {p ^ (k + 1)} Rat K
  rw [Algebra.norm_eq_iff Int (Sₘ := K) (Rₘ := Rat) le_rfl]
  simp [hζ.norm_pow_sub_one_of_prime_pow_ne_two (cyclotomic.irreducible_rat (NeZero.pos _)) hs htwo]

中文:
引理 norm_toInteger_pow_sub_one_of_prime_pow_ne_two
  结论: [IsCyclotomicExtension {p ^ (k + 1)} Rat K]
  证明: by
  have : NumberField K := IsCyclotomicExtension.numberField {p ^ (k + 1)} Rat K
  rw [Algebra.norm_eq_iff Int (Sₘ := K) (Rₘ := Rat) le_rfl]
  simp [hζ.norm_pow_sub_one_of_prime_pow_ne_two (cyclotomic.irreducible_rat (NeZero.pos _)) hs htwo]

Depends on / 依赖: Algebra, Algebra.norm_eq_iff, IsCyclotomicExtension, IsCyclotomicExtension.numberField, NeZero, NeZero.pos, NumberField, cyclotomic, cyclotomic.irreducible_rat, irreducible_rat, le_rfl, norm_eq_iff, norm_pow_sub_one_of_prime_pow_ne_two, numberField
-/
lemma norm_toInteger_pow_sub_one_of_prime_pow_ne_two [IsCyclotomicExtension {p ^ (k + 1)} Rat K]
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) {s : Nat} (hs : s <= k) (htwo : p ^ (k - s + 1) != 2) :
    Algebra.norm Int (hζ.toInteger ^ p ^ s - 1) = p ^ p ^ s := by
  have : NumberField K := IsCyclotomicExtension.numberField {p ^ (k + 1)} Rat K
  rw [Algebra.norm_eq_iff Int (Sₘ := K) (Rₘ := Rat) le_rfl]
  simp [hζ.norm_pow_sub_one_of_prime_pow_ne_two (cyclotomic.irreducible_rat (NeZero.pos _)) hs htwo]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `norm_toInteger_pow_sub_one_of_two` / 引理 `norm_toInteger_pow_sub_one_of_two`

English:
lemma norm_toInteger_pow_sub_one_of_two
  statement: [IsCyclotomicExtension {2 ^ (k + 1)} Rat K]
  proof: by
  have : NumberField K := IsCyclotomicExtension.numberField {2 ^ (k + 1)} Rat K
  rw [Algebra.norm_eq_iff Int (Sₘ := K) (Rₘ := Rat) le_rfl]
  simp [hζ.norm_pow_sub_one_two (cyclotomic.irreducible_rat (pow_pos (by decide) _))]

中文:
引理 norm_toInteger_pow_sub_one_of_two
  结论: [IsCyclotomicExtension {2 ^ (k + 1)} Rat K]
  证明: by
  have : NumberField K := IsCyclotomicExtension.numberField {2 ^ (k + 1)} Rat K
  rw [Algebra.norm_eq_iff Int (Sₘ := K) (Rₘ := Rat) le_rfl]
  simp [hζ.norm_pow_sub_one_two (cyclotomic.irreducible_rat (pow_pos (by decide) _))]

Depends on / 依赖: Algebra, Algebra.norm_eq_iff, IsCyclotomicExtension, IsCyclotomicExtension.numberField, NumberField, cyclotomic, cyclotomic.irreducible_rat, irreducible_rat, le_rfl, norm_eq_iff, norm_pow_sub_one_two, numberField, pow_pos
-/
lemma norm_toInteger_pow_sub_one_of_two [IsCyclotomicExtension {2 ^ (k + 1)} Rat K]
    (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1))) :
    Algebra.norm Int (hζ.toInteger ^ 2 ^ k - 1) = (-2) ^ 2 ^ k := by
  have : NumberField K := IsCyclotomicExtension.numberField {2 ^ (k + 1)} Rat K
  rw [Algebra.norm_eq_iff Int (Sₘ := K) (Rₘ := Rat) le_rfl]
  simp [hζ.norm_pow_sub_one_two (cyclotomic.irreducible_rat (pow_pos (by decide) _))]

/--
lemma `norm_toInteger_pow_sub_one_of_prime_ne_two` / 引理 `norm_toInteger_pow_sub_one_of_prime_ne_two`

English:
lemma norm_toInteger_pow_sub_one_of_prime_ne_two
  statement: [IsCyclotomicExtension {p ^ (k + 1)} Rat K]
  proof: by
  refine hζ.norm_toInteger_pow_sub_one_of_prime_pow_ne_two hs (fun h => hodd ?_)
  apply eq_of_prime_pow_eq hp.out.prime Nat.prime_two.prime (k - s).succ_pos
  rwa [pow_one]

中文:
引理 norm_toInteger_pow_sub_one_of_prime_ne_two
  结论: [IsCyclotomicExtension {p ^ (k + 1)} Rat K]
  证明: by
  refine hζ.norm_toInteger_pow_sub_one_of_prime_pow_ne_two hs (fun h => hodd ?_)
  apply eq_of_prime_pow_eq hp.out.prime Nat.prime_two.prime (k - s).succ_pos
  rwa [pow_one]

Depends on / 依赖: Nat.prime_two.prime, eq_of_prime_pow_eq, hp.out.prime, norm_toInteger_pow_sub_one_of_prime_pow_ne_two, pow_one, prime_two, succ_pos
-/
lemma norm_toInteger_pow_sub_one_of_prime_ne_two [IsCyclotomicExtension {p ^ (k + 1)} Rat K]
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) {s : Nat} (hs : s <= k) (hodd : p != 2) :
    Algebra.norm Int (hζ.toInteger ^ p ^ s - 1) = p ^ p ^ s := by
  refine hζ.norm_toInteger_pow_sub_one_of_prime_pow_ne_two hs (fun h => hodd ?_)
  apply eq_of_prime_pow_eq hp.out.prime Nat.prime_two.prime (k - s).succ_pos
  rwa [pow_one]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `norm_toInteger_sub_one_of_eq_two_pow` / 定理 `norm_toInteger_sub_one_of_eq_two_pow`

English:
theorem norm_toInteger_sub_one_of_eq_two_pow
  statement: {k : Nat} {K : Type*} [Field K]
  proof: by
  have : NumberField K := IsCyclotomicExtension.numberField {2 ^ (k + 2)} Rat K
  rw [norm_eq_iff Int (Sₘ := K) (Rₘ := Rat) le_rfl]; rw [map_sub]; rw [map_one]; rw [eq_intCast]; rw [Int.cast_ofNat]; rw [RingOfIntegers.map_mk]; rw [hζ.norm_sub_one_two (Nat.le_add_left 2 k)
    (Polynomial.cyclotom

中文:
定理 norm_toInteger_sub_one_of_eq_two_pow
  结论: {k : 自然数} {K : 类型} [Field K]
  证明: by
  have : NumberField K := IsCyclotomicExtension.numberField {2 ^ (k + 2)} Rat K
  rw [norm_eq_iff Int (Sₘ := K) (Rₘ := Rat) le_rfl]; rw [map_sub]; rw [map_one]; rw [eq_intCast]; rw [Int.cast_ofNat]; rw [RingOfIntegers.map_mk]; rw [hζ.norm_sub_one_two (Nat.le_add_left 2 k)
    (Polynomial.cyclotom

Depends on / 依赖: Int.cast_ofNat, IsCyclotomicExtension, IsCyclotomicExtension.numberField, Nat.le_add_left, Nat.two_pow_pos, NumberField, Polynomial, Polynomial.cyclotomic.irreducible_rat, RingOfIntegers, RingOfIntegers.map_mk, cast_ofNat, cyclotomic, eq_intCast, irreducible_rat, le_add_left, le_rfl, map_mk, map_one, map_sub, norm_eq_iff
-/
theorem norm_toInteger_sub_one_of_eq_two_pow {k : Nat} {K : Type*} [Field K]
    {ζ : K} [CharZero K] [IsCyclotomicExtension {2 ^ (k + 2)} Rat K]
    (hζ : IsPrimitiveRoot ζ (2 ^ (k + 2))) :
    norm Int (hζ.toInteger - 1) = 2 := by
  have : NumberField K := IsCyclotomicExtension.numberField {2 ^ (k + 2)} Rat K
  rw [norm_eq_iff Int (Sₘ := K) (Rₘ := Rat) le_rfl]; rw [map_sub]; rw [map_one]; rw [eq_intCast]; rw [Int.cast_ofNat]; rw [RingOfIntegers.map_mk]; rw [hζ.norm_sub_one_two (Nat.le_add_left 2 k)
    (Polynomial.cyclotomic.irreducible_rat (Nat.two_pow_pos _))]

/--
lemma `norm_toInteger_sub_one_of_prime_ne_two` / 引理 `norm_toInteger_sub_one_of_prime_ne_two`

English:
lemma norm_toInteger_sub_one_of_prime_ne_two
  statement: [IsCyclotomicExtension {p ^ (k + 1)} Rat K]
  proof: by
  simpa only [pow_zero, pow_one] using
    hζ.norm_toInteger_pow_sub_one_of_prime_ne_two (Nat.zero_le _) hodd

中文:
引理 norm_toInteger_sub_one_of_prime_ne_two
  结论: [IsCyclotomicExtension {p ^ (k + 1)} Rat K]
  证明: by
  simpa only [pow_zero, pow_one] using
    hζ.norm_toInteger_pow_sub_one_of_prime_ne_two (Nat.zero_le _) hodd

Depends on / 依赖: Nat.zero_le, norm_toInteger_pow_sub_one_of_prime_ne_two, pow_one, pow_zero, zero_le
-/
lemma norm_toInteger_sub_one_of_prime_ne_two [IsCyclotomicExtension {p ^ (k + 1)} Rat K]
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) (hodd : p != 2) :
    Algebra.norm Int (hζ.toInteger - 1) = p := by
  simpa only [pow_zero, pow_one] using
    hζ.norm_toInteger_pow_sub_one_of_prime_ne_two (Nat.zero_le _) hodd

/--
theorem `norm_toInteger_sub_one_of_eq_two` / 定理 `norm_toInteger_sub_one_of_eq_two`

English:
theorem norm_toInteger_sub_one_of_eq_two
  statement: [IsCyclotomicExtension {2} Rat K]
  proof: by
  rw [show 2 = (2 ^ (0 + 1)) by norm_num] at hζ
  simpa using hζ.norm_toInteger_pow_sub_one_of_two

中文:
定理 norm_toInteger_sub_one_of_eq_two
  结论: [IsCyclotomicExtension {2} Rat K]
  证明: by
  rw [show 2 = (2 ^ (0 + 1)) by norm_num] at hζ
  simpa using hζ.norm_toInteger_pow_sub_one_of_two

Depends on / 依赖: norm_toInteger_pow_sub_one_of_two
-/
theorem norm_toInteger_sub_one_of_eq_two [IsCyclotomicExtension {2} Rat K]
    (hζ : IsPrimitiveRoot ζ 2) :
    norm Int (hζ.toInteger - 1) = -2 := by
  rw [show 2 = (2 ^ (0 + 1)) by norm_num] at hζ
  simpa using hζ.norm_toInteger_pow_sub_one_of_two

/--
lemma `norm_toInteger_sub_one_of_prime_ne_two'` / 引理 `norm_toInteger_sub_one_of_prime_ne_two'`

English:
lemma norm_toInteger_sub_one_of_prime_ne_two'
  statement: [hcycl : IsCyclotomicExtension {p} Rat K]
  proof: by
  have : IsCyclotomicExtension {p ^ (0 + 1)} Rat K := by simpa using hcycl
  replace hζ : IsPrimitiveRoot ζ (p ^ (0 + 1)) := by simpa using hζ
  exact hζ.norm_toInteger_sub_one_of_prime_ne_two h

中文:
引理 norm_toInteger_sub_one_of_prime_ne_two'
  结论: [hcycl : IsCyclotomicExtension {p} Rat K]
  证明: by
  have : IsCyclotomicExtension {p ^ (0 + 1)} Rat K := by simpa using hcycl
  replace hζ : IsPrimitiveRoot ζ (p ^ (0 + 1)) := by simpa using hζ
  exact hζ.norm_toInteger_sub_one_of_prime_ne_two h

Depends on / 依赖: IsCyclotomicExtension, IsPrimitiveRoot, norm_toInteger_sub_one_of_prime_ne_two, replace
-/
lemma norm_toInteger_sub_one_of_prime_ne_two' [hcycl : IsCyclotomicExtension {p} Rat K]
    (hζ : IsPrimitiveRoot ζ p) (h : p != 2) : Algebra.norm Int (hζ.toInteger - 1) = p := by
  have : IsCyclotomicExtension {p ^ (0 + 1)} Rat K := by simpa using hcycl
  replace hζ : IsPrimitiveRoot ζ (p ^ (0 + 1)) := by simpa using hζ
  exact hζ.norm_toInteger_sub_one_of_prime_ne_two h

/--
lemma `prime_norm_toInteger_sub_one_of_prime_pow_ne_two` / 引理 `prime_norm_toInteger_sub_one_of_prime_pow_ne_two`

English:
lemma prime_norm_toInteger_sub_one_of_prime_pow_ne_two
  statement: [IsCyclotomicExtension {p ^ (k + 1)} Rat K]
  proof: by
  have := hζ.norm_toInteger_pow_sub_one_of_prime_pow_ne_two zero_le htwo
  simp only [pow_zero, pow_one] at this
  rw [this]
  exact Nat.prime_iff_prime_int.1 hp.out

中文:
引理 prime_norm_toInteger_sub_one_of_prime_pow_ne_two
  结论: [IsCyclotomicExtension {p ^ (k + 1)} Rat K]
  证明: by
  have := hζ.norm_toInteger_pow_sub_one_of_prime_pow_ne_two zero_le htwo
  simp only [pow_zero, pow_one] at this
  rw [this]
  exact Nat.prime_iff_prime_int.1 hp.out

Depends on / 依赖: Nat.prime_iff_prime_int, hp.out, norm_toInteger_pow_sub_one_of_prime_pow_ne_two, pow_one, pow_zero, prime_iff_prime_int, zero_le
-/
lemma prime_norm_toInteger_sub_one_of_prime_pow_ne_two [IsCyclotomicExtension {p ^ (k + 1)} Rat K]
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) (htwo : p ^ (k + 1) != 2) :
    Prime (Algebra.norm Int (hζ.toInteger - 1)) := by
  have := hζ.norm_toInteger_pow_sub_one_of_prime_pow_ne_two zero_le htwo
  simp only [pow_zero, pow_one] at this
  rw [this]
  exact Nat.prime_iff_prime_int.1 hp.out

/--
lemma `prime_norm_toInteger_sub_one_of_prime_ne_two` / 引理 `prime_norm_toInteger_sub_one_of_prime_ne_two`

English:
lemma prime_norm_toInteger_sub_one_of_prime_ne_two
  statement: [hcycl : IsCyclotomicExtension {p ^ (k + 1)} Rat K]
  proof: by
  have := hζ.norm_toInteger_sub_one_of_prime_ne_two hodd
  rw [this]
  exact Nat.prime_iff_prime_int.1 hp.out

中文:
引理 prime_norm_toInteger_sub_one_of_prime_ne_two
  结论: [hcycl : IsCyclotomicExtension {p ^ (k + 1)} Rat K]
  证明: by
  have := hζ.norm_toInteger_sub_one_of_prime_ne_two hodd
  rw [this]
  exact Nat.prime_iff_prime_int.1 hp.out

Depends on / 依赖: Nat.prime_iff_prime_int, hp.out, norm_toInteger_sub_one_of_prime_ne_two, prime_iff_prime_int
-/
lemma prime_norm_toInteger_sub_one_of_prime_ne_two [hcycl : IsCyclotomicExtension {p ^ (k + 1)} Rat K]
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) (hodd : p != 2) :
    Prime (Algebra.norm Int (hζ.toInteger - 1)) := by
  have := hζ.norm_toInteger_sub_one_of_prime_ne_two hodd
  rw [this]
  exact Nat.prime_iff_prime_int.1 hp.out

/--
lemma `prime_norm_toInteger_sub_one_of_prime_ne_two'` / 引理 `prime_norm_toInteger_sub_one_of_prime_ne_two'`

English:
lemma prime_norm_toInteger_sub_one_of_prime_ne_two'
  statement: [hcycl : IsCyclotomicExtension {p} Rat K]
  proof: by
  have : IsCyclotomicExtension {p ^ (0 + 1)} Rat K := by simpa using hcycl
  replace hζ : IsPrimitiveRoot ζ (p ^ (0 + 1)) := by simpa using hζ
  exact hζ.prime_norm_toInteger_sub_one_of_prime_ne_two hodd

中文:
引理 prime_norm_toInteger_sub_one_of_prime_ne_two'
  结论: [hcycl : IsCyclotomicExtension {p} Rat K]
  证明: by
  have : IsCyclotomicExtension {p ^ (0 + 1)} Rat K := by simpa using hcycl
  replace hζ : IsPrimitiveRoot ζ (p ^ (0 + 1)) := by simpa using hζ
  exact hζ.prime_norm_toInteger_sub_one_of_prime_ne_two hodd

Depends on / 依赖: IsCyclotomicExtension, IsPrimitiveRoot, prime_norm_toInteger_sub_one_of_prime_ne_two, replace
-/
lemma prime_norm_toInteger_sub_one_of_prime_ne_two' [hcycl : IsCyclotomicExtension {p} Rat K]
    (hζ : IsPrimitiveRoot ζ p) (hodd : p != 2) :
    Prime (Algebra.norm Int (hζ.toInteger - 1)) := by
  have : IsCyclotomicExtension {p ^ (0 + 1)} Rat K := by simpa using hcycl
  replace hζ : IsPrimitiveRoot ζ (p ^ (0 + 1)) := by simpa using hζ
  exact hζ.prime_norm_toInteger_sub_one_of_prime_ne_two hodd

/--
theorem `not_exists_int_prime_dvd_sub_of_prime_pow_ne_two` / 定理 `not_exists_int_prime_dvd_sub_of_prime_pow_ne_two`

English:
theorem not_exists_int_prime_dvd_sub_of_prime_pow_ne_two
  proof: by
  intro ⟨n, x, h⟩
  -- Let `pB` be the power basis of `𝓞 K` given by powers of `ζ`.
  let pB := hζ.integralPowerBasisOfPrimePow
  have hdim : pB.dim = p ^ k * (↑p - 1) := by
    simp [integralPowerBasisOfPrimePow_dim, pB, Nat.totient_prime_pow hp.1 (Nat.zero_lt_succ k)]
  replace hdim : 1 < pB.di

中文:
定理 not_exists_int_prime_dvd_sub_of_prime_pow_ne_two
  证明: by
  intro ⟨n, x, h⟩
  -- Let `pB` be the power basis of `𝓞 K` given by powers of `ζ`.
  let pB := hζ.integralPowerBasisOfPrimePow
  have hdim : pB.dim = p ^ k * (↑p - 1) := by
    simp [integralPowerBasisOfPrimePow_dim, pB, Nat.totient_prime_pow hp.1 (Nat.zero_lt_succ k)]
  replace hdim : 1 < pB.di
-/
theorem not_exists_int_prime_dvd_sub_of_prime_pow_ne_two
    [hcycl : IsCyclotomicExtension {p ^ (k + 1)} Rat K]
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) (htwo : p ^ (k + 1) != 2) :
    ¬(exists n : Int, (p : 𝓞 K) ∣ (hζ.toInteger - n : 𝓞 K)) := by
  intro ⟨n, x, h⟩
  -- Let `pB` be the power basis of `𝓞 K` given by powers of `ζ`.
  let pB := hζ.integralPowerBasisOfPrimePow
  have hdim : pB.dim = p ^ k * (↑p - 1) := by
    simp [integralPowerBasisOfPrimePow_dim, pB, Nat.totient_prime_pow hp.1 (Nat.zero_lt_succ k)]
  replace hdim : 1 < pB.dim := by
    rw [Nat.one_lt_iff_ne_zero_and_ne_one]; rw [hdim]
    refine ⟨by simp only [ne_eq, mul_eq_zero, NeZero.ne _, Nat.sub_eq_zero_iff_le, false_or,
      not_le, Nat.Prime.one_lt hp.out], ne_of_gt ?_⟩
    by_cases hk : k = 0
    · simp only [hk, zero_add, pow_one, pow_zero, one_mul, Nat.lt_sub_iff_add_lt,
        Nat.reduceAdd] at htwo ⊢
      exact htwo.symm.lt_of_le hp.1.two_le
    · exact one_lt_mul_of_lt_of_le (one_lt_pow₀ hp.1.one_lt hk)
        (have := Nat.Prime.two_le hp.out; by lia)
  rw [sub_eq_iff_eq_add] at h
  -- We are assuming that `ζ = n + p * x` for some integer `n` and `x : 𝓞 K`. Looking at the
  -- coordinates in the base `pB`, we obtain that `1` is a multiple of `p`, contradiction.
  replace h := pB.basis.ext_elem_iff.1 h ⟨1, hdim⟩
  have := pB.basis_eq_pow ⟨1, hdim⟩
  rw [hζ.integralPowerBasisOfPrimePow_gen] at this
  simp only [PowerBasis.coe_basis, pow_one] at this
  rw [← this]; rw [show pB.gen = pB.gen ^ (⟨1]; rw [hdim⟩ : Fin pB.dim).1 by simp]; rw [← pB.basis_eq_pow]; rw [pB.basis.repr_self_apply] at h
  simp only [↓reduceIte, map_add, Finsupp.coe_add, Pi.add_apply] at h
  rw [show (p : 𝓞 K) * x = (p : Int) • x by simp]; rw [← pB.basis.coord_apply]; rw [map_smul]; rw [← zsmul_one]; rw [← pB.basis.coord_apply]; rw [map_smul]; rw [show 1 = pB.gen ^ (⟨0]; rw [by lia⟩ : Fin pB.dim).1 by simp]; rw [← pB.basis_eq_pow]; rw [pB.basis.coord_apply]; rw [pB.basis.coord_apply]; rw [pB.basis.repr_self_apply] at h
  simp only [smul_eq_mul, Fin.mk.injEq, zero_ne_one, ↓reduceIte, mul_zero, add_zero] at h
  exact (Int.prime_iff_natAbs_prime.2 (by simp [hp.1])).not_dvd_one ⟨_, h⟩

/--
theorem `not_exists_int_prime_dvd_sub_of_prime_ne_two` / 定理 `not_exists_int_prime_dvd_sub_of_prime_ne_two`

English:
theorem not_exists_int_prime_dvd_sub_of_prime_ne_two
  proof: by
  refine not_exists_int_prime_dvd_sub_of_prime_pow_ne_two hζ (fun h => ?_)
  simp_all only [(@Nat.Prime.pow_eq_iff 2 p (k + 1) Nat.prime_two).mp (by assumption_mod_cast),
    pow_one, ne_eq]

中文:
定理 not_exists_int_prime_dvd_sub_of_prime_ne_two
  证明: by
  refine not_exists_int_prime_dvd_sub_of_prime_pow_ne_two hζ (fun h => ?_)
  simp_all only [(@Nat.Prime.pow_eq_iff 2 p (k + 1) Nat.prime_two).mp (by assumption_mod_cast),
    pow_one, ne_eq]

Depends on / 依赖: Nat.Prime.pow_eq_iff, Nat.prime_two, assumption_mod_cast, ne_eq, not_exists_int_prime_dvd_sub_of_prime_pow_ne_two, pow_eq_iff, pow_one, prime_two
-/
theorem not_exists_int_prime_dvd_sub_of_prime_ne_two
    [hcycl : IsCyclotomicExtension {p ^ (k + 1)} Rat K]
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) (hodd : p != 2) :
    ¬(exists n : Int, (p : 𝓞 K) ∣ (hζ.toInteger - n : 𝓞 K)) := by
  refine not_exists_int_prime_dvd_sub_of_prime_pow_ne_two hζ (fun h => ?_)
  simp_all only [(@Nat.Prime.pow_eq_iff 2 p (k + 1) Nat.prime_two).mp (by assumption_mod_cast),
    pow_one, ne_eq]

/--
theorem `not_exists_int_prime_dvd_sub_of_prime_ne_two'` / 定理 `not_exists_int_prime_dvd_sub_of_prime_ne_two'`

English:
theorem not_exists_int_prime_dvd_sub_of_prime_ne_two'
  proof: by
  have : IsCyclotomicExtension {p ^ (0 + 1)} Rat K := by simpa using hcycl
  replace hζ : IsPrimitiveRoot ζ (p ^ (0 + 1)) := by simpa using hζ
  exact not_exists_int_prime_dvd_sub_of_prime_ne_two hζ hodd

中文:
定理 not_exists_int_prime_dvd_sub_of_prime_ne_two'
  证明: by
  have : IsCyclotomicExtension {p ^ (0 + 1)} Rat K := by simpa using hcycl
  replace hζ : IsPrimitiveRoot ζ (p ^ (0 + 1)) := by simpa using hζ
  exact not_exists_int_prime_dvd_sub_of_prime_ne_two hζ hodd

Depends on / 依赖: IsCyclotomicExtension, IsPrimitiveRoot, not_exists_int_prime_dvd_sub_of_prime_ne_two, replace
-/
theorem not_exists_int_prime_dvd_sub_of_prime_ne_two'
    [hcycl : IsCyclotomicExtension {p} Rat K]
    (hζ : IsPrimitiveRoot ζ p) (hodd : p != 2) :
    ¬(exists n : Int, (p : 𝓞 K) ∣ (hζ.toInteger - n : 𝓞 K)) := by
  have : IsCyclotomicExtension {p ^ (0 + 1)} Rat K := by simpa using hcycl
  replace hζ : IsPrimitiveRoot ζ (p ^ (0 + 1)) := by simpa using hζ
  exact not_exists_int_prime_dvd_sub_of_prime_ne_two hζ hodd

/--
theorem `finite_quotient_span_sub_one` / 定理 `finite_quotient_span_sub_one`

English:
theorem finite_quotient_span_sub_one
  statement: [hcycl : IsCyclotomicExtension {p ^ (k + 1)} Rat K]
  proof: by
  have : NumberField K := IsCyclotomicExtension.numberField {p ^ (k + 1)} Rat K
  refine Ideal.finiteQuotientOfFreeOfNeBot _ (fun h => ?_)
  simp only [Ideal.span_singleton_eq_bot, sub_eq_zero] at h
  exact hζ.ne_one (one_lt_pow₀ hp.1.one_lt (Nat.zero_ne_add_one k).symm)
    (RingOfIntegers.ext_i

中文:
定理 finite_quotient_span_sub_one
  结论: [hcycl : IsCyclotomicExtension {p ^ (k + 1)} Rat K]
  证明: by
  have : NumberField K := IsCyclotomicExtension.numberField {p ^ (k + 1)} Rat K
  refine Ideal.finiteQuotientOfFreeOfNeBot _ (fun h => ?_)
  simp only [Ideal.span_singleton_eq_bot, sub_eq_zero] at h
  exact hζ.ne_one (one_lt_pow₀ hp.1.one_lt (Nat.zero_ne_add_one k).symm)
    (RingOfIntegers.ext_i

Depends on / 依赖: Ideal.finiteQuotientOfFreeOfNeBot, Ideal.span_singleton_eq_bot, IsCyclotomicExtension, IsCyclotomicExtension.numberField, Nat.zero_ne_add_one, NumberField, RingOfIntegers, RingOfIntegers.ext_iff, ext_iff, finiteQuotientOfFreeOfNeBot, ne_one, numberField, one_lt, span_singleton_eq_bot, sub_eq_zero, zero_ne_add_one
-/
theorem finite_quotient_span_sub_one [hcycl : IsCyclotomicExtension {p ^ (k + 1)} Rat K]
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) :
    Finite (𝓞 K ⧸ Ideal.span {hζ.toInteger - 1}) := by
  have : NumberField K := IsCyclotomicExtension.numberField {p ^ (k + 1)} Rat K
  refine Ideal.finiteQuotientOfFreeOfNeBot _ (fun h => ?_)
  simp only [Ideal.span_singleton_eq_bot, sub_eq_zero] at h
  exact hζ.ne_one (one_lt_pow₀ hp.1.one_lt (Nat.zero_ne_add_one k).symm)
    (RingOfIntegers.ext_iff.1 h)

/--
theorem `finite_quotient_span_sub_one'` / 定理 `finite_quotient_span_sub_one'`

English:
theorem finite_quotient_span_sub_one'
  statement: [hcycl : IsCyclotomicExtension {p} Rat K]
  proof: by
  have : IsCyclotomicExtension {p ^ (0 + 1)} Rat K := by simpa using hcycl
  replace hζ : IsPrimitiveRoot ζ (p ^ (0 + 1)) := by simpa using hζ
  exact hζ.finite_quotient_span_sub_one

中文:
定理 finite_quotient_span_sub_one'
  结论: [hcycl : IsCyclotomicExtension {p} Rat K]
  证明: by
  have : IsCyclotomicExtension {p ^ (0 + 1)} Rat K := by simpa using hcycl
  replace hζ : IsPrimitiveRoot ζ (p ^ (0 + 1)) := by simpa using hζ
  exact hζ.finite_quotient_span_sub_one

Depends on / 依赖: IsCyclotomicExtension, IsPrimitiveRoot, finite_quotient_span_sub_one, replace
-/
theorem finite_quotient_span_sub_one' [hcycl : IsCyclotomicExtension {p} Rat K]
    (hζ : IsPrimitiveRoot ζ p) :
    Finite (𝓞 K ⧸ Ideal.span {hζ.toInteger - 1}) := by
  have : IsCyclotomicExtension {p ^ (0 + 1)} Rat K := by simpa using hcycl
  replace hζ : IsPrimitiveRoot ζ (p ^ (0 + 1)) := by simpa using hζ
  exact hζ.finite_quotient_span_sub_one

/--
lemma `toInteger_sub_one_dvd_prime` / 引理 `toInteger_sub_one_dvd_prime`

English:
lemma toInteger_sub_one_dvd_prime
  statement: [hcycl : IsCyclotomicExtension {p ^ (k + 1)} Rat K]
  proof: by
  by_cases htwo : p ^ (k + 1) = 2
  · have ⟨hp2, hk⟩ := (Nat.Prime.pow_eq_iff Nat.prime_two).1 htwo
    simp only [add_eq_right] at hk
    have hζ' : ζ = -1 := by
      refine IsPrimitiveRoot.eq_neg_one_of_two_right ?_
      rwa [hk, zero_add, pow_one, hp2] at hζ
    replace hζ' : hζ.toInteger = 

中文:
引理 toInteger_sub_one_dvd_prime
  结论: [hcycl : IsCyclotomicExtension {p ^ (k + 1)} Rat K]
  证明: by
  by_cases htwo : p ^ (k + 1) = 2
  · have ⟨hp2, hk⟩ := (Nat.Prime.pow_eq_iff Nat.prime_two).1 htwo
    simp only [add_eq_right] at hk
    have hζ' : ζ = -1 := by
      refine IsPrimitiveRoot.eq_neg_one_of_two_right ?_
      rwa [hk, zero_add, pow_one, hp2] at hζ
    replace hζ' : hζ.toInteger = 

Depends on / 依赖: IsCyclotomicExtension, IsCyclotomicExtension.numberField, IsPrimitiveRoot, IsPrimitiveRoot.eq_neg_one_of_two_right, Nat.Prime.pow_eq_iff, Nat.prime_two, add_eq_right, eq_neg_one_of_two_right, norm_toInteger_pow_sub_one_of_prime_pow_ne, numberField, pow_eq_iff, pow_one, prime_two, replace, toInteger, zero_add
-/
lemma toInteger_sub_one_dvd_prime [hcycl : IsCyclotomicExtension {p ^ (k + 1)} Rat K]
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) : ((hζ.toInteger - 1)) ∣ p := by
  by_cases htwo : p ^ (k + 1) = 2
  · have ⟨hp2, hk⟩ := (Nat.Prime.pow_eq_iff Nat.prime_two).1 htwo
    simp only [add_eq_right] at hk
    have hζ' : ζ = -1 := by
      refine IsPrimitiveRoot.eq_neg_one_of_two_right ?_
      rwa [hk, zero_add, pow_one, hp2] at hζ
    replace hζ' : hζ.toInteger = -1 := by
      ext
      exact hζ'
    rw [hζ']; rw [hp2]
    exact ⟨-1, by ring⟩
  suffices (hζ.toInteger - 1) ∣ (p : Int) by simpa
  have := IsCyclotomicExtension.numberField {p ^ (k + 1)} Rat K
  have H := hζ.norm_toInteger_pow_sub_one_of_prime_pow_ne_two zero_le htwo
  rw [pow_zero]; rw [pow_one] at H
  rw [← Ideal.norm_dvd_iff]; rw [H]
  · simp
  · exact prime_norm_toInteger_sub_one_of_prime_pow_ne_two hζ htwo

/--
lemma `toInteger_sub_one_dvd_prime'` / 引理 `toInteger_sub_one_dvd_prime'`

English:
lemma toInteger_sub_one_dvd_prime'
  statement: [hcycl : IsCyclotomicExtension {p} Rat K]
  proof: by
  have : IsCyclotomicExtension {p ^ (0 + 1)} Rat K := by simpa using hcycl
  replace hζ : IsPrimitiveRoot ζ (p ^ (0 + 1)) := by simpa using hζ
  exact toInteger_sub_one_dvd_prime hζ

中文:
引理 toInteger_sub_one_dvd_prime'
  结论: [hcycl : IsCyclotomicExtension {p} Rat K]
  证明: by
  have : IsCyclotomicExtension {p ^ (0 + 1)} Rat K := by simpa using hcycl
  replace hζ : IsPrimitiveRoot ζ (p ^ (0 + 1)) := by simpa using hζ
  exact toInteger_sub_one_dvd_prime hζ

Depends on / 依赖: IsCyclotomicExtension, IsPrimitiveRoot, replace, toInteger_sub_one_dvd_prime
-/
lemma toInteger_sub_one_dvd_prime' [hcycl : IsCyclotomicExtension {p} Rat K]
    (hζ : IsPrimitiveRoot ζ p) : hζ.toInteger - 1 ∣ p := by
  have : IsCyclotomicExtension {p ^ (0 + 1)} Rat K := by simpa using hcycl
  replace hζ : IsPrimitiveRoot ζ (p ^ (0 + 1)) := by simpa using hζ
  exact toInteger_sub_one_dvd_prime hζ

/--
lemma `toInteger_sub_one_not_dvd_two` / 引理 `toInteger_sub_one_not_dvd_two`

English:
lemma toInteger_sub_one_not_dvd_two
  statement: [IsCyclotomicExtension {p ^ (k + 1)} Rat K]
  proof: fun h => by
  have : NumberField K := IsCyclotomicExtension.numberField {p ^ (k + 1)} Rat K
  replace h : hζ.toInteger - 1 ∣ (2 : Int) := by simp [h]
  rw [← Ideal.norm_dvd_iff]; rw [hζ.norm_toInteger_sub_one_of_prime_ne_two hodd] at h
· refine hodd (prime_dvd_prime_iff_eq ?_ ?_).1 ?_
    · exact Na

中文:
引理 toInteger_sub_one_not_dvd_two
  结论: [IsCyclotomicExtension {p ^ (k + 1)} Rat K]
  证明: fun h => by
  have : NumberField K := IsCyclotomicExtension.numberField {p ^ (k + 1)} Rat K
  replace h : hζ.toInteger - 1 ∣ (2 : Int) := by simp [h]
  rw [← Ideal.norm_dvd_iff]; rw [hζ.norm_toInteger_sub_one_of_prime_ne_two hodd] at h
· refine hodd (prime_dvd_prime_iff_eq ?_ ?_).1 ?_
    · exact Na

Depends on / 依赖: Ideal.norm_dvd_iff, Int.ofNat_dvd.mp, IsCyclotomicExtension, IsCyclotomicExtension.numberField, Nat.prime_iff, Nat.prime_iff_prime_int, Nat.prime_two, NumberField, norm_dvd_iff, norm_toInteger_sub_one_of_prime_ne_two, numberField, ofNat_dvd, prime_dvd_prime_iff_eq, prime_iff, prime_iff_prime_int, prime_two, replace, toInteger
-/
lemma toInteger_sub_one_not_dvd_two [IsCyclotomicExtension {p ^ (k + 1)} Rat K]
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) (hodd : p != 2) : ¬ hζ.toInteger - 1 ∣ 2 := fun h => by
  have : NumberField K := IsCyclotomicExtension.numberField {p ^ (k + 1)} Rat K
  replace h : hζ.toInteger - 1 ∣ (2 : Int) := by simp [h]
  rw [← Ideal.norm_dvd_iff]; rw [hζ.norm_toInteger_sub_one_of_prime_ne_two hodd] at h
· refine hodd (prime_dvd_prime_iff_eq ?_ ?_).1 ?_
    · exact Nat.prime_iff.1 hp.1
    · exact Nat.prime_iff.1 Nat.prime_two
    · exact Int.ofNat_dvd.mp h
  · rw [hζ.norm_toInteger_sub_one_of_prime_ne_two hodd]
    exact Nat.prime_iff_prime_int.1 hp.1

set_option backward.isDefEq.respectTransparency.types false in
open IntermediateField in
/--
theorem `prime_dvd_of_dvd_norm_sub_one` / 定理 `prime_dvd_of_dvd_norm_sub_one`

English:
theorem prime_dvd_of_dvd_norm_sub_one
  statement: {n : Nat} (hn : 2 <= n) {K : Type*}
  proof: by
  have : NeZero n := NeZero.of_gt hn
  obtain ⟨μ, hC, hμ, h⟩ :
      exists μ : Rat⟮ζ⟯, exists (_ : IsCyclotomicExtension {n} Rat Rat⟮ζ⟯), exists (hμ : IsPrimitiveRoot μ n),
      norm Int (hζ.toInteger - 1) = norm Int (hμ.toInteger - 1) ^ Module.finrank Rat⟮ζ⟯ K := by
    refine ⟨IntermediateFie

中文:
定理 prime_dvd_of_dvd_norm_sub_one
  结论: {n : 自然数} (hn : 2 <= n) {K : 类型}
  证明: by
  have : NeZero n := NeZero.of_gt hn
  obtain ⟨μ, hC, hμ, h⟩ :
      exists μ : Rat⟮ζ⟯, exists (_ : IsCyclotomicExtension {n} Rat Rat⟮ζ⟯), exists (hμ : IsPrimitiveRoot μ n),
      norm Int (hζ.toInteger - 1) = norm Int (hμ.toInteger - 1) ^ Module.finrank Rat⟮ζ⟯ K := by
    refine ⟨IntermediateFie

Depends on / 依赖: NeZero, NeZero.of_gt, of_gt, toInteger
-/
theorem prime_dvd_of_dvd_norm_sub_one {n : Nat} (hn : 2 <= n) {K : Type*}
    [Field K] [NumberField K] {ζ : K} {p : Nat} [hF : Fact (Nat.Prime p)] (hζ : IsPrimitiveRoot ζ n)
    (hp : haveI : NeZero n := NeZero.of_gt hn; (p : Int) ∣ norm Int (hζ.toInteger - 1)) :
    p ∣ n := by
  have : NeZero n := NeZero.of_gt hn
  obtain ⟨μ, hC, hμ, h⟩ :
      exists μ : Rat⟮ζ⟯, exists (_ : IsCyclotomicExtension {n} Rat Rat⟮ζ⟯), exists (hμ : IsPrimitiveRoot μ n),
      norm Int (hζ.toInteger - 1) = norm Int (hμ.toInteger - 1) ^ Module.finrank Rat⟮ζ⟯ K := by
    refine ⟨IntermediateField.AdjoinSimple.gen Rat ζ,
      intermediateField_adjoin_isCyclotomicExtension Rat hζ, coe_submonoidClass_iff.mp hζ, ?_⟩
    have : NumberField Rat⟮ζ⟯ := of_intermediateField _
    rw [norm_eq_iff Int (Sₘ := K) (Rₘ := Rat) le_rfl]; rw [map_sub]; rw [map_one]; rw [RingOfIntegers.map_mk]; rw [show ζ - 1 = algebraMap Rat⟮ζ⟯ K (IntermediateField.AdjoinSimple.gen Rat ζ - 1) by rfl]; rw [← norm_norm (S := Rat⟮ζ⟯)]; rw [Algebra.norm_algebraMap]; rw [map_pow]; rw [map_pow]; rw [← norm_localization Int
      (nonZeroDivisors Int) (Sₘ := Rat⟮ζ⟯)]; rw [map_sub (algebraMap _ _)]; rw [RingOfIntegers.map_mk]; rw [map_one]
  rw [h] at hp
  rsuffices ⟨q, hq, t, s, ht₁, ht₂, hs⟩ :
      exists q, q.Prime ∧ exists t s, t != 0 ∧ n = q ^ t ∧ (p : Int) ∣ (q : Int) ^ s := by
    obtain hn | hn := lt_or_eq_of_le hn
    · by_cases! h : exists q, q.Prime ∧ exists t, q ^ t = n
      · obtain ⟨q, hq, t, hn'⟩ := h
        have : Fact (Nat.Prime q) := ⟨hq⟩
        cases t with
        | zero => simp [← hn'] at hn
        | succ r =>
          rw [← hn'] at hC hμ
          refine ⟨q, hq, r + 1, Module.finrank (Rat⟮ζ⟯) K, r.add_one_ne_zero, hn'.symm, ?_⟩
          by_cases hq' : q = 2
          · cases r with
            | zero =>
                rw [← hn']; rw [hq']; rw [zero_add]; rw [pow_one] at hn
                exact hn.false.elim
            | succ k =>
                rw [hq'] at hC hμ ⊢
                rwa [hμ.norm_toInteger_sub_one_of_eq_two_pow] at hp
          · rwa [hμ.norm_toInteger_sub_one_of_prime_ne_two hq'] at hp
      · rw [IsPrimitiveRoot.norm_toInteger_sub_one_eq_one hμ hn, one_pow,
          Int.natCast_dvd_ofNat, Nat.dvd_one] at hp
        · exact (Nat.Prime.ne_one hF.out hp).elim
        · exact fun {p} a k => h p a k
    · rw [← hn] at hμ hC ⊢
      refine ⟨2, Nat.prime_two, 1, Module.finrank Rat⟮ζ⟯ K, one_ne_zero, by rw [pow_one], ?_⟩
      rwa [hμ.norm_toInteger_sub_one_of_eq_two, neg_eq_neg_one_mul, mul_pow, IsUnit.dvd_mul_left
        ((isUnit_pow_iff Module.finrank_pos.ne').mpr isUnit_neg_one)] at hp
  have : p = q := by
    rw [← Int.natCast_pow]; rw [Int.natCast_dvd_natCast] at hs
    exact (Nat.prime_dvd_prime_iff_eq hF.out hq).mp (hF.out.dvd_of_dvd_pow hs)
  rw [ht₂]; rw [this]
  exact dvd_pow_self _ ht₁

end IsPrimitiveRoot

section discr

namespace IsCyclotomicExtension.Rat

open nonZeroDivisors IsPrimitiveRoot

variable (K p k)
variable [CharZero K]

set_option backward.defeqAttrib.useBackward true in
/--
theorem `discr_prime_pow` / 定理 `discr_prime_pow`

English:
theorem discr_prime_pow
  given: [IsCyclotomicExtension {p ^ k} Rat K]
  proof: IsCyclotomicExtension.numberField {p ^ k} Rat K
    NumberField.discr K =
    (-1) ^ ((p ^ k).totient / 2) * p ^ (p ^ (k - 1) * ((p - 1) * k - 1)) := by
  have hζ := IsCyclotomicExtension.zeta_spec (p ^ k) Rat K
  have : NumberField K := IsCyclotomicExtension.numberField {p ^ k} Rat K
  let pB₁ := i

中文:
定理 discr_prime_pow
  条件: [IsCyclotomicExtension {p ^ k} Rat K]
  证明: IsCyclotomicExtension.numberField {p ^ k} Rat K
    NumberField.discr K =
    (-1) ^ ((p ^ k).totient / 2) * p ^ (p ^ (k - 1) * ((p - 1) * k - 1)) := by
  have hζ := IsCyclotomicExtension.zeta_spec (p ^ k) Rat K
  have : NumberField K := IsCyclotomicExtension.numberField {p ^ k} Rat K
  let pB₁ := i

Depends on / 依赖: IsCyclotomicExtension, IsCyclotomicExtension.numberField, numberField
-/
theorem discr_prime_pow [IsCyclotomicExtension {p ^ k} Rat K] :
    haveI : NumberField K := IsCyclotomicExtension.numberField {p ^ k} Rat K
    NumberField.discr K =
    (-1) ^ ((p ^ k).totient / 2) * p ^ (p ^ (k - 1) * ((p - 1) * k - 1)) := by
  have hζ := IsCyclotomicExtension.zeta_spec (p ^ k) Rat K
  have : NumberField K := IsCyclotomicExtension.numberField {p ^ k} Rat K
  let pB₁ := integralPowerBasisOfPrimePow hζ
  apply (algebraMap Int Rat).injective_int
  rw [← NumberField.discr_eq_discr _ pB₁.basis]; rw [← Algebra.discr_localizationLocalization Int Int⁰ K]
  convert!
    IsCyclotomicExtension.discr_prime_pow hζ (cyclotomic.irreducible_rat (NeZero.pos _)) using 1
  · have : pB₁.dim = (IsPrimitiveRoot.powerBasis Rat hζ).dim := by
      rw [← PowerBasis.finrank]; rw [← PowerBasis.finrank]
      exact RingOfIntegers.rank K
    rw [← Algebra.discr_reindex _ _ (finCongr this)]
    congr 1
    ext i
    simp_rw [Function.comp_apply, Module.Basis.localizationLocalization_apply, powerBasis_dim,
      PowerBasis.coe_basis, pB₁, integralPowerBasisOfPrimePow_gen]
    convert! ← ((IsPrimitiveRoot.powerBasis Rat hζ).basis_eq_pow i).symm using 1
  · simp_rw [algebraMap_int_eq, map_mul, map_pow, map_neg, map_one, map_natCast]

open Nat in
/--
theorem `discr_prime_pow_succ` / 定理 `discr_prime_pow_succ`

English:
theorem discr_prime_pow_succ
  given: [IsCyclotomicExtension {p ^ (k + 1)} Rat K]
  proof: IsCyclotomicExtension.numberField {p ^ (k + 1)} Rat K
    NumberField.discr K =
    (-1) ^ (p ^ k * (p - 1) / 2) * p ^ (p ^ k * ((p - 1) * (k + 1) - 1)) := by
  simpa [totient_prime_pow hp.out (succ_pos k)] using discr_prime_pow p (k + 1) K

中文:
定理 discr_prime_pow_succ
  条件: [IsCyclotomicExtension {p ^ (k + 1)} Rat K]
  证明: IsCyclotomicExtension.numberField {p ^ (k + 1)} Rat K
    NumberField.discr K =
    (-1) ^ (p ^ k * (p - 1) / 2) * p ^ (p ^ k * ((p - 1) * (k + 1) - 1)) := by
  simpa [totient_prime_pow hp.out (succ_pos k)] using discr_prime_pow p (k + 1) K

Depends on / 依赖: IsCyclotomicExtension, IsCyclotomicExtension.numberField, numberField
-/
theorem discr_prime_pow_succ [IsCyclotomicExtension {p ^ (k + 1)} Rat K] :
    haveI : NumberField K := IsCyclotomicExtension.numberField {p ^ (k + 1)} Rat K
    NumberField.discr K =
    (-1) ^ (p ^ k * (p - 1) / 2) * p ^ (p ^ k * ((p - 1) * (k + 1) - 1)) := by
  simpa [totient_prime_pow hp.out (succ_pos k)] using discr_prime_pow p (k + 1) K

/--
theorem `discr_prime` / 定理 `discr_prime`

English:
theorem discr_prime
  given: [IsCyclotomicExtension {p} Rat K]
  proof: IsCyclotomicExtension.numberField {p} Rat K
    NumberField.discr K = (-1) ^ ((p - 1) / 2) * p ^ (p - 2) := by
  have : IsCyclotomicExtension {p ^ (0 + 1)} Rat K := by
    rw [zero_add]; rw [pow_one]
    infer_instance
  rw [discr_prime_pow_succ p 0 K]
  simp [Nat.sub_sub]

中文:
定理 discr_prime
  条件: [IsCyclotomicExtension {p} Rat K]
  证明: IsCyclotomicExtension.numberField {p} Rat K
    NumberField.discr K = (-1) ^ ((p - 1) / 2) * p ^ (p - 2) := by
  have : IsCyclotomicExtension {p ^ (0 + 1)} Rat K := by
    rw [zero_add]; rw [pow_one]
    infer_instance
  rw [discr_prime_pow_succ p 0 K]
  simp [Nat.sub_sub]

Depends on / 依赖: IsCyclotomicExtension, IsCyclotomicExtension.numberField, numberField
-/
theorem discr_prime [IsCyclotomicExtension {p} Rat K] :
    haveI : NumberField K := IsCyclotomicExtension.numberField {p} Rat K
    NumberField.discr K = (-1) ^ ((p - 1) / 2) * p ^ (p - 2) := by
  have : IsCyclotomicExtension {p ^ (0 + 1)} Rat K := by
    rw [zero_add]; rw [pow_one]
    infer_instance
  rw [discr_prime_pow_succ p 0 K]
  simp [Nat.sub_sub]

variable (n) [hn : NeZero n]

set_option backward.isDefEq.respectTransparency false in
open Algebra IntermediateField Nat in
/--
theorem `discr` / 定理 `discr`

English:
theorem discr
  given: [hK : IsCyclotomicExtension {n} Rat K]
  proof: IsCyclotomicExtension.numberField {n} Rat K
    discr K = (-1) ^ (φ n / 2) * (n ^ φ n / ∏ p in n.primeFactors, p ^ (φ n / (p - 1))) := by
  have : NumberField K := IsCyclotomicExtension.numberField {n} Rat K
  rw [← Int.sign_mul_natAbs (NumberField.discr K)]; rw [sign_discr]; rw [nrComplexPlaces_eq_

中文:
定理 discr
  条件: [hK : IsCyclotomicExtension {n} Rat K]
  证明: IsCyclotomicExtension.numberField {n} Rat K
    discr K = (-1) ^ (φ n / 2) * (n ^ φ n / ∏ p in n.primeFactors, p ^ (φ n / (p - 1))) := by
  have : NumberField K := IsCyclotomicExtension.numberField {n} Rat K
  rw [← Int.sign_mul_natAbs (NumberField.discr K)]; rw [sign_discr]; rw [nrComplexPlaces_eq_

Depends on / 依赖: IsCyclotomicExtension, IsCyclotomicExtension.numberField, numberField
-/
theorem discr [hK : IsCyclotomicExtension {n} Rat K] :
    haveI : NumberField K := IsCyclotomicExtension.numberField {n} Rat K
    discr K = (-1) ^ (φ n / 2) * (n ^ φ n / ∏ p in n.primeFactors, p ^ (φ n / (p - 1))) := by
  have : NumberField K := IsCyclotomicExtension.numberField {n} Rat K
  rw [← Int.sign_mul_natAbs (NumberField.discr K)]; rw [sign_discr]; rw [nrComplexPlaces_eq_totient_div_two n]
  congr
  induction n using Nat.recOnPrimeCoprime generalizing K hn with
  | zero => exact (neZero_zero_iff_false.mp hn).elim
  | prime_pow p k hp =>
    have : Fact (Nat.Prime p) := ⟨hp⟩
    rw [discr_prime_pow p k K]
    cases k with
    | zero => simp
    | succ k =>
      simpa only [Int.reduceNeg, add_tsub_cancel_right, Int.natAbs_mul, Int.natAbs_pow,
        IsUnit.neg_iff, isUnit_one, Int.natAbs_of_isUnit, one_pow, Int.natAbs_natCast, one_mul]
        using! (Nat.prime_pow_pow_totient_ediv_prod hp k.zero_lt_succ).symm
  | coprime n₁ n₂ hn₁ hn₂ h hK₁ hK₂ =>
    have : NeZero n₁ := NeZero.of_gt hn₁
    have : NeZero n₂ := NeZero.of_gt hn₂
    let ζ := zeta (n₁ * n₂) Rat K
    have hζ := zeta_spec (n₁ * n₂) Rat K
    have hζ₁ := hζ.pow (NeZero.pos _) (a := n₂) (b := n₁) (by rw [mul_comm])
    have := hζ₁.intermediateField_adjoin_isCyclotomicExtension Rat
    have hζ₁' : IsPrimitiveRoot (AdjoinSimple.gen Rat (ζ ^ n₂)) n₁ :=
      IsPrimitiveRoot.coe_submonoidClass_iff.mp hζ₁
    replace hK₁ := @hK₁ Rat⟮ζ ^ n₂⟯ _ _ _ _ (of_intermediateField _)
    have hζ₂ := hζ.pow (NeZero.pos _) (a := n₁) (b := n₂) rfl
    have := hζ₂.intermediateField_adjoin_isCyclotomicExtension Rat
    have hζ₂' : IsPrimitiveRoot (AdjoinSimple.gen Rat (ζ ^ n₁)) n₂ :=
      IsPrimitiveRoot.coe_submonoidClass_iff.mp hζ₂
    replace hK₂ := @hK₂ Rat⟮ζ ^ n₁⟯ _ _ _ _ (of_intermediateField _)
    have : IsGalois Rat Rat⟮ζ ^ n₂⟯ := isGalois {n₁} Rat _
    have h_top : Rat⟮ζ ^ n₂⟯ ⊔ Rat⟮ζ ^ n₁⟯ = ⊤ := by
      have : IsCyclotomicExtension {n₁ * n₂} Rat (⊤ : IntermediateField Rat K) :=
          hK.equiv _ _ _ topEquiv.symm
      have : IsCyclotomicExtension {n₁ * n₂} Rat ↥(Rat⟮ζ ^ n₂⟯ ⊔ Rat⟮ζ ^ n₁⟯) := by
        rw [← Nat.Coprime.lcm_eq_mul h]
        exact isCyclotomicExtension_lcm_sup Rat K n₁ n₂ Rat⟮ζ ^ n₂⟯ Rat⟮ζ ^ n₁⟯
      exact isCyclotomicExtension_eq {n₁ * n₂} Rat K _ _
    have h_cpr : IsCoprime (discr Rat⟮ζ ^ n₂⟯) (discr Rat⟮ζ ^ n₁⟯) := by
      rw [Int.isCoprime_iff_nat_coprime]; rw [hK₁]; rw [hK₂]
      refine Coprime.coprime_div_left ?_ (prod_primeFactors_pow_totient_ediv_dvd (NeZero.pos _))
      refine Coprime.coprime_div_right ?_ (prod_primeFactors_pow_totient_ediv_dvd (NeZero.pos _))
      exact Coprime.pow_left _ (Coprime.pow_right _ h)
    have h_dsj : Rat⟮ζ ^ n₂⟯.LinearDisjoint Rat⟮ζ ^ n₁⟯ :=
      linearDisjoint_of_isGalois_isCoprime_discr _ _ _ h_cpr
    have h_div₁ := prod_primeFactors_pow_totient_ediv_dvd n₁.pos_of_neZero
    have h_div₂ := prod_primeFactors_pow_totient_ediv_dvd n₂.pos_of_neZero
    rw [natAbs_discr_eq_natAbs_discr_pow_mul_natAbs_discr_pow K Rat⟮ζ ^ n₂⟯ Rat⟮ζ ^ n₁⟯ h_dsj h_top
      (isCoprime_differentIdeal_of_isCoprime_discr _ h_cpr)]; rw [hK₁]; rw [hK₂]; rw [finrank n₁ Rat⟮ζ ^ n₂⟯]; rw [finrank n₂ Rat⟮ζ ^ n₁⟯]; rw [Nat.div_pow h_div₁]; rw [Nat.div_pow h_div₂]; rw [← Nat.mul_div_mul_comm (pow_dvd_pow_of_dvd h_div₁ n₂.totient)
      (pow_dvd_pow_of_dvd h_div₂ n₁.totient)]; rw [primeFactors_mul (NeZero.ne _) (NeZero.ne _)]; rw [Finset.prod_union h.disjoint_primeFactors]; rw [← Finset.prod_pow]; rw [← Finset.prod_pow]
    have {n p : Nat} (hp : p in n.primeFactors) : p - 1 ∣ n.totient :=
      p.totient_prime (prime_of_mem_primeFactors hp) ▸ totient_dvd_of_dvd (b := n)
 dvd_of_mem_primeFactors hp
    simp_rw +contextual [← pow_mul, Nat.div_mul_right_comm (this _), Nat.totient_mul h]
    rw [mul_pow]; rw [mul_comm n₂.totient]

/--
theorem `natAbs_discr` / 定理 `natAbs_discr`

English:
theorem natAbs_discr
  given: [hK : IsCyclotomicExtension {n} Rat K]
  proof: IsCyclotomicExtension.numberField {n} Rat K
    (NumberField.discr K).natAbs = n ^ φ n / ∏ p in n.primeFactors, p ^ (φ n / (p - 1)) := by
  have : NumberField K := IsCyclotomicExtension.numberField {n} Rat K
  rw [discr n K]; rw [Int.natAbs_mul]; rw [Int.natAbs_pow]; rw [Int.natAbs_neg]; rw [Int.nat

中文:
定理 natAbs_discr
  条件: [hK : IsCyclotomicExtension {n} Rat K]
  证明: IsCyclotomicExtension.numberField {n} Rat K
    (NumberField.discr K).natAbs = n ^ φ n / ∏ p in n.primeFactors, p ^ (φ n / (p - 1)) := by
  have : NumberField K := IsCyclotomicExtension.numberField {n} Rat K
  rw [discr n K]; rw [Int.natAbs_mul]; rw [Int.natAbs_pow]; rw [Int.natAbs_neg]; rw [Int.nat

Depends on / 依赖: IsCyclotomicExtension, IsCyclotomicExtension.numberField, numberField
-/
theorem natAbs_discr [hK : IsCyclotomicExtension {n} Rat K] :
    haveI : NumberField K := IsCyclotomicExtension.numberField {n} Rat K
    (NumberField.discr K).natAbs = n ^ φ n / ∏ p in n.primeFactors, p ^ (φ n / (p - 1)) := by
  have : NumberField K := IsCyclotomicExtension.numberField {n} Rat K
  rw [discr n K]; rw [Int.natAbs_mul]; rw [Int.natAbs_pow]; rw [Int.natAbs_neg]; rw [Int.natAbs_one]; rw [one_pow]; rw [one_mul]; rw [Int.natAbs_ediv_of_dvd]; rw [Int.natAbs_pow]; rw [Int.natAbs_natCast]; rw [Int.natAbs_natCast]
  rw [← Nat.cast_pow]; rw [Int.natCast_dvd_natCast]
  exact Nat.prod_primeFactors_pow_totient_ediv_dvd (NeZero.pos _)

open IntermediateField Algebra Nat in
/--
theorem `adjoin_singleton_eq_top_aux` / 定理 `adjoin_singleton_eq_top_aux`

English:
theorem adjoin_singleton_eq_top_aux
  statement: [NumberField K] (F₁ F₂ : IntermediateField Rat K)
  proof: by
  have h_cpr : IsCoprime (NumberField.discr F₁) (NumberField.discr F₂) := by
    rw [Int.isCoprime_iff_nat_coprime]; rw [natAbs_discr n₁ F₁]; rw [natAbs_discr n₂ F₂]
    refine Coprime.coprime_div_left ?_ (prod_primeFactors_pow_totient_ediv_dvd (NeZero.pos _))
    refine Coprime.coprime_div_right

中文:
定理 adjoin_singleton_eq_top_aux
  结论: [NumberField K] (F₁ F₂ : 整数ermediateField Rat K)
  证明: by
  have h_cpr : IsCoprime (NumberField.discr F₁) (NumberField.discr F₂) := by
    rw [Int.isCoprime_iff_nat_coprime]; rw [natAbs_discr n₁ F₁]; rw [natAbs_discr n₂ F₂]
    refine Coprime.coprime_div_left ?_ (prod_primeFactors_pow_totient_ediv_dvd (NeZero.pos _))
    refine Coprime.coprime_div_right
-/
private theorem adjoin_singleton_eq_top_aux [NumberField K] (F₁ F₂ : IntermediateField Rat K)
    {n₁ n₂ : Nat} [NeZero n₁] [NeZero n₂] [IsCyclotomicExtension {n₁} Rat F₁]
    [IsCyclotomicExtension {n₂} Rat F₂] {ζ₁ : F₁} (hζ₁ : IsPrimitiveRoot ζ₁ n₁)
    (h₁ : Int[hζ₁.toInteger] = ⊤) {ζ₂ : F₂} (hζ₂ : IsPrimitiveRoot ζ₂ n₂)
    (h₂ : Int[hζ₂.toInteger] = ⊤) (h : n₁.Coprime n₂) (htop : F₁ ⊔ F₂ = ⊤)
    {ζ : K} (hζ : IsPrimitiveRoot ζ (n₁ * n₂)) :
    Int[hζ.toInteger] = ⊤ := by
  have h_cpr : IsCoprime (NumberField.discr F₁) (NumberField.discr F₂) := by
    rw [Int.isCoprime_iff_nat_coprime]; rw [natAbs_discr n₁ F₁]; rw [natAbs_discr n₂ F₂]
    refine Coprime.coprime_div_left ?_ (prod_primeFactors_pow_totient_ediv_dvd (NeZero.pos _))
    refine Coprime.coprime_div_right ?_ (prod_primeFactors_pow_totient_ediv_dvd (NeZero.pos _))
    exact Coprime.pow_left _ (Coprime.pow_right _ h)
  have h_disj : F₁.LinearDisjoint F₂ := by
    have : IsGalois Rat F₁ := IsCyclotomicExtension.isGalois {n₁} Rat F₁
    apply linearDisjoint_of_isGalois_isCoprime_discr
    exact h_cpr
  replace hζ₁ : IsPrimitiveRoot hζ₁.toInteger n₁ := hζ₁.toInteger_isPrimitiveRoot
  replace hζ₁ := hζ₁.map_of_injective (FaithfulSMul.algebraMap_injective (𝓞 F₁) (𝓞 K))
  replace hζ₂ : IsPrimitiveRoot hζ₂.toInteger n₂ := hζ₂.toInteger_isPrimitiveRoot
  replace hζ₂ := hζ₂.map_of_injective (FaithfulSMul.algebraMap_injective (𝓞 F₂) (𝓞 K))
  rw [← IsDedekindDomain.adjoin_union_eq_top_of_isCoprime_differentialIdeal Int (𝓞 K) (𝓞 F₁)
    (𝓞 F₂) h_disj _ _ h₁ h₂]; rw [Set.image_singleton]; rw [Set.image_singleton]; rw [Set.singleton_union]
  · refine (IsPrimitiveRoot.adjoin_pair_eq Int hζ₁ hζ₂ (NeZero.ne _) (NeZero.ne _) ?_).symm
    rw [Nat.Coprime.lcm_eq_mul h]
    exact toInteger_isPrimitiveRoot hζ
  · simp [← sup_toSubalgebra_of_left, htop]
  · exact isCoprime_differentIdeal_of_isCoprime_discr _ h_cpr

variable {n K}

set_option backward.isDefEq.respectTransparency false in
open IntermediateField Algebra in
/--
theorem `adjoin_singleton_eq_top` / 定理 `adjoin_singleton_eq_top`

English:
theorem adjoin_singleton_eq_top
  statement: [hK : IsCyclotomicExtension {n} Rat K]
  proof: by
  have : NumberField K := IsCyclotomicExtension.numberField {n} Rat K
  induction n using Nat.recOnPrimeCoprime generalizing K hn with
  | zero => exact (neZero_zero_iff_false.mp hn).elim
  | prime_pow p k hp =>
    have : Fact (p.Prime) := ⟨hp⟩
    rw [← hζ.integralPowerBasisOfPrimePow.adjoin_ge

中文:
定理 adjoin_singleton_eq_top
  结论: [hK : IsCyclotomicExtension {n} Rat K]
  证明: by
  have : NumberField K := IsCyclotomicExtension.numberField {n} Rat K
  induction n using Nat.recOnPrimeCoprime generalizing K hn with
  | zero => exact (neZero_zero_iff_false.mp hn).elim
  | prime_pow p k hp =>
    have : Fact (p.Prime) := ⟨hp⟩
    rw [← hζ.integralPowerBasisOfPrimePow.adjoin_ge

Depends on / 依赖: IsCyclotomicExtension, IsCyclotomicExtension.numberField, Nat.recOnPrimeCoprime, NeZero, NeZero.of_gt, NeZero.pos, NumberField, adjoin_gen_eq_top, coprime, generalizing, integralPowerBasisOfPrimePow, integralPowerBasisOfPrimePow.adjoin_gen_eq_top, integralPowerBasisOfPrimePow_gen, neZero_zero_iff_false, neZero_zero_iff_false.mp, numberField, of_gt, p.Prime, prime_pow, recOnPrimeCoprime
-/
theorem adjoin_singleton_eq_top [hK : IsCyclotomicExtension {n} Rat K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) :
    Int[hζ.toInteger] = ⊤ := by
  have : NumberField K := IsCyclotomicExtension.numberField {n} Rat K
  induction n using Nat.recOnPrimeCoprime generalizing K hn with
  | zero => exact (neZero_zero_iff_false.mp hn).elim
  | prime_pow p k hp =>
    have : Fact (p.Prime) := ⟨hp⟩
    rw [← hζ.integralPowerBasisOfPrimePow.adjoin_gen_eq_top]; rw [hζ.integralPowerBasisOfPrimePow_gen]
  | coprime n₁ n₂ hn₁ hn₂ h hK₁ hK₂ =>
    have : NeZero n₁ := NeZero.of_gt hn₁
    have : NeZero n₂ := NeZero.of_gt hn₂
    have hζ₁ := hζ.pow (NeZero.pos _) (a := n₂) (b := n₁) (by rw [mul_comm])
    have := hζ₁.intermediateField_adjoin_isCyclotomicExtension Rat
    replace hζ₁ : IsPrimitiveRoot (AdjoinSimple.gen Rat (ζ ^ n₂)) n₁ :=
      IsPrimitiveRoot.coe_submonoidClass_iff.mp hζ₁
    replace hK₁ := @hK₁ Rat⟮ζ ^ n₂⟯ _ _ _ _ (AdjoinSimple.gen _ _) hζ₁ (of_intermediateField _)
    have hζ₂ := hζ.pow (NeZero.pos _) (a := n₁) (b := n₂) rfl
    have := hζ₂.intermediateField_adjoin_isCyclotomicExtension Rat
    replace hζ₂ : IsPrimitiveRoot (AdjoinSimple.gen Rat (ζ ^ n₁)) n₂ :=
      IsPrimitiveRoot.coe_submonoidClass_iff.mp hζ₂
    replace hK₂ := @hK₂ Rat⟮ζ ^ n₁⟯ _ _ _ _ (AdjoinSimple.gen _ _) hζ₂ (of_intermediateField _)
    have h_top : Rat⟮ζ ^ n₂⟯ ⊔ Rat⟮ζ ^ n₁⟯ = ⊤ := by
      have : IsCyclotomicExtension {n₁ * n₂} Rat (⊤ : IntermediateField Rat K) :=
          hK.equiv _ _ _ topEquiv.symm
      have : IsCyclotomicExtension {n₁ * n₂} Rat ↥(Rat⟮ζ ^ n₂⟯ ⊔ Rat⟮ζ ^ n₁⟯) := by
        rw [← Nat.Coprime.lcm_eq_mul h]
        exact isCyclotomicExtension_lcm_sup Rat K n₁ n₂ Rat⟮ζ ^ n₂⟯ Rat⟮ζ ^ n₁⟯
      exact isCyclotomicExtension_eq {n₁ * n₂} Rat K _ _
    exact adjoin_singleton_eq_top_aux K Rat⟮ζ ^ n₂⟯ Rat⟮ζ ^ n₁⟯ hζ₁ hK₁ hζ₂ hK₂ h h_top hζ

set_option backward.isDefEq.respectTransparency.types false in
open Algebra in
/--
theorem `isIntegralClosure_adjoin_singleton` / 定理 `isIntegralClosure_adjoin_singleton`

English:
theorem isIntegralClosure_adjoin_singleton
  statement: {ζ : K} [hcycl : IsCyclotomicExtension {n} Rat K]
  proof: by
  constructor
  · exact FaithfulSMul.algebraMap_injective _ K
  · intro _
    have := congr_arg (Subalgebra.map (IsScalarTower.toAlgHom Int (𝓞 K) K))
      (adjoin_singleton_eq_top hζ)
    simp only [AlgHom.map_adjoin_singleton, IsScalarTower.coe_toAlgHom', RingOfIntegers.map_mk,
      Algebra.ma

中文:
定理 isIntegralClosure_adjoin_singleton
  结论: {ζ : K} [hcycl : IsCyclotomicExtension {n} Rat K]
  证明: by
  constructor
  · exact FaithfulSMul.algebraMap_injective _ K
  · intro _
    have := congr_arg (Subalgebra.map (IsScalarTower.toAlgHom Int (𝓞 K) K))
      (adjoin_singleton_eq_top hζ)
    simp only [AlgHom.map_adjoin_singleton, IsScalarTower.coe_toAlgHom', RingOfIntegers.map_mk,
      Algebra.ma

Depends on / 依赖: AlgHom, AlgHom.map_adjoin_singleton, Algebra, Algebra.map_top, FaithfulSMul, FaithfulSMul.algebraMap_injective, IsIntegralClosure, IsIntegralClosure.isIntegral_iff, IsScalarTower, IsScalarTower.coe_toAlgHom, IsScalarTower.toAlgHom, RingOfIntegers, RingOfIntegers.map_mk, SetLike, SetLike.mem_coe, Subalgebra, Subalgebra.map, adjoin_singleton_eq_top, algebraMap_injective, coe_toAlgHom
-/
theorem isIntegralClosure_adjoin_singleton {ζ : K} [hcycl : IsCyclotomicExtension {n} Rat K]
    (hζ : IsPrimitiveRoot ζ n) :
    IsIntegralClosure (Int[ζ]) Int K := by
  constructor
  · exact FaithfulSMul.algebraMap_injective _ K
  · intro _
    have := congr_arg (Subalgebra.map (IsScalarTower.toAlgHom Int (𝓞 K) K))
      (adjoin_singleton_eq_top hζ)
    simp only [AlgHom.map_adjoin_singleton, IsScalarTower.coe_toAlgHom', RingOfIntegers.map_mk,
      Algebra.map_top] at this
    simp [IsIntegralClosure.isIntegral_iff (A := 𝓞 K), this, ← SetLike.mem_coe]

variable (n)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `cyclotomicRing_isIntegralClosure` / 定理 `cyclotomicRing_isIntegralClosure`

English:
theorem cyclotomicRing_isIntegralClosure
  proof: by
  have hζ := zeta_spec n Rat (CyclotomicField n Rat)
  refine ⟨IsFractionRing.injective _ _, fun {x} => ⟨fun h => ⟨⟨x, ?_⟩, rfl⟩, ?_⟩⟩
  · obtain ⟨y, rfl⟩ := (isIntegralClosure_adjoin_singleton hζ).isIntegral_iff.1 h
    refine adjoin_mono ?_ y.2
    simp only [Set.singleton_subset_iff, Set.mem_o

中文:
定理 cyclotomicRing_isIntegralClosure
  证明: by
  have hζ := zeta_spec n Rat (CyclotomicField n Rat)
  refine ⟨IsFractionRing.injective _ _, fun {x} => ⟨fun h => ⟨⟨x, ?_⟩, rfl⟩, ?_⟩⟩
  · obtain ⟨y, rfl⟩ := (isIntegralClosure_adjoin_singleton hζ).isIntegral_iff.1 h
    refine adjoin_mono ?_ y.2
    simp only [Set.singleton_subset_iff, Set.mem_o

Depends on / 依赖: CyclotomicField, IsCyclotomicExtension, IsCyclotomicExtension.integral, IsFractionRing, IsFractionRing.injective, IsIntegral, IsIntegral.algebraMap, Set.mem_ofPred_eq, Set.singleton_subset_iff, adjoin_mono, algebraMap, injective, integral, isIntegral, isIntegralClosure_adjoin_singleton, isIntegral_iff, mem_ofPred_eq, pow_eq_one, singleton_subset_iff, zeta_spec
-/
theorem cyclotomicRing_isIntegralClosure :
    IsIntegralClosure (CyclotomicRing n Int Rat) Int (CyclotomicField n Rat) := by
  have hζ := zeta_spec n Rat (CyclotomicField n Rat)
  refine ⟨IsFractionRing.injective _ _, fun {x} => ⟨fun h => ⟨⟨x, ?_⟩, rfl⟩, ?_⟩⟩
  · obtain ⟨y, rfl⟩ := (isIntegralClosure_adjoin_singleton hζ).isIntegral_iff.1 h
    refine adjoin_mono ?_ y.2
    simp only [Set.singleton_subset_iff, Set.mem_ofPred_eq]
    exact hζ.pow_eq_one
  · rintro ⟨y, rfl⟩
    exact IsIntegral.algebraMap ((IsCyclotomicExtension.integral {n} Int _).isIntegral _)

end IsCyclotomicExtension.Rat

namespace IsPrimitiveRoot

variable [NeZero n] [CharZero K]

/-- The algebra isomorphism `adjoin ℤ {ζ} ≃ₐ[ℤ] (𝓞 K)`, where `ζ` is a primitive `n`-th root of
unity and `K` is an `n`-th cyclotomic extension of `ℚ`. -/
@[simps!]
/--
Definition of `adjoinEquivRingOfIntegers` / `adjoinEquivRingOfIntegers` 的定义

English:
definition adjoinEquivRingOfIntegers
  signature: [IsCyclotomicExtension {n} Rat K]
  body: let _ := isIntegralClosure_adjoin_singleton hζ
  IsIntegralClosure.equiv Int (adjoin Int ({ζ} : Set K)) K (𝓞 K)

中文:
定义 adjoinEquivRingOfIntegers
  签名: [IsCyclotomicExtension {n} Rat K]
  定义体: let _ := isIntegralClosure_adjoin_singleton hζ
  IsIntegralClosure.equiv Int (adjoin Int ({ζ} : Set K)) K (𝓞 K)

Depends on / 依赖: IsIntegralClosure, IsIntegralClosure.equiv, adjoin, isIntegralClosure_adjoin_singleton
-/
noncomputable def adjoinEquivRingOfIntegers [IsCyclotomicExtension {n} Rat K]
    (hζ : IsPrimitiveRoot ζ n) :
    adjoin Int ({ζ} : Set K) ≃ₐ[Int] 𝓞 K :=
  let _ := isIntegralClosure_adjoin_singleton hζ
  IsIntegralClosure.equiv Int (adjoin Int ({ζ} : Set K)) K (𝓞 K)

/--
Instance `_root_.IsCyclotomicExtension.ringOfIntegers` / 实例 `_root_.IsCyclotomicExtension.ringOfIntegers`

English:
instance _root_.IsCyclotomicExtension.ringOfIntegers
  signature: [IsCyclotomicExtension {n} Rat K]
  body: let _ := (zeta_spec n Rat K).adjoin_isCyclotomicExtension Int
  IsCyclotomicExtension.equiv _ Int _ (zeta_spec n Rat K).adjoinEquivRingOfIntegers

中文:
实例 _root_.IsCyclotomicExtension.ringOfIntegers
  签名: [IsCyclotomicExtension {n} Rat K]
  定义体: let _ := (zeta_spec n Rat K).adjoin_isCyclotomicExtension Int
  IsCyclotomicExtension.equiv _ Int _ (zeta_spec n Rat K).adjoinEquivRingOfIntegers

Depends on / 依赖: IsCyclotomicExtension, IsCyclotomicExtension.equiv, adjoinEquivRingOfIntegers, adjoin_isCyclotomicExtension, zeta_spec
-/
instance _root_.IsCyclotomicExtension.ringOfIntegers [IsCyclotomicExtension {n} Rat K] :
    IsCyclotomicExtension {n} Int (𝓞 K) :=
  let _ := (zeta_spec n Rat K).adjoin_isCyclotomicExtension Int
  IsCyclotomicExtension.equiv _ Int _ (zeta_spec n Rat K).adjoinEquivRingOfIntegers

/--
Definition of `integralPowerBasis` / `integralPowerBasis` 的定义

English:
definition integralPowerBasis
  signature: [IsCyclotomicExtension {n} Rat K]
  body: (Algebra.adjoin.powerBasis' (hζ.isIntegral (NeZero.pos _))).map hζ.adjoinEquivRingOfIntegers

@[simp]

中文:
定义 integralPowerBasis
  签名: [IsCyclotomicExtension {n} Rat K]
  定义体: (Algebra.adjoin.powerBasis' (hζ.isIntegral (NeZero.pos _))).map hζ.adjoinEquivRingOfIntegers

@[simp]

Depends on / 依赖: Algebra, Algebra.adjoin.powerBasis, NeZero, NeZero.pos, adjoin, adjoinEquivRingOfIntegers, isIntegral, powerBasis
-/
noncomputable def integralPowerBasis [IsCyclotomicExtension {n} Rat K]
    (hζ : IsPrimitiveRoot ζ n) : PowerBasis Int (𝓞 K) :=
  (Algebra.adjoin.powerBasis' (hζ.isIntegral (NeZero.pos _))).map hζ.adjoinEquivRingOfIntegers

@[simp]
/--
theorem `integralPowerBasis_gen` / 定理 `integralPowerBasis_gen`

English:
theorem integralPowerBasis_gen
  given: [hcycl : IsCyclotomicExtension {n} Rat K] (hζ : IsPrimitiveRoot ζ n)
  proof: Subtype.ext show algebraMap _ K hζ.integralPowerBasis.gen = _ by
    rw [integralPowerBasis]; rw [PowerBasis.map_gen]; rw [adjoin.powerBasis'_gen]
    simp

@[simp]

中文:
定理 integralPowerBasis_gen
  条件: [hcycl : IsCyclotomicExtension {n} Rat K] (hζ : IsPrimitiveRoot ζ n)
  证明: Subtype.ext show algebraMap _ K hζ.integralPowerBasis.gen = _ by
    rw [integralPowerBasis]; rw [PowerBasis.map_gen]; rw [adjoin.powerBasis'_gen]
    simp

@[simp]

Depends on / 依赖: PowerBasis, PowerBasis.map_gen, Subtype, Subtype.ext, _gen, adjoin, adjoin.powerBasis, algebraMap, integralPowerBasis, integralPowerBasis.gen, map_gen, powerBasis
-/
theorem integralPowerBasis_gen [hcycl : IsCyclotomicExtension {n} Rat K] (hζ : IsPrimitiveRoot ζ n) :
    hζ.integralPowerBasis.gen = hζ.toInteger :=
Subtype.ext show algebraMap _ K hζ.integralPowerBasis.gen = _ by
    rw [integralPowerBasis]; rw [PowerBasis.map_gen]; rw [adjoin.powerBasis'_gen]
    simp

@[simp]
/--
theorem `integralPowerBasis_dim` / 定理 `integralPowerBasis_dim`

English:
theorem integralPowerBasis_dim
  given: [IsCyclotomicExtension {n} Rat K] (hζ : IsPrimitiveRoot ζ n)
  proof: by
  simp [integralPowerBasis, ← cyclotomic_eq_minpoly hζ (NeZero.pos _), natDegree_cyclotomic]

中文:
定理 integralPowerBasis_dim
  条件: [IsCyclotomicExtension {n} Rat K] (hζ : IsPrimitiveRoot ζ n)
  证明: by
  simp [integralPowerBasis, ← cyclotomic_eq_minpoly hζ (NeZero.pos _), natDegree_cyclotomic]

Depends on / 依赖: NeZero, NeZero.pos, cyclotomic_eq_minpoly, integralPowerBasis, natDegree_cyclotomic
-/
theorem integralPowerBasis_dim [IsCyclotomicExtension {n} Rat K] (hζ : IsPrimitiveRoot ζ n) :
    hζ.integralPowerBasis.dim = φ n := by
  simp [integralPowerBasis, ← cyclotomic_eq_minpoly hζ (NeZero.pos _), natDegree_cyclotomic]

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `subOneIntegralPowerBasis` / `subOneIntegralPowerBasis` 的定义

English:
definition subOneIntegralPowerBasis
  signature: [IsCyclotomicExtension {n} Rat K]
  body: PowerBasis.ofAdjoinEqTop'
    (RingOfIntegers.isIntegral ⟨ζ- 1, (hζ.isIntegral (NeZero.pos _)).sub isIntegral_one⟩) (by
    refine hζ.integralPowerBasis.adjoin_eq_top_of_gen_mem_adjoin ?_
    convert! Subalgebra.add_mem _ (self_mem_adjoin_singleton Int _) (Subalgebra.one_mem _)
    simp [RingOfInteg

中文:
定义 subOneIntegralPowerBasis
  签名: [IsCyclotomicExtension {n} Rat K]
  定义体: PowerBasis.ofAdjoinEqTop'
    (RingOfIntegers.isIntegral ⟨ζ- 1, (hζ.isIntegral (NeZero.pos _)).sub isIntegral_one⟩) (by
    refine hζ.integralPowerBasis.adjoin_eq_top_of_gen_mem_adjoin ?_
    convert! Subalgebra.add_mem _ (self_mem_adjoin_singleton Int _) (Subalgebra.one_mem _)
    simp [RingOfInteg

Depends on / 依赖: NeZero, NeZero.pos, PowerBasis, PowerBasis.ofAdjoinEqTop, RingOfIntegers, RingOfIntegers.ext_iff, RingOfIntegers.isIntegral, Subalgebra, Subalgebra.add_mem, Subalgebra.one_mem, add_mem, adjoin_eq_top_of_gen_mem_adjoin, convert, ext_iff, integralPowerBasis, integralPowerBasis.adjoin_eq_top_of_gen_mem_adjoin, integralPowerBasis_gen, isIntegral, isIntegral_one, ofAdjoinEqTop
-/
noncomputable def subOneIntegralPowerBasis [IsCyclotomicExtension {n} Rat K]
    (hζ : IsPrimitiveRoot ζ n) : PowerBasis Int (𝓞 K) :=
  PowerBasis.ofAdjoinEqTop'
    (RingOfIntegers.isIntegral ⟨ζ- 1, (hζ.isIntegral (NeZero.pos _)).sub isIntegral_one⟩) (by
    refine hζ.integralPowerBasis.adjoin_eq_top_of_gen_mem_adjoin ?_
    convert! Subalgebra.add_mem _ (self_mem_adjoin_singleton Int _) (Subalgebra.one_mem _)
    simp [RingOfIntegers.ext_iff, integralPowerBasis_gen, toInteger])

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `subOneIntegralPowerBasis_gen` / 定理 `subOneIntegralPowerBasis_gen`

English:
theorem subOneIntegralPowerBasis_gen
  statement: [IsCyclotomicExtension {n} Rat K]
  proof: by
  simp [subOneIntegralPowerBasis]

中文:
定理 subOneIntegralPowerBasis_gen
  结论: [IsCyclotomicExtension {n} Rat K]
  证明: by
  simp [subOneIntegralPowerBasis]

Depends on / 依赖: subOneIntegralPowerBasis
-/
theorem subOneIntegralPowerBasis_gen [IsCyclotomicExtension {n} Rat K]
    (hζ : IsPrimitiveRoot ζ n) :
    hζ.subOneIntegralPowerBasis.gen =
      ⟨ζ - 1, Subalgebra.sub_mem _ (hζ.isIntegral (NeZero.pos _)) (Subalgebra.one_mem _)⟩ := by
  simp [subOneIntegralPowerBasis]

end IsPrimitiveRoot

end discr

end PowerBasis

section NumberField

open Units

/--
theorem `NumberField.Units.dvd_torsionOrder_of_isPrimitiveRoot` / 定理 `NumberField.Units.dvd_torsionOrder_of_isPrimitiveRoot`

English:
theorem NumberField.Units.dvd_torsionOrder_of_isPrimitiveRoot
  statement: [NeZero n] {ζ : K}
  proof: by
  replace hζ := (hζ.toInteger_isPrimitiveRoot).isUnit_unit (NeZero.ne n)
  convert! orderOf_dvd_natCard (⟨(hζ.isUnit (NeZero.ne n)).unit, ?_⟩ : torsion K)
  · rw [Subgroup.orderOf_mk]
    exact hζ.eq_orderOf
  · refine (CommGroup.mem_torsion _).mpr ⟨n, NeZero.pos n, ?_⟩
    rw [isPeriodicPt_mul_i

中文:
定理 NumberField.Units.dvd_torsionOrder_of_isPrimitiveRoot
  结论: [NeZero n] {ζ : K}
  证明: by
  replace hζ := (hζ.toInteger_isPrimitiveRoot).isUnit_unit (NeZero.ne n)
  convert! orderOf_dvd_natCard (⟨(hζ.isUnit (NeZero.ne n)).unit, ?_⟩ : torsion K)
  · rw [Subgroup.orderOf_mk]
    exact hζ.eq_orderOf
  · refine (CommGroup.mem_torsion _).mpr ⟨n, NeZero.pos n, ?_⟩
    rw [isPeriodicPt_mul_i

Depends on / 依赖: CommGroup, CommGroup.mem_torsion, NeZero, NeZero.ne, NeZero.pos, Subgroup, Subgroup.orderOf_mk, convert, eq_orderOf, isPeriodicPt_mul_iff_pow_eq_one, isUnit, isUnit_unit, mem_torsion, orderOf_dvd_natCard, orderOf_mk, pow_eq_one, replace, toInteger_isPrimitiveRoot, torsion
-/
theorem NumberField.Units.dvd_torsionOrder_of_isPrimitiveRoot [NeZero n] {ζ : K}
    (hζ : IsPrimitiveRoot ζ n) : n ∣ torsionOrder K := by
  replace hζ := (hζ.toInteger_isPrimitiveRoot).isUnit_unit (NeZero.ne n)
  convert! orderOf_dvd_natCard (⟨(hζ.isUnit (NeZero.ne n)).unit, ?_⟩ : torsion K)
  · rw [Subgroup.orderOf_mk]
    exact hζ.eq_orderOf
  · refine (CommGroup.mem_torsion _).mpr ⟨n, NeZero.pos n, ?_⟩
    rw [isPeriodicPt_mul_iff_pow_eq_one]
    exact hζ.pow_eq_one

/--
theorem `IsCyclotomicExtension.Rat.torsionOrder_eq` / 定理 `IsCyclotomicExtension.Rat.torsionOrder_eq`

English:
theorem IsCyclotomicExtension.Rat.torsionOrder_eq
  statement: [NeZero n] [NumberField K]
  proof: by
  have hζ := hK.zeta_spec
  -- We first prove that `K` contains a primitive root of order `torsionOrder K`
  obtain ⟨μ, hμ⟩ : exists μ : torsion K, orderOf μ = torsionOrder K := by
    exact IsCyclic.exists_ofOrder_eq_natCard
  rw [← IsPrimitiveRoot.iff_orderOf]; rw [← IsPrimitiveRoot.coe_submono

中文:
定理 IsCyclotomicExtension.Rat.torsionOrder_eq
  结论: [NeZero n] [NumberField K]
  证明: by
  have hζ := hK.zeta_spec
  -- We first prove that `K` contains a primitive root of order `torsionOrder K`
  obtain ⟨μ, hμ⟩ : exists μ : torsion K, orderOf μ = torsionOrder K := by
    exact IsCyclic.exists_ofOrder_eq_natCard
  rw [← IsPrimitiveRoot.iff_orderOf]; rw [← IsPrimitiveRoot.coe_submono

Depends on / 依赖: hK.zeta_spec, zeta_spec
-/
theorem IsCyclotomicExtension.Rat.torsionOrder_eq [NeZero n] [NumberField K]
    [hK : IsCyclotomicExtension {n} Rat K] :
    torsionOrder K = if Even n then n else 2 * n := by
  have hζ := hK.zeta_spec
  -- We first prove that `K` contains a primitive root of order `torsionOrder K`
  obtain ⟨μ, hμ⟩ : exists μ : torsion K, orderOf μ = torsionOrder K := by
    exact IsCyclic.exists_ofOrder_eq_natCard
  rw [← IsPrimitiveRoot.iff_orderOf]; rw [← IsPrimitiveRoot.coe_submonoidClass_iff]; rw [← IsPrimitiveRoot.coe_units_iff] at hμ
  replace hμ := hμ.map_of_injective (FaithfulSMul.algebraMap_injective (𝓞 K) K)
  -- Thus, `K` contains a primitive root of order `l = lcm (n, torsionOrder K)`.
  have h := hζ.pow_mul_pow_lcm hμ (NeZero.ne _) (torsionOrder_ne_zero K)
  have : NeZero (n.lcm (torsionOrder K)) :=
NeZero.of_pos Nat.lcm_pos_iff.mpr ⟨NeZero.pos n, torsionOrder_pos K⟩
  -- and therefore `K` is the `l`-th cyclotomic field
  have : IsCyclotomicExtension {n.lcm (torsionOrder K)} Rat K := by
    have := hK.union_of_isPrimitiveRoot _ _ _ h
    rwa [Set.union_comm, ← IsCyclotomicExtension.iff_union_of_dvd] at this
    exact ⟨n.lcm (torsionOrder K), by simp, NeZero.ne _, Nat.dvd_lcm_left _ _⟩
  -- We deduce the identity `φ(n) = φ(lcm (n, torsionOrder K))`.
have h_main := (IsCyclotomicExtension.Rat.finrank n K).symm.trans
    (IsCyclotomicExtension.Rat.finrank (n.lcm (torsionOrder K)) K)
  obtain hn | hn := Nat.even_or_odd n
  · rw [if_pos hn]
    apply dvd_antisymm
    · have := hn.eq_of_totient_eq_totient (Nat.dvd_lcm_left _ _) h_main
      rwa [eq_comm, Nat.lcm_eq_left_iff_dvd] at this
    · exact dvd_torsionOrder_of_isPrimitiveRoot hζ
  · rw [if_neg (Nat.not_even_iff_odd.mpr hn)]
    have := (Nat.eq_or_eq_of_totient_eq_totient (Nat.dvd_lcm_left _ _) h_main).resolve_left ?_
    · rw [this, eq_comm, Nat.lcm_eq_right_iff_dvd]
      exact dvd_torsionOrder_of_isPrimitiveRoot hζ
    · rw [eq_comm, Nat.lcm_eq_left_iff_dvd]
      exact fun h => Nat.not_even_iff_odd.mpr (Odd.of_dvd_nat hn h) (even_torsionOrder K)

end NumberField
