/-
Copyright (c) 2020 Kenji Nakagawa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenji Nakagawa, Anne Baanen, Filippo A. E. Nuccio, Yongle Hu
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.LocalProperties.IntegrallyClosed

/-!
# Dedekind domains

This file defines an equivalent notion of a Dedekind domain (or Dedekind ring),
namely a Noetherian integral domain where the localization at every nonzero prime ideal is a DVR.

## Main definitions

- `IsDedekindDomainDvr` alternatively defines a Dedekind domain as an integral domain that
  is Noetherian, and the localization at every nonzero prime ideal is a DVR.

## Main results
- `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain` shows that
  `IsDedekindDomain` implies the localization at each nonzero prime ideal is a DVR.
- `IsDedekindDomain.isDedekindDomainDvr` is one direction of the equivalence of definitions
  of a Dedekind domain

## Implementation notes

The definitions that involve a field of fractions choose a canonical field of fractions,
but are independent of that choice. The `..._iff` lemmas express this independence.

Often, definitions assume that Dedekind domains are not fields. We found it more practical
to add a `(h : ¬ IsField A)` assumption whenever this is explicitly needed.

## References

* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Fröhlich, *Algebraic Number Theory*][cassels1967algebraic]
* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992]

## Tags

dedekind domain, dedekind ring
-/

public section


variable (A : Type*) [CommRing A] [IsDomain A]

open scoped nonZeroDivisors Polynomial

/--
Definition of `IsDedekindDomainDvr` / `IsDedekindDomainDvr` 的定义

English:
class IsDedekindDomainDvr
  parameters: : Prop extends IsNoetherian A A where
  extends: IsNoetherian A A
  axioms and operations (1):
    - is_dvr_at_nonzero_prime : forall P != (⊥ : Ideal A), forall _ : P.IsPrime, IsDiscreteValuationRing (Localization.AtPrime P)

中文:
类 是DedekindDomainDvr
  参数: : 命题 extends 是Noether A A where
  继承: 是Noether A A
  公理与运算 (1 个):
    - is_dvr_at_nonzero_prime : 对任意 P != (⊥ : 理想 A), 对任意 _ : P.是素, 是离散赋值环 (Localization.AtPrime P)
-/
class IsDedekindDomainDvr : Prop extends IsNoetherian A A where
  is_dvr_at_nonzero_prime : forall P != (⊥ : Ideal A), forall _ : P.IsPrime,
    IsDiscreteValuationRing (Localization.AtPrime P)

/--
theorem `Ring.DimensionLEOne.localization` / 定理 `Ring.DimensionLEOne.localization`

English:
theorem Ring.DimensionLEOne.localization
  statement: {R : Type*} (Rₘ : Type*) [CommRing R] [IsDomain R]
  proof: ⟨by
  intro p hp0 hpp
  refine Ideal.isMaximal_def.mpr ⟨hpp.ne_top, Ideal.maximal_of_no_maximal fun P hpP hPm => ?_⟩
  have hpP' : (⟨p, hpp⟩ : { p : Ideal Rₘ // p.IsPrime }) < ⟨P, hPm.isPrime⟩ := hpP
  rw [← (IsLocalization.orderIsoOfPrime M Rₘ).lt_iff_lt] at hpP'
  refine h.not_lt_lt ⊥ (p.under R) 

中文:
定理 环.维数不超过一.localization
  结论: {R : 类型} (Rₘ : 类型) [交换环 R] [是整环 R]
  证明: ⟨by
  intro p hp0 hpp
  refine Ideal.isMaximal_def.mpr ⟨hpp.ne_top, Ideal.maximal_of_no_maximal fun P hpP hPm => ?_⟩
  have hpP' : (⟨p, hpp⟩ : { p : Ideal Rₘ // p.IsPrime }) < ⟨P, hPm.isPrime⟩ := hpP
  rw [← (IsLocalization.orderIsoOfPrime M Rₘ).lt_iff_lt] at hpP'
  refine h.not_lt_lt ⊥ (p.under R) 

Depends on / 依赖: Ideal.isMaximal_def.mpr, Ideal.maximal_of_no_maximal, IsLocalization, IsLocalization.bot_lt_under_prime, IsLocalization.orderIsoOfPrime, IsPrime, P.under, bot_lt_under_prime, h.not_lt_lt, hPm.isPrime, hpp.ne_top, isMaximal_def, isPrime, lt_iff_lt, maximal_of_no_maximal, ne_top, not_lt_lt, orderIsoOfPrime, p.IsPrime, p.under
-/
theorem Ring.DimensionLEOne.localization {R : Type*} (Rₘ : Type*) [CommRing R] [IsDomain R]
    [CommRing Rₘ] [Algebra R Rₘ] {M : Submonoid R} [IsLocalization M Rₘ] (hM : M <= R⁰)
    [h : Ring.DimensionLEOne R] : Ring.DimensionLEOne Rₘ := ⟨by
  intro p hp0 hpp
  refine Ideal.isMaximal_def.mpr ⟨hpp.ne_top, Ideal.maximal_of_no_maximal fun P hpP hPm => ?_⟩
  have hpP' : (⟨p, hpp⟩ : { p : Ideal Rₘ // p.IsPrime }) < ⟨P, hPm.isPrime⟩ := hpP
  rw [← (IsLocalization.orderIsoOfPrime M Rₘ).lt_iff_lt] at hpP'
  refine h.not_lt_lt ⊥ (p.under R) (P.under R) ⟨?_, hpP'⟩
  exact IsLocalization.bot_lt_under_prime _ _ hM _ hp0⟩

set_option linter.overlappingInstances false

/--
theorem `IsLocalization.isDedekindDomain` / 定理 `IsLocalization.isDedekindDomain`

English:
theorem IsLocalization.isDedekindDomain
  statement: [IsDedekindDomain A] {M : Submonoid A} (hM : M <= A⁰)
  proof: by
  have h : forall y : M, IsUnit (algebraMap A (FractionRing A) y) := by
    rintro ⟨y, hy⟩
    exact IsUnit.mk0 _ (mt IsFractionRing.to_map_eq_zero_iff.mp (nonZeroDivisors.ne_zero (hM hy)))
  let : Algebra Aₘ (FractionRing A) := RingHom.toAlgebra (IsLocalization.lift h)
  have : IsScalarTower A A

中文:
定理 是Localization.isDedekindDomain
  结论: [是Dedekind整环 A] {M : 子幺半群 A} (hM : M <= A⁰)
  证明: by
  have h : forall y : M, IsUnit (algebraMap A (FractionRing A) y) := by
    rintro ⟨y, hy⟩
    exact IsUnit.mk0 _ (mt IsFractionRing.to_map_eq_zero_iff.mp (nonZeroDivisors.ne_zero (hM hy)))
  let : Algebra Aₘ (FractionRing A) := RingHom.toAlgebra (IsLocalization.lift h)
  have : IsScalarTower A A

Depends on / 依赖: Algebra, FractionRing, IsFractionRing, IsFractionRing.isFractionRing_of_isDomain_of_isLocalization, IsFractionRing.to_map_eq_zero_iff.mp, IsLocalization, IsLocalization.lift, IsLocalization.lift_eq, IsScalarTower, IsScalarTower.of_algebraMap_eq, IsUnit, IsUnit.mk0, RingHom, RingHom.toAlgebra, algebraMap, isFractionRing_of_isDomain_of_isLocalization, lift_eq, ne_zero, nonZeroDivisors, nonZeroDivisors.ne_zero
-/
theorem IsLocalization.isDedekindDomain [IsDedekindDomain A] {M : Submonoid A} (hM : M <= A⁰)
    (Aₘ : Type*) [CommRing Aₘ] [IsDomain Aₘ] [Algebra A Aₘ] [IsLocalization M Aₘ] :
    IsDedekindDomain Aₘ := by
  have h : forall y : M, IsUnit (algebraMap A (FractionRing A) y) := by
    rintro ⟨y, hy⟩
    exact IsUnit.mk0 _ (mt IsFractionRing.to_map_eq_zero_iff.mp (nonZeroDivisors.ne_zero (hM hy)))
  let : Algebra Aₘ (FractionRing A) := RingHom.toAlgebra (IsLocalization.lift h)
  have : IsScalarTower A Aₘ (FractionRing A) :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.lift_eq h x).symm
  have : IsFractionRing Aₘ (FractionRing A) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization M _ _
  refine (isDedekindDomain_iff _ (FractionRing A)).mpr ⟨?_, ?_, ?_, ?_⟩
  · infer_instance
  · exact IsLocalization.isNoetherianRing M _ inferInstance
  · exact Ring.DimensionLEOne.localization Aₘ hM
  · intro x hx
    obtain ⟨⟨y, y_mem⟩, hy⟩ := hx.exists_multiple_integral_of_isLocalization M _
    obtain ⟨z, hz⟩ := (isIntegrallyClosed_iff _).mp IsDedekindRing.toIsIntegralClosure hy
    refine ⟨IsLocalization.mk' Aₘ z ⟨y, y_mem⟩, (IsLocalization.lift_mk'_spec _ _ _ _).mpr ?_⟩
    rw [hz]; rw [← Algebra.smul_def]
    rfl

/--
theorem `IsLocalization.AtPrime.isDedekindDomain` / 定理 `IsLocalization.AtPrime.isDedekindDomain`

English:
theorem IsLocalization.AtPrime.isDedekindDomain
  statement: [IsDedekindDomain A] (P : Ideal A) [P.IsPrime]
  proof: IsLocalization.isDedekindDomain A P.primeCompl_le_nonZeroDivisors Aₘ

中文:
定理 是Localization.AtPrime.isDedekindDomain
  结论: [是Dedekind整环 A] (P : 理想 A) [P.是素]
  证明: IsLocalization.isDedekindDomain A P.primeCompl_le_nonZeroDivisors Aₘ

Depends on / 依赖: IsLocalization, IsLocalization.isDedekindDomain, P.primeCompl_le_nonZeroDivisors, isDedekindDomain, primeCompl_le_nonZeroDivisors
-/
theorem IsLocalization.AtPrime.isDedekindDomain [IsDedekindDomain A] (P : Ideal A) [P.IsPrime]
    (Aₘ : Type*) [CommRing Aₘ] [IsDomain Aₘ] [Algebra A Aₘ] [IsLocalization.AtPrime Aₘ P] :
    IsDedekindDomain Aₘ :=
  IsLocalization.isDedekindDomain A P.primeCompl_le_nonZeroDivisors Aₘ

/--
Instance `Localization.AtPrime.isDedekindDomain` / 实例 `Localization.AtPrime.isDedekindDomain`

English:
instance Localization.AtPrime.isDedekindDomain
  signature: [IsDedekindDomain A] (P : Ideal A) [P.IsPrime]
  body: IsLocalization.AtPrime.isDedekindDomain A P _

中文:
实例 Localization.AtPrime.isDedekindDomain
  签名: [是Dedekind整环 A] (P : 理想 A) [P.是素]
  定义体: IsLocalization.AtPrime.isDedekindDomain A P _

Depends on / 依赖: AtPrime, IsLocalization, IsLocalization.AtPrime.isDedekindDomain, isDedekindDomain
-/
instance Localization.AtPrime.isDedekindDomain [IsDedekindDomain A] (P : Ideal A) [P.IsPrime] :
    IsDedekindDomain (Localization.AtPrime P) :=
  IsLocalization.AtPrime.isDedekindDomain A P _

/--
theorem `IsLocalization.AtPrime.not_isField` / 定理 `IsLocalization.AtPrime.not_isField`

English:
theorem IsLocalization.AtPrime.not_isField
  statement: {P : Ideal A} (hP : P != ⊥) [pP : P.IsPrime] (Aₘ : Type*)
  proof: by
  intro h
  let := h.toField
  obtain ⟨x, x_mem, x_ne⟩ := P.ne_bot_iff.mp hP
  exact
    (IsLocalRing.maximalIdeal.isMaximal _).ne_top
      (Ideal.eq_top_of_isUnit_mem _
        ((IsLocalization.AtPrime.to_map_mem_maximal_iff Aₘ P _).mpr x_mem)
        (isUnit_iff_ne_zero.mpr
          ((map_ne_

中文:
定理 是Localization.AtPrime.not_isField
  结论: {P : 理想 A} (hP : P != ⊥) [pP : P.是素] (Aₘ : 类型)
  证明: by
  intro h
  let := h.toField
  obtain ⟨x, x_mem, x_ne⟩ := P.ne_bot_iff.mp hP
  exact
    (IsLocalRing.maximalIdeal.isMaximal _).ne_top
      (Ideal.eq_top_of_isUnit_mem _
        ((IsLocalization.AtPrime.to_map_mem_maximal_iff Aₘ P _).mpr x_mem)
        (isUnit_iff_ne_zero.mpr
          ((map_ne_

Depends on / 依赖: AtPrime, Ideal.eq_top_of_isUnit_mem, IsLocalRing, IsLocalRing.maximalIdeal.isMaximal, IsLocalization, IsLocalization.AtPrime.to_map_mem_maximal_iff, IsLocalization.injective, P.ne_bot_iff.mp, P.primeCompl_le_nonZeroDivisors, algebraMap, eq_top_of_isUnit_mem, h.toField, injective, isMaximal, isUnit_iff_ne_zero, isUnit_iff_ne_zero.mpr, map_ne_zero_iff, maximalIdeal, ne_bot_iff, ne_top
-/
theorem IsLocalization.AtPrime.not_isField {P : Ideal A} (hP : P != ⊥) [pP : P.IsPrime] (Aₘ : Type*)
    [CommRing Aₘ] [Algebra A Aₘ] [IsLocalization.AtPrime Aₘ P] : ¬ IsField Aₘ := by
  intro h
  let := h.toField
  obtain ⟨x, x_mem, x_ne⟩ := P.ne_bot_iff.mp hP
  exact
    (IsLocalRing.maximalIdeal.isMaximal _).ne_top
      (Ideal.eq_top_of_isUnit_mem _
        ((IsLocalization.AtPrime.to_map_mem_maximal_iff Aₘ P _).mpr x_mem)
        (isUnit_iff_ne_zero.mpr
          ((map_ne_zero_iff (algebraMap A Aₘ)
                (IsLocalization.injective Aₘ P.primeCompl_le_nonZeroDivisors)).mpr
            x_ne)))

/--
theorem `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain` / 定理 `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain`

English:
theorem IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
  statement: [IsDedekindDomain A]
  proof: by
  let : IsNoetherianRing Aₘ :=
    IsLocalization.isNoetherianRing P.primeCompl _ IsDedekindRing.toIsNoetherian
  let : IsLocalRing Aₘ := IsLocalization.AtPrime.isLocalRing Aₘ P
  have hnf := IsLocalization.AtPrime.not_isField A hP Aₘ
  exact
    ((IsDiscreteValuationRing.TFAE Aₘ hnf).out 0 2).mp

中文:
定理 是Localization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
  结论: [是Dedekind整环 A]
  证明: by
  let : IsNoetherianRing Aₘ :=
    IsLocalization.isNoetherianRing P.primeCompl _ IsDedekindRing.toIsNoetherian
  let : IsLocalRing Aₘ := IsLocalization.AtPrime.isLocalRing Aₘ P
  have hnf := IsLocalization.AtPrime.not_isField A hP Aₘ
  exact
    ((IsDiscreteValuationRing.TFAE Aₘ hnf).out 0 2).mp

Depends on / 依赖: AtPrime, IsDedekindRing, IsDedekindRing.toIsNoetherian, IsDiscreteValuationRing, IsDiscreteValuationRing.TFAE, IsLocalRing, IsLocalization, IsLocalization.AtPrime.isDedekindDomain, IsLocalization.AtPrime.isLocalRing, IsLocalization.AtPrime.not_isField, IsLocalization.isNoetherianRing, IsNoetherianRing, P.primeCompl, isDedekindDomain, isLocalRing, isNoetherianRing, not_isField, primeCompl, toIsNoetherian
-/
theorem IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain [IsDedekindDomain A]
    {P : Ideal A} (hP : P != ⊥) [pP : P.IsPrime] (Aₘ : Type*) [CommRing Aₘ] [IsDomain Aₘ]
    [Algebra A Aₘ] [IsLocalization.AtPrime Aₘ P] : IsDiscreteValuationRing Aₘ := by
  let : IsNoetherianRing Aₘ :=
    IsLocalization.isNoetherianRing P.primeCompl _ IsDedekindRing.toIsNoetherian
  let : IsLocalRing Aₘ := IsLocalization.AtPrime.isLocalRing Aₘ P
  have hnf := IsLocalization.AtPrime.not_isField A hP Aₘ
  exact
    ((IsDiscreteValuationRing.TFAE Aₘ hnf).out 0 2).mpr
      (IsLocalization.AtPrime.isDedekindDomain A P _)

/--
Instance `IsDedekindDomain.isDedekindDomainDvr` / 实例 `IsDedekindDomain.isDedekindDomainDvr`

English:
instance IsDedekindDomain.isDedekindDomainDvr
  signature: [IsDedekindDomain A]
  body: fun _ hP _ =>
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hP _

中文:
实例 是Dedekind整环.isDedekindDomainDvr
  签名: [是Dedekind整环 A]
  定义体: fun _ hP _ =>
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hP _
-/
instance IsDedekindDomain.isDedekindDomainDvr [IsDedekindDomain A] : IsDedekindDomainDvr A where
  is_dvr_at_nonzero_prime := fun _ hP _ =>
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hP _

/--
Instance `IsDedekindDomainDvr.ring_dimensionLEOne` / 实例 `IsDedekindDomainDvr.ring_dimensionLEOne`

English:
instance IsDedekindDomainDvr.ring_dimensionLEOne
  signature: [h : IsDedekindDomainDvr A]
  body: by
    intro p hp hpp
    rcases p.exists_le_maximal (Ideal.IsPrime.ne_top hpp) with ⟨q, hq, hpq⟩
    let f := (IsLocalization.orderIsoOfPrime q.primeCompl (Localization.AtPrime q)).symm
    let P := f ⟨p, hpp, hpq.disjoint_compl_left⟩
    let Q := f ⟨q, hq.isPrime, Set.disjoint_left.mpr fun _ a => 

中文:
实例 是DedekindDomainDvr.ring_dimensionLEOne
  签名: [h : 是DedekindDomainDvr A]
  定义体: by
    intro p hp hpp
    rcases p.exists_le_maximal (Ideal.IsPrime.ne_top hpp) with ⟨q, hq, hpq⟩
    let f := (IsLocalization.orderIsoOfPrime q.primeCompl (Localization.AtPrime q)).symm
    let P := f ⟨p, hpp, hpq.disjoint_compl_left⟩
    let Q := f ⟨q, hq.isPrime, Set.disjoint_left.mpr fun _ a => 

Depends on / 依赖: AtPrime, Function, Function.Injective, Ideal.IsPrime.ne_top, Injective, IsLocalization, IsLocalization.injective, IsLocalization.orderIsoOfPrime, IsPrime, Localization, Localization.AtPrime, Set.disjoint_left.mpr, algebraMap, disjoint_compl_left, disjoint_left, exists_le_maximal, hpq.disjoint_compl_left, hq.isPrime, injective, isPrime
-/
instance IsDedekindDomainDvr.ring_dimensionLEOne [h : IsDedekindDomainDvr A] :
    Ring.DimensionLEOne A where
  maximalOfPrime := by
    intro p hp hpp
    rcases p.exists_le_maximal (Ideal.IsPrime.ne_top hpp) with ⟨q, hq, hpq⟩
    let f := (IsLocalization.orderIsoOfPrime q.primeCompl (Localization.AtPrime q)).symm
    let P := f ⟨p, hpp, hpq.disjoint_compl_left⟩
    let Q := f ⟨q, hq.isPrime, Set.disjoint_left.mpr fun _ a => a⟩
    have hinj : Function.Injective (algebraMap A (Localization.AtPrime q)) :=
      IsLocalization.injective (Localization.AtPrime q) q.primeCompl_le_nonZeroDivisors
    have hp1 : P.1 != ⊥ := fun x => hp ((p.map_eq_bot_iff_of_injective hinj).mp x)
    have hq1 : Q.1 != ⊥ :=
      fun x => (ne_bot_of_le_ne_bot hp hpq) ((q.map_eq_bot_iff_of_injective hinj).mp x)
    rcases (IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime (Localization.AtPrime q)).mp
      (h.is_dvr_at_nonzero_prime q (ne_bot_of_le_ne_bot hp hpq) hq.isPrime) with ⟨_, huq⟩
    rw [show p = q from Subtype.val_inj.mpr <| f.injective <|
      Subtype.val_inj.mp (huq.unique ⟨hp1]; rw [P.2⟩ ⟨hq1]; rw [Q.2⟩)]
    exact hq

/--
Instance `IsDedekindDomainDvr.isIntegrallyClosed` / 实例 `IsDedekindDomainDvr.isIntegrallyClosed`

English:
instance IsDedekindDomainDvr.isIntegrallyClosed
  signature: [h : IsDedekindDomainDvr A]
  body: IsIntegrallyClosed.of_localization_maximal fun p hp0 hpm =>
    let ⟨_, _⟩ := (IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime
      (Localization.AtPrime p)).mp (h.is_dvr_at_nonzero_prime p hp0 hpm.isPrime)
    inferInstance

中文:
实例 是DedekindDomainDvr.is整数egrallyClosed
  签名: [h : 是DedekindDomainDvr A]
  定义体: IsIntegrallyClosed.of_localization_maximal fun p hp0 hpm =>
    let ⟨_, _⟩ := (IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime
      (Localization.AtPrime p)).mp (h.is_dvr_at_nonzero_prime p hp0 hpm.isPrime)
    inferInstance

Depends on / 依赖: AtPrime, IsDiscreteValuationRing, IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime, IsIntegrallyClosed, IsIntegrallyClosed.of_localization_maximal, Localization, Localization.AtPrime, h.is_dvr_at_nonzero_prime, hpm.isPrime, iff_pid_with_one_nonzero_prime, isPrime, is_dvr_at_nonzero_prime, of_localization_maximal
-/
instance IsDedekindDomainDvr.isIntegrallyClosed [h : IsDedekindDomainDvr A] :
    IsIntegrallyClosed A :=
IsIntegrallyClosed.of_localization_maximal fun p hp0 hpm =>
    let ⟨_, _⟩ := (IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime
      (Localization.AtPrime p)).mp (h.is_dvr_at_nonzero_prime p hp0 hpm.isPrime)
    inferInstance

/--
Instance `IsDedekindDomainDvr.isDedekindDomain` / 实例 `IsDedekindDomainDvr.isDedekindDomain`

English:
instance IsDedekindDomainDvr.isDedekindDomain
  signature: [IsDedekindDomainDvr A]

中文:
实例 是DedekindDomainDvr.isDedekindDomain
  签名: [是DedekindDomainDvr A]
-/
instance IsDedekindDomainDvr.isDedekindDomain [IsDedekindDomainDvr A] : IsDedekindDomain A where
