/-
Copyright (c) 2020 Kenji Nakagawa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenji Nakagawa, Anne Baanen, Filippo A. E. Nuccio
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.DualLattice
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Trace.Basic

/-!
# Integral closure of Dedekind domains

This file shows the integral closure of a Dedekind domain (in particular, the ring of integers
of a number field) is a Dedekind domain.

## Implementation notes

The definitions that involve a field of fractions choose a canonical field of fractions,
but are independent of that choice. The `..._iff` lemmas express this independence.

Often, definitions assume that Dedekind domains are not fields. We found it more practical
to add a `(h : ¬IsField A)` assumption whenever this is explicitly needed.

## References

* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Fröhlich, *Algebraic Number Theory*][cassels1967algebraic]
* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992]

## Tags

dedekind domain, dedekind ring
-/

public section

open Algebra Module
open scoped nonZeroDivisors Polynomial

variable (A K : Type*) [CommRing A] [Field K]

section IsIntegralClosure

/-! ### `IsIntegralClosure` section

We show that an integral closure of a Dedekind domain in a finite separable
field extension is again a Dedekind domain. This implies the ring of integers
of a number field is a Dedekind domain. -/


variable [Algebra A K] [IsFractionRing A K]
variable (L : Type*) [Field L] (C : Type*) [CommRing C]
variable [Algebra K L] [Algebra A L] [IsScalarTower A K L]
variable [Algebra C L] [IsIntegralClosure C A L] [Algebra A C] [IsScalarTower A C L]
include K L

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `IsIntegralClosure.isLocalization` / 定理 `IsIntegralClosure.isLocalization`

English:
theorem IsIntegralClosure.isLocalization
  given: [IsDomain A] [Algebra.IsAlgebraic K L]
  proof: by
  have : IsDomain C :=
    (IsIntegralClosure.equiv A C L (integralClosure A L)).toMulEquiv.isDomain (integralClosure A L)
  have : IsTorsionFree A L := .trans_faithfulSMul A K L
  have : IsTorsionFree A C := IsIntegralClosure.isTorsionFree A L
  refine ⟨?_, fun z => ?_, fun {x y} h => ⟨1, ?_⟩⟩
 

中文:
定理 是整闭包.isLocalization
  条件: [是整环 A] [代数.是代数 K L]
  证明: by
  have : IsDomain C :=
    (IsIntegralClosure.equiv A C L (integralClosure A L)).toMulEquiv.isDomain (integralClosure A L)
  have : IsTorsionFree A L := .trans_faithfulSMul A K L
  have : IsTorsionFree A C := IsIntegralClosure.isTorsionFree A L
  refine ⟨?_, fun z => ?_, fun {x y} h => ⟨1, ?_⟩⟩
 

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, IsDomain, IsIntegralClosure, IsIntegralClosure.algebraMap_injective, IsIntegralClosure.equiv, IsIntegralClosure.isTorsionFree, IsTorsionFree, Subtype, Subtype.coe_mk, algebraMap_injective, coe_mk, integralClosure, isDomain, isTorsionFree, isUnit_iff_ne_zero, map_ne_zero_iff, toMulEquiv, toMulEquiv.isDomain, trans_faithfulSMul
-/
theorem IsIntegralClosure.isLocalization [IsDomain A] [Algebra.IsAlgebraic K L] :
    IsLocalization (Algebra.algebraMapSubmonoid C A⁰) L := by
  have : IsDomain C :=
    (IsIntegralClosure.equiv A C L (integralClosure A L)).toMulEquiv.isDomain (integralClosure A L)
  have : IsTorsionFree A L := .trans_faithfulSMul A K L
  have : IsTorsionFree A C := IsIntegralClosure.isTorsionFree A L
  refine ⟨?_, fun z => ?_, fun {x y} h => ⟨1, ?_⟩⟩
  · rintro ⟨_, x, hx, rfl⟩
    rw [isUnit_iff_ne_zero]; rw [map_ne_zero_iff _ (IsIntegralClosure.algebraMap_injective C A L)]; rw [Subtype.coe_mk]; rw [map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective A C)]
    exact mem_nonZeroDivisors_iff_ne_zero.mp hx
  · obtain ⟨m, hm⟩ :=
      IsIntegral.exists_multiple_integral_of_isLocalization A⁰ z
        (Algebra.IsIntegral.isIntegral (R := K) z)
    obtain ⟨x, hx⟩ : exists x, algebraMap C L x = m • z := IsIntegralClosure.isIntegral_iff.mp hm
    refine ⟨⟨x, algebraMap A C m, m, SetLike.coe_mem m, rfl⟩, ?_⟩
    rw [Subtype.coe_mk]; rw [← IsScalarTower.algebraMap_apply]; rw [hx]; rw [mul_comm]; rw [Submonoid.smul_def]; rw [smul_def]
  · simp only [IsIntegralClosure.algebraMap_injective C A L h]

/--
theorem `IsIntegralClosure.isLocalization_of_isSeparable` / 定理 `IsIntegralClosure.isLocalization_of_isSeparable`

English:
theorem IsIntegralClosure.isLocalization_of_isSeparable
  given: [IsDomain A] [Algebra.IsSeparable K L]
  proof: IsIntegralClosure.isLocalization A K L C

中文:
定理 是整闭包.isLocalization_of_isSeparable
  条件: [是整环 A] [代数.是可分 K L]
  证明: IsIntegralClosure.isLocalization A K L C

Depends on / 依赖: IsIntegralClosure, IsIntegralClosure.isLocalization, isLocalization
-/
theorem IsIntegralClosure.isLocalization_of_isSeparable [IsDomain A] [Algebra.IsSeparable K L] :
    IsLocalization (Algebra.algebraMapSubmonoid C A⁰) L :=
  IsIntegralClosure.isLocalization A K L C

variable [FiniteDimensional K L]
variable {A K L}

/--
theorem `IsIntegralClosure.range_le_span_dualBasis` / 定理 `IsIntegralClosure.range_le_span_dualBasis`

English:
theorem IsIntegralClosure.range_le_span_dualBasis
  statement: [Algebra.IsSeparable K L] {ι : Type*} [Finite ι]
  proof: by
  rw [← LinearMap.BilinForm.dualSubmodule_span_of_basis]; rw [← LinearMap.BilinForm.le_flip_dualSubmodule]; rw [Submodule.span_le]
  rintro _ ⟨i, rfl⟩ _ ⟨y, rfl⟩
  simp only [LinearMap.coe_restrictScalars, linearMap_apply, LinearMap.BilinForm.flip_apply,
    traceForm_apply]
refine Submodule.mem_

中文:
定理 是整闭包.range_le_span_dualBasis
  结论: [代数.是可分 K L] {ι : 类型} [有限 ι]
  证明: by
  rw [← LinearMap.BilinForm.dualSubmodule_span_of_basis]; rw [← LinearMap.BilinForm.le_flip_dualSubmodule]; rw [Submodule.span_le]
  rintro _ ⟨i, rfl⟩ _ ⟨y, rfl⟩
  simp only [LinearMap.coe_restrictScalars, linearMap_apply, LinearMap.BilinForm.flip_apply,
    traceForm_apply]
refine Submodule.mem_

Depends on / 依赖: BilinForm, IsIntegralClosure, IsIntegralClosure.isIntegral, IsIntegrallyClosed, IsIntegrallyClosed.isIntegral_iff.mp, LinearMap, LinearMap.BilinForm.dualSubmodule_span_of_basis, LinearMap.BilinForm.flip_apply, LinearMap.BilinForm.le_flip_dualSubmodule, LinearMap.coe_restrictScalars, Submodule, Submodule.mem_one.mpr, Submodule.span_le, algebraMap, algebraMap.mul, coe_restrictScalars, dualSubmodule_span_of_basis, flip_apply, hb_int, isIntegral
-/
theorem IsIntegralClosure.range_le_span_dualBasis [Algebra.IsSeparable K L] {ι : Type*} [Finite ι]
    [DecidableEq ι] (b : Basis ι K L) (hb_int : forall i, IsIntegral A (b i)) [IsIntegrallyClosed A] :
    LinearMap.range ((Algebra.linearMap C L).restrictScalars A) <=
    Submodule.span A (Set.range <| (traceForm K L).dualBasis (traceForm_nondegenerate K L) b) := by
  rw [← LinearMap.BilinForm.dualSubmodule_span_of_basis]; rw [← LinearMap.BilinForm.le_flip_dualSubmodule]; rw [Submodule.span_le]
  rintro _ ⟨i, rfl⟩ _ ⟨y, rfl⟩
  simp only [LinearMap.coe_restrictScalars, linearMap_apply, LinearMap.BilinForm.flip_apply,
    traceForm_apply]
refine Submodule.mem_one.mpr IsIntegrallyClosed.isIntegral_iff.mp ?_
  exact isIntegral_trace ((IsIntegralClosure.isIntegral A L y).algebraMap.mul (hb_int i))

/--
theorem `integralClosure_le_span_dualBasis` / 定理 `integralClosure_le_span_dualBasis`

English:
theorem integralClosure_le_span_dualBasis
  statement: [Algebra.IsSeparable K L] {ι : Type*} [Finite ι]
  proof: by
  refine le_trans ?_ (IsIntegralClosure.range_le_span_dualBasis (integralClosure A L) b hb_int)
  intro x hx
  exact ⟨⟨x, hx⟩, rfl⟩

中文:
定理 integralClosure_le_span_dualBasis
  结论: [代数.是可分 K L] {ι : 类型} [有限 ι]
  证明: by
  refine le_trans ?_ (IsIntegralClosure.range_le_span_dualBasis (integralClosure A L) b hb_int)
  intro x hx
  exact ⟨⟨x, hx⟩, rfl⟩

Depends on / 依赖: IsIntegralClosure, IsIntegralClosure.range_le_span_dualBasis, hb_int, integralClosure, le_trans, range_le_span_dualBasis
-/
theorem integralClosure_le_span_dualBasis [Algebra.IsSeparable K L] {ι : Type*} [Finite ι]
    [DecidableEq ι] (b : Basis ι K L) (hb_int : forall i, IsIntegral A (b i)) [IsIntegrallyClosed A] :
    Subalgebra.toSubmodule (integralClosure A L) <=
    Submodule.span A (Set.range <| (traceForm K L).dualBasis (traceForm_nondegenerate K L) b) := by
  refine le_trans ?_ (IsIntegralClosure.range_le_span_dualBasis (integralClosure A L) b hb_int)
  intro x hx
  exact ⟨⟨x, hx⟩, rfl⟩

variable [IsDomain A]
variable (A K)

/--
theorem `exists_integral_multiples` / 定理 `exists_integral_multiples`

English:
theorem exists_integral_multiples
  given: (s : Finset L)
  proof: have := IsLocalization.isAlgebraic K (nonZeroDivisors A)
  have := Algebra.IsAlgebraic.trans A K L
  Algebra.IsAlgebraic.exists_integral_multiples ..

中文:
定理 存在_integral_multiples
  条件: (s : 有限集 L)
  证明: have := IsLocalization.isAlgebraic K (nonZeroDivisors A)
  have := Algebra.IsAlgebraic.trans A K L
  Algebra.IsAlgebraic.exists_integral_multiples ..

Depends on / 依赖: Algebra, Algebra.IsAlgebraic.exists_integral_multiples, Algebra.IsAlgebraic.trans, IsAlgebraic, IsLocalization, IsLocalization.isAlgebraic, exists_integral_multiples, isAlgebraic, nonZeroDivisors
-/
theorem exists_integral_multiples (s : Finset L) :
    exists y != (0 : A), forall x in s, IsIntegral A (y • x) :=
  have := IsLocalization.isAlgebraic K (nonZeroDivisors A)
  have := Algebra.IsAlgebraic.trans A K L
  Algebra.IsAlgebraic.exists_integral_multiples ..

variable (L)

/--
theorem `FiniteDimensional.exists_is_basis_integral` / 定理 `FiniteDimensional.exists_is_basis_integral`

English:
theorem FiniteDimensional.exists_is_basis_integral
  proof: by
  let := Classical.decEq L
  let s' := IsNoetherian.finsetBasisIndex K L
  let bs' := IsNoetherian.finsetBasis K L
  obtain ⟨y, hy, his'⟩ := exists_integral_multiples A K (Finset.univ.image bs')
  have hy' : algebraMap A L y != 0 := by
    refine mt ((injective_iff_map_eq_zero (algebraMap A L)).m

中文:
定理 有限维.存在_is_basis_integral
  证明: by
  let := Classical.decEq L
  let s' := IsNoetherian.finsetBasisIndex K L
  let bs' := IsNoetherian.finsetBasis K L
  obtain ⟨y, hy, his'⟩ := exists_integral_multiples A K (Finset.univ.image bs')
  have hy' : algebraMap A L y != 0 := by
    refine mt ((injective_iff_map_eq_zero (algebraMap A L)).m

Depends on / 依赖: Algebra, Algebra.lmul, Classical, Classical.decEq, Finset, Finset.univ.image, IsFractionRing, IsFractionRing.injective, IsNoetherian, IsNoetherian.finsetBasis, IsNoetherian.finsetBasisIndex, IsScalarTower, IsScalarTower.algebraMap_eq, algebraMap, algebraMap_eq, exists_integral_multiples, finsetBasis, finsetBasisIndex, injective, injective.comp
-/
theorem FiniteDimensional.exists_is_basis_integral :
    exists (s : Finset L) (b : Basis s K L), forall x, IsIntegral A (b x) := by
  let := Classical.decEq L
  let s' := IsNoetherian.finsetBasisIndex K L
  let bs' := IsNoetherian.finsetBasis K L
  obtain ⟨y, hy, his'⟩ := exists_integral_multiples A K (Finset.univ.image bs')
  have hy' : algebraMap A L y != 0 := by
    refine mt ((injective_iff_map_eq_zero (algebraMap A L)).mp ?_ _) hy
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  refine ⟨s', bs'.map {Algebra.lmul _ _ (algebraMap A L y) with
    toFun := fun x => algebraMap A L y * x
    invFun := fun x => (algebraMap A L y)⁻¹ * x
    left_inv := ?_
    right_inv := ?_}, ?_⟩
  · intro x; simp only [inv_mul_cancel_left₀ hy']
  · intro x; simp only [mul_inv_cancel_left₀ hy']
  · rintro ⟨x', hx'⟩
    simp only [Algebra.smul_def, Finset.mem_image, Finset.mem_univ,
      true_and] at his'
    exact his' _ ⟨_, rfl⟩

variable [Algebra.IsSeparable K L]

/--
theorem `IsIntegralClosure.isNoetherian` / 定理 `IsIntegralClosure.isNoetherian`

English:
theorem IsIntegralClosure.isNoetherian
  given: [IsIntegrallyClosed A] [IsNoetherianRing A]
  proof: by
  have := Classical.decEq L
  obtain ⟨s, b, hb_int⟩ := FiniteDimensional.exists_is_basis_integral A K L
  let b' := (traceForm K L).dualBasis (traceForm_nondegenerate K L) b
  let := isNoetherian_span_of_finite A (Set.finite_range b')
  let f : C ->ₗ[A] Submodule.span A (Set.range b') :=
    (Sub

中文:
定理 是整闭包.isNoetherian
  条件: [是整闭 A] [是Noether环 A]
  证明: by
  have := Classical.decEq L
  obtain ⟨s, b, hb_int⟩ := FiniteDimensional.exists_is_basis_integral A K L
  let b' := (traceForm K L).dualBasis (traceForm_nondegenerate K L) b
  let := isNoetherian_span_of_finite A (Set.finite_range b')
  let f : C ->ₗ[A] Submodule.span A (Set.range b') :=
    (Sub

Depends on / 依赖: Algebra, Algebra.linearMap, Classical, Classical.decEq, FiniteDimensional, FiniteDimensional.exists_is_basis_integral, IsIntegralClosure, IsIntegralClosure.range_le_span_dualBasis, LinearMap, LinearMap.ker_comp, Set.finite_range, Set.range, Submodule, Submodule.inclusion, Submodule.ker, Submodule.span, dualBasis, exists_is_basis_integral, finite_range, hb_int
-/
theorem IsIntegralClosure.isNoetherian [IsIntegrallyClosed A] [IsNoetherianRing A] :
    IsNoetherian A C := by
  have := Classical.decEq L
  obtain ⟨s, b, hb_int⟩ := FiniteDimensional.exists_is_basis_integral A K L
  let b' := (traceForm K L).dualBasis (traceForm_nondegenerate K L) b
  let := isNoetherian_span_of_finite A (Set.finite_range b')
  let f : C ->ₗ[A] Submodule.span A (Set.range b') :=
    (Submodule.inclusion (IsIntegralClosure.range_le_span_dualBasis C b hb_int)).comp
      ((Algebra.linearMap C L).restrictScalars A).rangeRestrict
  refine isNoetherian_of_ker_bot f ?_
  rw [LinearMap.ker_comp]; rw [Submodule.ker_inclusion]; rw [Submodule.comap_bot]; rw [LinearMap.ker_codRestrict]
  exact LinearMap.ker_eq_bot_of_injective (IsIntegralClosure.algebraMap_injective C A L)

/--
theorem `IsIntegralClosure.isNoetherianRing` / 定理 `IsIntegralClosure.isNoetherianRing`

English:
theorem IsIntegralClosure.isNoetherianRing
  given: [IsIntegrallyClosed A] [IsNoetherianRing A]
  proof: isNoetherianRing_iff.mpr isNoetherian_of_tower A (IsIntegralClosure.isNoetherian A K L C)

中文:
定理 是整闭包.isNoetherianRing
  条件: [是整闭 A] [是Noether环 A]
  证明: isNoetherianRing_iff.mpr isNoetherian_of_tower A (IsIntegralClosure.isNoetherian A K L C)

Depends on / 依赖: IsIntegralClosure, IsIntegralClosure.isNoetherian, isNoetherian, isNoetherianRing_iff, isNoetherianRing_iff.mpr, isNoetherian_of_tower
-/
theorem IsIntegralClosure.isNoetherianRing [IsIntegrallyClosed A] [IsNoetherianRing A] :
    IsNoetherianRing C :=
isNoetherianRing_iff.mpr isNoetherian_of_tower A (IsIntegralClosure.isNoetherian A K L C)

/--
theorem `IsIntegralClosure.finite` / 定理 `IsIntegralClosure.finite`

English:
theorem IsIntegralClosure.finite
  given: [IsIntegrallyClosed A] [IsNoetherianRing A]
  proof: by
  have := IsIntegralClosure.isNoetherian A K L C
  exact Module.IsNoetherian.finite A C

中文:
定理 是整闭包.finite
  条件: [是整闭 A] [是Noether环 A]
  证明: by
  have := IsIntegralClosure.isNoetherian A K L C
  exact Module.IsNoetherian.finite A C

Depends on / 依赖: IsIntegralClosure, IsIntegralClosure.isNoetherian, IsNoetherian, Module, Module.IsNoetherian.finite, finite, isNoetherian
-/
theorem IsIntegralClosure.finite [IsIntegrallyClosed A] [IsNoetherianRing A] :
    Module.Finite A C := by
  have := IsIntegralClosure.isNoetherian A K L C
  exact Module.IsNoetherian.finite A C

/--
theorem `IsIntegralClosure.module_free` / 定理 `IsIntegralClosure.module_free`

English:
theorem IsIntegralClosure.module_free
  given: [IsTorsionFree A L] [IsPrincipalIdealRing A]
  proof: haveI : IsTorsionFree A C := IsIntegralClosure.isTorsionFree A L
  haveI : IsNoetherian A C := IsIntegralClosure.isNoetherian A K L _
  inferInstance

中文:
定理 是整闭包.module_free
  条件: [是无挠 A L] [是主理想环 A]
  证明: haveI : IsTorsionFree A C := IsIntegralClosure.isTorsionFree A L
  haveI : IsNoetherian A C := IsIntegralClosure.isNoetherian A K L _
  inferInstance

Depends on / 依赖: IsIntegralClosure, IsIntegralClosure.isNoetherian, IsIntegralClosure.isTorsionFree, IsNoetherian, IsTorsionFree, isNoetherian, isTorsionFree
-/
theorem IsIntegralClosure.module_free [IsTorsionFree A L] [IsPrincipalIdealRing A] :
    Module.Free A C :=
  haveI : IsTorsionFree A C := IsIntegralClosure.isTorsionFree A L
  haveI : IsNoetherian A C := IsIntegralClosure.isNoetherian A K L _
  inferInstance

/--
theorem `IsIntegralClosure.rank` / 定理 `IsIntegralClosure.rank`

English:
theorem IsIntegralClosure.rank
  given: [IsPrincipalIdealRing A] [IsTorsionFree A L]
  proof: by
  have : Module.Free A C := IsIntegralClosure.module_free A K L C
  have : IsNoetherian A C := IsIntegralClosure.isNoetherian A K L C
  have : IsLocalization (Algebra.algebraMapSubmonoid C A⁰) L :=
    IsIntegralClosure.isLocalization A K L C
  let b := Basis.localizationLocalization K A⁰ L (Modu

中文:
定理 是整闭包.rank
  条件: [是主理想环 A] [是无挠 A L]
  证明: by
  have : Module.Free A C := IsIntegralClosure.module_free A K L C
  have : IsNoetherian A C := IsIntegralClosure.isNoetherian A K L C
  have : IsLocalization (Algebra.algebraMapSubmonoid C A⁰) L :=
    IsIntegralClosure.isLocalization A K L C
  let b := Basis.localizationLocalization K A⁰ L (Modu

Depends on / 依赖: Algebra, Algebra.algebraMapSubmonoid, Basis.localizationLocalization, IsIntegralClosure, IsIntegralClosure.isLocalization, IsIntegralClosure.isNoetherian, IsIntegralClosure.module_free, IsLocalization, IsNoetherian, Module, Module.Free, Module.Free.chooseBasis, Module.finrank_eq_card_basis, Module.finrank_eq_card_chooseBasisIndex, algebraMapSubmonoid, chooseBasis, finrank_eq_card_basis, finrank_eq_card_chooseBasisIndex, isLocalization, isNoetherian
-/
theorem IsIntegralClosure.rank [IsPrincipalIdealRing A] [IsTorsionFree A L] :
    Module.finrank A C = Module.finrank K L := by
  have : Module.Free A C := IsIntegralClosure.module_free A K L C
  have : IsNoetherian A C := IsIntegralClosure.isNoetherian A K L C
  have : IsLocalization (Algebra.algebraMapSubmonoid C A⁰) L :=
    IsIntegralClosure.isLocalization A K L C
  let b := Basis.localizationLocalization K A⁰ L (Module.Free.chooseBasis A C)
  rw [Module.finrank_eq_card_chooseBasisIndex]; rw [Module.finrank_eq_card_basis b]

variable {A K}

/--
theorem `integralClosure.isNoetherianRing` / 定理 `integralClosure.isNoetherianRing`

English:
theorem integralClosure.isNoetherianRing
  given: [IsIntegrallyClosed A] [IsNoetherianRing A]
  proof: IsIntegralClosure.isNoetherianRing A K L (integralClosure A L)

中文:
定理 integralClosure.isNoetherianRing
  条件: [是整闭 A] [是Noether环 A]
  证明: IsIntegralClosure.isNoetherianRing A K L (integralClosure A L)

Depends on / 依赖: IsIntegralClosure, IsIntegralClosure.isNoetherianRing, integralClosure, isNoetherianRing
-/
theorem integralClosure.isNoetherianRing [IsIntegrallyClosed A] [IsNoetherianRing A] :
    IsNoetherianRing (integralClosure A L) :=
  IsIntegralClosure.isNoetherianRing A K L (integralClosure A L)

variable (A K) [IsDomain C]

set_option linter.overlappingInstances false

/--
theorem `IsIntegralClosure.isDedekindDomain` / 定理 `IsIntegralClosure.isDedekindDomain`

English:
theorem IsIntegralClosure.isDedekindDomain
  given: [IsDedekindDomain A]
  statement: IsDedekindDomain C
  proof: have : IsFractionRing C L := IsIntegralClosure.isFractionRing_of_finite_extension A K L C
  have : Algebra.IsIntegral A C := IsIntegralClosure.isIntegral_algebra A L
  { IsIntegralClosure.isNoetherianRing A K L C,
    Ring.DimensionLEOne.of_isIntegral A C,
    (isIntegrallyClosed_iff L).mpr fun {x} 

中文:
定理 是整闭包.isDedekindDomain
  条件: [是Dedekind整环 A]
  结论: 是Dedekind整环 C
  证明: have : IsFractionRing C L := IsIntegralClosure.isFractionRing_of_finite_extension A K L C
  have : Algebra.IsIntegral A C := IsIntegralClosure.isIntegral_algebra A L
  { IsIntegralClosure.isNoetherianRing A K L C,
    Ring.DimensionLEOne.of_isIntegral A C,
    (isIntegrallyClosed_iff L).mpr fun {x} 

Depends on / 依赖: Algebra, Algebra.IsIntegral, DimensionLEOne, IsDedekindDomain, IsFractionRing, IsIntegral, IsIntegralClosure, IsIntegralClosure.algebraMap_mk, IsIntegralClosure.isFractionRing_of_finite_extension, IsIntegralClosure.isIntegral_algebra, IsIntegralClosure.isNoetherianRing, IsIntegralClosure.mk, Ring.DimensionLEOne.of_isIntegral, algebraMap_mk, isFractionRing_of_finite_extension, isIntegral_algebra, isIntegral_trans, isIntegrallyClosed_iff, isNoetherianRing, of_isIntegral
-/
theorem IsIntegralClosure.isDedekindDomain [IsDedekindDomain A] : IsDedekindDomain C :=
  have : IsFractionRing C L := IsIntegralClosure.isFractionRing_of_finite_extension A K L C
  have : Algebra.IsIntegral A C := IsIntegralClosure.isIntegral_algebra A L
  { IsIntegralClosure.isNoetherianRing A K L C,
    Ring.DimensionLEOne.of_isIntegral A C,
    (isIntegrallyClosed_iff L).mpr fun {x} hx =>
      ⟨IsIntegralClosure.mk' C x (isIntegral_trans (R := A) _ hx),
        IsIntegralClosure.algebraMap_mk' _ _ _⟩ with : IsDedekindDomain C }

/--
theorem `integralClosure.isDedekindDomain` / 定理 `integralClosure.isDedekindDomain`

English:
theorem integralClosure.isDedekindDomain
  given: [IsDedekindDomain A]
  proof: IsIntegralClosure.isDedekindDomain A K L (integralClosure A L)

中文:
定理 integralClosure.isDedekindDomain
  条件: [是Dedekind整环 A]
  证明: IsIntegralClosure.isDedekindDomain A K L (integralClosure A L)

Depends on / 依赖: IsIntegralClosure, IsIntegralClosure.isDedekindDomain, integralClosure, isDedekindDomain
-/
theorem integralClosure.isDedekindDomain [IsDedekindDomain A] :
    IsDedekindDomain (integralClosure A L) :=
  IsIntegralClosure.isDedekindDomain A K L (integralClosure A L)

variable [Algebra (FractionRing A) L] [IsScalarTower A (FractionRing A) L]
variable [FiniteDimensional (FractionRing A) L] [Algebra.IsSeparable (FractionRing A) L]

/--
Instance `integralClosure.isDedekindDomain_fractionRing` / 实例 `integralClosure.isDedekindDomain_fractionRing`

English:
instance integralClosure.isDedekindDomain_fractionRing
  signature: [IsDedekindDomain A]
  body: integralClosure.isDedekindDomain A (FractionRing A) L

中文:
实例 integralClosure.isDedekindDomain_fractionRing
  签名: [是Dedekind整环 A]
  定义体: integralClosure.isDedekindDomain A (FractionRing A) L

Depends on / 依赖: FractionRing, integralClosure, integralClosure.isDedekindDomain, isDedekindDomain
-/
instance integralClosure.isDedekindDomain_fractionRing [IsDedekindDomain A] :
    IsDedekindDomain (integralClosure A L) :=
  integralClosure.isDedekindDomain A (FractionRing A) L

end IsIntegralClosure
