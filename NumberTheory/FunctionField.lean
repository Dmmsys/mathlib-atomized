/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Ashvni Narayanan
-/
module

public import Mathlib.FieldTheory.RatFunc.Degree
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Topology.Algebra.Valued.ValuedField
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.FieldTheory.RatFunc.IntermediateField
public import Mathlib.RingTheory.Adjoin.Polynomial.Bivariate
public import Mathlib.FieldTheory.RatFunc.Valuation -- for deprecation to `RatFunc.inftyValuation` and `RatFunc.CompletionAtInfty`

/-!
# Function fields

This file defines a function field and the ring of integers corresponding to it.

## Main definitions

- `FunctionField F K` states that `K` is a function field over the field `F`,
  i.e. it is a finite extension of the field of rational functions in one variable over `F`.
- `FunctionField.ringOfIntegers` defines the ring of integers corresponding to a function field
  as the integral closure of `F[X]` in the function field.

## Implementation notes
The definitions that involve a field of fractions choose a canonical field of fractions,
but are independent of that choice. We also omit assumptions like
`IsScalarTower F[X] (FractionRing F[X]) K` in definitions,
adding them back in lemmas when they are needed.

## References
* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Fröhlich, *Algebraic Number Theory*][cassels1967algebraic]
* [P. Samuel, *Algebraic Theory of Numbers*][samuel1967]
* [M. Rosen, *Number Theory in Function Fields*][rosen2002]

## Tags
function field, ring of integers
-/

@[expose] public section


noncomputable section

open scoped nonZeroDivisors Polynomial WithZero RatFunc

variable (F K : Type*) [Field F] [Field K]

/--
Definition of `FunctionField` / `FunctionField` 的定义

English:
abbreviation FunctionField
  signature: [Algebra F⟮X⟯ K]
  body: FiniteDimensional F⟮X⟯ K

中文:
缩写 FunctionField
  签名: [代数 F⟮X⟯ K]
  定义体: FiniteDimensional F⟮X⟯ K

Depends on / 依赖: FiniteDimensional
-/
abbrev FunctionField [Algebra F⟮X⟯ K] : Prop :=
  FiniteDimensional F⟮X⟯ K

/--
theorem `functionField_iff` / 定理 `functionField_iff`

English:
theorem functionField_iff
  statement: (Ft : Type*) [Field Ft] [Algebra F[X] Ft]
  proof: by
  let e := IsLocalization.algEquiv F[X]⁰ F⟮X⟯ Ft
  have : forall (c) (x : K), e c • x = c • x := by
    intro c x
    rw [Algebra.smul_def]; rw [Algebra.smul_def]
    congr
    refine congr_fun (f := fun c => algebraMap Ft K (e c)) ?_ c
    refine IsLocalization.ext (nonZeroDivisors F[X]) _ _ ?_ ?_ ?_ ?_ ?_ <;> intros <;>
      simp only [map_one, map_mul, AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
  constructor <;> intro h
  · let b := Module.finBasis F⟮X⟯ K
    exact (b.mapCoeffs e this).finiteDimensional_of_finite
  · let b := Module.finBasis Ft K
    refine (b.mapCoeffs e.symm ?_).finiteDimensional_of_finite
    intro c x; convert! (this (e.symm c) x).symm; simp only [e.apply_symm_apply]

中文:
定理 functionField_iff
  结论: (Ft : 类型) [域 Ft] [代数 F[X] Ft]
  证明: by
  let e := IsLocalization.algEquiv F[X]⁰ F⟮X⟯ Ft
  have : forall (c) (x : K), e c • x = c • x := by
    intro c x
    rw [Algebra.smul_def]; rw [Algebra.smul_def]
    congr
    refine congr_fun (f := fun c => algebraMap Ft K (e c)) ?_ c
    refine IsLocalization.ext (nonZeroDivisors F[X]) _ _ ?_ ?_ ?_ ?_ ?_ <;> intros <;>
      simp only [map_one, map_mul, AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
  constructor <;> intro h
  · let b := Module.finBasis F⟮X⟯ K
    exact (b.mapCoeffs e this).finiteDimensional_of_finite
  · let b := Module.finBasis Ft K
    refine (b.mapCoeffs e.symm ?_).finiteDimensional_of_finite
    intro c x; convert! (this (e.symm c) x).symm; simp only [e.apply_symm_apply]

Depends on / 依赖: AlgEquiv, AlgEquiv.commutes, Algebra, Algebra.smul_def, IsLocalization, IsLocalization.algEquiv, IsLocalization.ext, IsScalarTower, IsScalarTower.algebraMap_apply, Module, Module.finBasis, algEquiv, algebraMap, algebraMap_apply, b.mapCoeffs, commutes, congr_fun, finBasis, finiteDimensional_of_finite, intros
-/
theorem functionField_iff (Ft : Type*) [Field Ft] [Algebra F[X] Ft]
    [IsFractionRing F[X] Ft] [Algebra F⟮X⟯ K] [Algebra Ft K] [Algebra F[X] K]
    [IsScalarTower F[X] Ft K] [IsScalarTower F[X] F⟮X⟯ K] :
    FunctionField F K ↔ FiniteDimensional Ft K := by
  let e := IsLocalization.algEquiv F[X]⁰ F⟮X⟯ Ft
  have : forall (c) (x : K), e c • x = c • x := by
    intro c x
    rw [Algebra.smul_def]; rw [Algebra.smul_def]
    congr
    refine congr_fun (f := fun c => algebraMap Ft K (e c)) ?_ c
    refine IsLocalization.ext (nonZeroDivisors F[X]) _ _ ?_ ?_ ?_ ?_ ?_ <;> intros <;>
      simp only [map_one, map_mul, AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
  constructor <;> intro h
  · let b := Module.finBasis F⟮X⟯ K
    exact (b.mapCoeffs e this).finiteDimensional_of_finite
  · let b := Module.finBasis Ft K
    refine (b.mapCoeffs e.symm ?_).finiteDimensional_of_finite
    intro c x; convert! (this (e.symm c) x).symm; simp only [e.apply_symm_apply]

namespace FunctionField

/--
theorem `algebraMap_injective` / 定理 `algebraMap_injective`

English:
theorem algebraMap_injective
  statement: [Algebra F[X] K] [Algebra F⟮X⟯ K]
  proof: by
  rw [IsScalarTower.algebraMap_eq F[X] F⟮X⟯ K]
  exact (algebraMap F⟮X⟯ K).injective.comp (IsFractionRing.injective F[X] F⟮X⟯)

中文:
定理 algebraMap_injective
  结论: [代数 F[X] K] [代数 F⟮X⟯ K]
  证明: by
  rw [IsScalarTower.algebraMap_eq F[X] F⟮X⟯ K]
  exact (algebraMap F⟮X⟯ K).injective.comp (IsFractionRing.injective F[X] F⟮X⟯)

Depends on / 依赖: IsFractionRing, IsFractionRing.injective, IsScalarTower, IsScalarTower.algebraMap_eq, algebraMap, algebraMap_eq, injective, injective.comp
-/
theorem algebraMap_injective [Algebra F[X] K] [Algebra F⟮X⟯ K]
    [IsScalarTower F[X] F⟮X⟯ K] : Function.Injective (algebraMap F[X] K) := by
  rw [IsScalarTower.algebraMap_eq F[X] F⟮X⟯ K]
  exact (algebraMap F⟮X⟯ K).injective.comp (IsFractionRing.injective F[X] F⟮X⟯)

/--
Definition of `ringOfIntegers` / `ringOfIntegers` 的定义

English:
definition ringOfIntegers
  signature: [Algebra F[X] K]
  body: integralClosure F[X] K

中文:
定义 ringOf整数egers
  签名: [代数 F[X] K]
  定义体: integralClosure F[X] K

Depends on / 依赖: integralClosure
-/
def ringOfIntegers [Algebra F[X] K] :=
  integralClosure F[X] K

namespace ringOfIntegers

variable [Algebra F[X] K]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsDomain (ringOfIntegers F K)
  body: (ringOfIntegers F K).isDomain

中文:
实例 :
  签名: 是整环 (ringOf整数egers F K)
  定义体: (ringOfIntegers F K).isDomain

Depends on / 依赖: isDomain, ringOfIntegers
-/
instance : IsDomain (ringOfIntegers F K) :=
  (ringOfIntegers F K).isDomain

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIntegralClosure (ringOfIntegers F K) F[X] K
  body: integralClosure.isIntegralClosure _ _

中文:
实例 :
  签名: 是整闭包 (ringOf整数egers F K) F[X] K
  定义体: integralClosure.isIntegralClosure _ _

Depends on / 依赖: integralClosure, integralClosure.isIntegralClosure, isIntegralClosure
-/
instance : IsIntegralClosure (ringOfIntegers F K) F[X] K :=
  integralClosure.isIntegralClosure _ _

variable [Algebra F⟮X⟯ K] [IsScalarTower F[X] F⟮X⟯ K]

/--
theorem `algebraMap_injective` / 定理 `algebraMap_injective`

English:
theorem algebraMap_injective
  statement: Function.Injective (algebraMap F[X] (ringOfIntegers F K))
  proof: by
  have hinj : Function.Injective (algebraMap F[X] K) := by
    rw [IsScalarTower.algebraMap_eq F[X] F⟮X⟯ K]
    exact (algebraMap F⟮X⟯ K).injective.comp (IsFractionRing.injective F[X] F⟮X⟯)
  rw [injective_iff_map_eq_zero (algebraMap F[X] (↥(ringOfIntegers F K)))]
  intro p hp
  rw [← Subtype.coe_inj]; rw [Subalgebra.coe_zero] at hp
  rw [injective_iff_map_eq_zero (algebraMap F[X] K)] at hinj
  exact hinj p hp

中文:
定理 algebraMap_injective
  结论: 函数.单射 (algebraMap F[X] (ringOf整数egers F K))
  证明: by
  have hinj : Function.Injective (algebraMap F[X] K) := by
    rw [IsScalarTower.algebraMap_eq F[X] F⟮X⟯ K]
    exact (algebraMap F⟮X⟯ K).injective.comp (IsFractionRing.injective F[X] F⟮X⟯)
  rw [injective_iff_map_eq_zero (algebraMap F[X] (↥(ringOfIntegers F K)))]
  intro p hp
  rw [← Subtype.coe_inj]; rw [Subalgebra.coe_zero] at hp
  rw [injective_iff_map_eq_zero (algebraMap F[X] K)] at hinj
  exact hinj p hp

Depends on / 依赖: Function, Function.Injective, Injective, IsFractionRing, IsFractionRing.injective, IsScalarTower, IsScalarTower.algebraMap_eq, Subalgebra, Subalgebra.coe_zero, Subtype, Subtype.coe_inj, algebraMap, algebraMap_eq, coe_inj, coe_zero, injective, injective.comp, injective_iff_map_eq_zero, ringOfIntegers
-/
theorem algebraMap_injective : Function.Injective (algebraMap F[X] (ringOfIntegers F K)) := by
  have hinj : Function.Injective (algebraMap F[X] K) := by
    rw [IsScalarTower.algebraMap_eq F[X] F⟮X⟯ K]
    exact (algebraMap F⟮X⟯ K).injective.comp (IsFractionRing.injective F[X] F⟮X⟯)
  rw [injective_iff_map_eq_zero (algebraMap F[X] (↥(ringOfIntegers F K)))]
  intro p hp
  rw [← Subtype.coe_inj]; rw [Subalgebra.coe_zero] at hp
  rw [injective_iff_map_eq_zero (algebraMap F[X] K)] at hinj
  exact hinj p hp

/--
theorem `not_isField` / 定理 `not_isField`

English:
theorem not_isField
  statement: ¬IsField (ringOfIntegers F K)
  proof: by
  simpa [← (IsIntegralClosure.isIntegral_algebra F[X] K).isField_iff_isField
      (algebraMap_injective F K)] using
    Polynomial.not_isField F

中文:
定理 not_isField
  结论: ¬是域 (ringOf整数egers F K)
  证明: by
  simpa [← (IsIntegralClosure.isIntegral_algebra F[X] K).isField_iff_isField
      (algebraMap_injective F K)] using
    Polynomial.not_isField F

Depends on / 依赖: IsIntegralClosure, IsIntegralClosure.isIntegral_algebra, Polynomial, Polynomial.not_isField, algebraMap_injective, isField_iff_isField, isIntegral_algebra, not_isField
-/
theorem not_isField : ¬IsField (ringOfIntegers F K) := by
  simpa [← (IsIntegralClosure.isIntegral_algebra F[X] K).isField_iff_isField
      (algebraMap_injective F K)] using
    Polynomial.not_isField F

variable [FunctionField F K]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsFractionRing (ringOfIntegers F K) K
  body: integralClosure.isFractionRing_of_finite_extension F⟮X⟯ K

中文:
实例 :
  签名: IsFractionRing (ringOf整数egers F K) K
  定义体: integralClosure.isFractionRing_of_finite_extension F⟮X⟯ K

Depends on / 依赖: integralClosure, integralClosure.isFractionRing_of_finite_extension, isFractionRing_of_finite_extension
-/
instance : IsFractionRing (ringOfIntegers F K) K :=
  integralClosure.isFractionRing_of_finite_extension F⟮X⟯ K

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIntegrallyClosed (ringOfIntegers F K)
  body: integralClosure.isIntegrallyClosedOfFiniteExtension F⟮X⟯

中文:
实例 :
  签名: 是整闭 (ringOf整数egers F K)
  定义体: integralClosure.isIntegrallyClosedOfFiniteExtension F⟮X⟯

Depends on / 依赖: integralClosure, integralClosure.isIntegrallyClosedOfFiniteExtension, isIntegrallyClosedOfFiniteExtension
-/
instance : IsIntegrallyClosed (ringOfIntegers F K) :=
  integralClosure.isIntegrallyClosedOfFiniteExtension F⟮X⟯

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Algebra.IsSeparable
  signature: F⟮X⟯ K] : IsNoetherian F[X] (ringOfIntegers F K)
  body: IsIntegralClosure.isNoetherian _ F⟮X⟯ K _

中文:
实例 [代数.是可分
  签名: F⟮X⟯ K] : 是Noether F[X] (ringOf整数egers F K)
  定义体: IsIntegralClosure.isNoetherian _ F⟮X⟯ K _

Depends on / 依赖: IsIntegralClosure, IsIntegralClosure.isNoetherian, isNoetherian
-/
instance [Algebra.IsSeparable F⟮X⟯ K] : IsNoetherian F[X] (ringOfIntegers F K) :=
  IsIntegralClosure.isNoetherian _ F⟮X⟯ K _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Algebra.IsSeparable
  signature: F⟮X⟯ K] : IsDedekindDomain (ringOfIntegers F K)
  body: IsIntegralClosure.isDedekindDomain F[X] F⟮X⟯ K _

中文:
实例 [代数.是可分
  签名: F⟮X⟯ K] : 是Dedekind整环 (ringOf整数egers F K)
  定义体: IsIntegralClosure.isDedekindDomain F[X] F⟮X⟯ K _

Depends on / 依赖: IsIntegralClosure, IsIntegralClosure.isDedekindDomain, isDedekindDomain
-/
instance [Algebra.IsSeparable F⟮X⟯ K] : IsDedekindDomain (ringOfIntegers F K) :=
  IsIntegralClosure.isDedekindDomain F[X] F⟮X⟯ K _

end ringOfIntegers

section deprecated

@[deprecated RatFunc.inftyValuationDef (since := "2026-04-14")]
alias inftyValuationDef := RatFunc.inftyValuationDef

@[deprecated RatFunc.InftyValuation.map_zero' (since := "2026-04-14")]
alias InftyValuation.map_zero' := RatFunc.InftyValuation.map_zero'

@[deprecated RatFunc.InftyValuation.map_one' (since := "2026-04-14")]
alias InftyValuation.map_one' := RatFunc.InftyValuation.map_one'

@[deprecated RatFunc.InftyValuation.map_mul' (since := "2026-04-14")]
alias InftyValuation.map_mul' := RatFunc.InftyValuation.map_mul'

@[deprecated RatFunc.InftyValuation.map_add_le_max' (since := "2026-04-14")]
alias InftyValuation.map_add_le_max' := RatFunc.InftyValuation.map_add_le_max'

@[deprecated RatFunc.inftyValuation_of_nonzero (since := "2026-04-14")]
alias inftyValuation_of_nonzero := RatFunc.inftyValuation_of_nonzero

@[deprecated RatFunc.inftyValuation (since := "2026-04-14")]
alias inftyValuation := RatFunc.inftyValuation

@[deprecated RatFunc.inftyValuation_apply (since := "2026-04-14")]
alias inftyValuation_apply := RatFunc.inftyValuation_apply

@[deprecated RatFunc.inftyValuation.C (since := "2026-04-14")]
alias inftyValuation.C := RatFunc.inftyValuation.C

@[deprecated RatFunc.inftyValuation.X (since := "2026-04-14")]
alias inftyValuation.X := RatFunc.inftyValuation.X

@[deprecated RatFunc.inftyValuation.X_zpow (since := "2026-04-14")]
alias inftyValuation.X_zpow := RatFunc.inftyValuation.X_zpow

@[deprecated RatFunc.inftyValuation.X_inv (since := "2026-04-14")]
alias inftyValuation.X_inv := RatFunc.inftyValuation.X_inv

@[deprecated RatFunc.inftyValuation.polynomial (since := "2026-04-14")]
alias inftyValuation.polynomial := RatFunc.inftyValuation.polynomial

@[deprecated RatFunc.inftyValued (since := "2026-04-14")]
alias inftyValuedFqt := RatFunc.inftyValued

@[deprecated RatFunc.inftyValued.def (since := "2026-04-14")]
alias inftyValuedFqt.def := RatFunc.inftyValued.def

@[deprecated RatFunc.CompletionAtInfty (since := "2026-04-14")]
alias FqtInfty := RatFunc.CompletionAtInfty

@[deprecated "Use the anonymous `Valued` instance on `RatFunc.CompletionAtInfty`"
(since := "2026-04-14")]
/--
Instance `valuedFqtInfty` / 实例 `valuedFqtInfty`

English:
instance valuedFqtInfty
  signature: [DecidableEq F⟮X⟯]
  body: inferInstance

@[deprecated RatFunc.valuedCompletionAtInfty.def (since := "2026-04-14")]
alias valuedFqtInfty.def := RatFunc.valuedCompletionAtInfty.def

中文:
实例 valuedFqtInfty
  签名: [DecidableEq F⟮X⟯]
  定义体: inferInstance

@[deprecated RatFunc.valuedCompletionAtInfty.def (since := "2026-04-14")]
alias valuedFqtInfty.def := RatFunc.valuedCompletionAtInfty.def
-/
instance valuedFqtInfty [DecidableEq F⟮X⟯] :
    Valued (RatFunc.CompletionAtInfty F) Intᵐ⁰ :=
  inferInstance

@[deprecated RatFunc.valuedCompletionAtInfty.def (since := "2026-04-14")]
alias valuedFqtInfty.def := RatFunc.valuedCompletionAtInfty.def

end deprecated

section AdjoinTranscendental

open IntermediateField RatFunc

variable {F K : Type*} [Field F] [Field K] [Algebra F⟮X⟯ K] [FunctionField F K]

/--
Instance `FiniteDimensional.adjoin_X` / 实例 `FiniteDimensional.adjoin_X`

English:
instance FiniteDimensional.adjoin_X
  signature: : FiniteDimensional F⟮(X : F⟮X⟯)⟯ K
  body: have : Module.Finite (⊤ : IntermediateField F F⟮X⟯) F⟮X⟯ :=
    .top_left F⟮X⟯ F⟮X⟯
  RatFunc.adjoin_X (K := F) ▸ Module.Finite.trans F⟮X⟯ _

中文:
实例 有限维.adjoin_X
  签名: : 有限维 F⟮(X : F⟮X⟯)⟯ K
  定义体: have : Module.Finite (⊤ : IntermediateField F F⟮X⟯) F⟮X⟯ :=
    .top_left F⟮X⟯ F⟮X⟯
  RatFunc.adjoin_X (K := F) ▸ Module.Finite.trans F⟮X⟯ _

Depends on / 依赖: Finite, IntermediateField, Module, Module.Finite, Module.Finite.trans, RatFunc, RatFunc.adjoin_X, adjoin_X, top_left
-/
instance FiniteDimensional.adjoin_X : FiniteDimensional F⟮(X : F⟮X⟯)⟯ K :=
  have : Module.Finite (⊤ : IntermediateField F F⟮X⟯) F⟮X⟯ :=
    .top_left F⟮X⟯ F⟮X⟯
  RatFunc.adjoin_X (K := F) ▸ Module.Finite.trans F⟮X⟯ _

variable [Algebra F K] [IsScalarTower F F⟮X⟯ K]

/--
theorem `FiniteDimensional.adjoin_algebraMap_X` / 定理 `FiniteDimensional.adjoin_algebraMap_X`

English:
theorem FiniteDimensional.adjoin_algebraMap_X
  proof: .of_restrictScalars_finite F⟮(X : F⟮X⟯)⟯ _ _

中文:
定理 有限维.adjoin_algebraMap_X
  证明: .of_restrictScalars_finite F⟮(X : F⟮X⟯)⟯ _ _

Depends on / 依赖: of_restrictScalars_finite
-/
theorem FiniteDimensional.adjoin_algebraMap_X :
    FiniteDimensional F⟮algebraMap _ K (X : F⟮X⟯)⟯ K :=
  .of_restrictScalars_finite F⟮(X : F⟮X⟯)⟯ _ _

/--
theorem `Algebra.IsAlgebraic.adjoin_algebraMap_X` / 定理 `Algebra.IsAlgebraic.adjoin_algebraMap_X`

English:
theorem Algebra.IsAlgebraic.adjoin_algebraMap_X
  proof: by
  exact .tower_top (K := F⟮(X : F⟮X⟯)⟯) _

中文:
定理 代数.是代数.adjoin_algebraMap_X
  证明: by
  exact .tower_top (K := F⟮(X : F⟮X⟯)⟯) _

Depends on / 依赖: tower_top
-/
theorem Algebra.IsAlgebraic.adjoin_algebraMap_X :
    Algebra.IsAlgebraic F⟮algebraMap _ K (X : F⟮X⟯)⟯ K := by
  exact .tower_top (K := F⟮(X : F⟮X⟯)⟯) _

variable {y : K}

/--
theorem `isAlgebraic_X_over_adjoin_transcendental` / 定理 `isAlgebraic_X_over_adjoin_transcendental`

English:
theorem isAlgebraic_X_over_adjoin_transcendental
  given: (hy : Transcendental F y)
  proof: isAlgebraic_adjoin_iff.mpr (.adjoin_singleton transcendental_X hy
    (isAlgebraic_adjoin_iff.mp (Algebra.IsAlgebraic.isAlgebraic y)))

中文:
定理 isAlgebraic_X_over_adjoin_transcendental
  条件: (hy : 超越 F y)
  证明: isAlgebraic_adjoin_iff.mpr (.adjoin_singleton transcendental_X hy
    (isAlgebraic_adjoin_iff.mp (Algebra.IsAlgebraic.isAlgebraic y)))

Depends on / 依赖: Algebra, Algebra.IsAlgebraic.isAlgebraic, IsAlgebraic, adjoin_singleton, isAlgebraic, isAlgebraic_adjoin_iff, isAlgebraic_adjoin_iff.mp, isAlgebraic_adjoin_iff.mpr, transcendental_X
-/
theorem isAlgebraic_X_over_adjoin_transcendental (hy : Transcendental F y) :
    IsAlgebraic F⟮y⟯ (algebraMap _ K (X : F⟮X⟯)) :=
  isAlgebraic_adjoin_iff.mpr (.adjoin_singleton transcendental_X hy
    (isAlgebraic_adjoin_iff.mp (Algebra.IsAlgebraic.isAlgebraic y)))

/--
lemma `finiteDimensional_of_adjoin_transcendental` / 引理 `finiteDimensional_of_adjoin_transcendental`

English:
lemma finiteDimensional_of_adjoin_transcendental
  given: (hy : Transcendental F y)
  proof: -- Local definitions for convenience
  let x := algebraMap _ K (X : F⟮X⟯)
  let Fyx := restrictScalars F F⟮y⟯⟮x⟯
  let Fxy := restrictScalars F F⟮x⟯⟮y⟯
  -- Recalling instance to speed up search
  let : Algebra F⟮y⟯ Fyx := F⟮y⟯⟮x⟯.algebra
  let : Module F⟮y⟯ Fyx := Algebra.toModule
  let : SMul F⟮y⟯ Fyx := Algebra.toSMul
  let : Algebra F⟮x⟯ Fxy := F⟮x⟯⟮y⟯.algebra
  let : Module F⟮x⟯ Fxy := Algebra.toModule
  let : SMul F⟮x⟯ Fxy := Algebra.toSMul
  have : FiniteDimensional F⟮y⟯ Fyx :=
    adjoin.finiteDimensional
      (isAlgebraic_iff_isIntegral.mp (isAlgebraic_X_over_adjoin_transcendental hy))
  have : FiniteDimensional Fyx K := by
    have := FiniteDimensional.adjoin_algebraMap_X (F := F) (K := K)
    unfold Fyx
    rw [adjoin_simple_comm]
    have : IsScalarTower F⟮x⟯ Fxy K := isScalarTower_mid' F⟮x⟯⟮y⟯
    exact .right F⟮x⟯ Fxy K
  have : IsScalarTower F⟮y⟯ Fyx K := isScalarTower_mid' F⟮y⟯⟮x⟯
  .trans F⟮y⟯ Fyx K

中文:
引理 finiteDimensional_of_adjoin_transcendental
  条件: (hy : 超越 F y)
  证明: -- Local definitions for convenience
  let x := algebraMap _ K (X : F⟮X⟯)
  let Fyx := restrictScalars F F⟮y⟯⟮x⟯
  let Fxy := restrictScalars F F⟮x⟯⟮y⟯
  -- Recalling instance to speed up search
  let : Algebra F⟮y⟯ Fyx := F⟮y⟯⟮x⟯.algebra
  let : Module F⟮y⟯ Fyx := Algebra.toModule
  let : SMul F⟮y⟯ Fyx := Algebra.toSMul
  let : Algebra F⟮x⟯ Fxy := F⟮x⟯⟮y⟯.algebra
  let : Module F⟮x⟯ Fxy := Algebra.toModule
  let : SMul F⟮x⟯ Fxy := Algebra.toSMul
  have : FiniteDimensional F⟮y⟯ Fyx :=
    adjoin.finiteDimensional
      (isAlgebraic_iff_isIntegral.mp (isAlgebraic_X_over_adjoin_transcendental hy))
  have : FiniteDimensional Fyx K := by
    have := FiniteDimensional.adjoin_algebraMap_X (F := F) (K := K)
    unfold Fyx
    rw [adjoin_simple_comm]
    have : IsScalarTower F⟮x⟯ Fxy K := isScalarTower_mid' F⟮x⟯⟮y⟯
    exact .right F⟮x⟯ Fxy K
  have : IsScalarTower F⟮y⟯ Fyx K := isScalarTower_mid' F⟮y⟯⟮x⟯
  .trans F⟮y⟯ Fyx K
-/
lemma finiteDimensional_of_adjoin_transcendental (hy : Transcendental F y) :
    FiniteDimensional F⟮y⟯ K :=
  -- Local definitions for convenience
  let x := algebraMap _ K (X : F⟮X⟯)
  let Fyx := restrictScalars F F⟮y⟯⟮x⟯
  let Fxy := restrictScalars F F⟮x⟯⟮y⟯
  -- Recalling instance to speed up search
  let : Algebra F⟮y⟯ Fyx := F⟮y⟯⟮x⟯.algebra
  let : Module F⟮y⟯ Fyx := Algebra.toModule
  let : SMul F⟮y⟯ Fyx := Algebra.toSMul
  let : Algebra F⟮x⟯ Fxy := F⟮x⟯⟮y⟯.algebra
  let : Module F⟮x⟯ Fxy := Algebra.toModule
  let : SMul F⟮x⟯ Fxy := Algebra.toSMul
  have : FiniteDimensional F⟮y⟯ Fyx :=
    adjoin.finiteDimensional
      (isAlgebraic_iff_isIntegral.mp (isAlgebraic_X_over_adjoin_transcendental hy))
  have : FiniteDimensional Fyx K := by
    have := FiniteDimensional.adjoin_algebraMap_X (F := F) (K := K)
    unfold Fyx
    rw [adjoin_simple_comm]
    have : IsScalarTower F⟮x⟯ Fxy K := isScalarTower_mid' F⟮x⟯⟮y⟯
    exact .right F⟮x⟯ Fxy K
  have : IsScalarTower F⟮y⟯ Fyx K := isScalarTower_mid' F⟮y⟯⟮x⟯
  .trans F⟮y⟯ Fyx K

end AdjoinTranscendental

section constantExtension

open RatFunc

variable {F}
variable [Algebra F[X] K] [FaithfulSMul F[X] K] [FunctionField F K]

attribute [local instance] Polynomial.algebra

section Unbundled

open Polynomial

variable {E : Type*} [Field E] [Algebra F E] [Algebra E[X] K] [FaithfulSMul E[X] K]

/--
theorem `finiteDimensional_ratFunc_of_constantExtension` / 定理 `finiteDimensional_ratFunc_of_constantExtension`

English:
theorem finiteDimensional_ratFunc_of_constantExtension
  given: [IsScalarTower F[X] E[X] K]
  proof: .equiv (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F⟮X⟯ E⟮X⟯ K)).toLinearEquiv.symm

中文:
定理 finiteDimensional_ratFunc_of_constantExtension
  条件: [标量塔 F[X] E[X] K]
  证明: .equiv (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F⟮X⟯ E⟮X⟯ K)).toLinearEquiv.symm

Depends on / 依赖: AlgEquiv, AlgEquiv.ofInjectiveField, IsScalarTower, IsScalarTower.toAlgHom, ofInjectiveField, toAlgHom, toLinearEquiv, toLinearEquiv.symm
-/
theorem finiteDimensional_ratFunc_of_constantExtension [IsScalarTower F[X] E[X] K] :
    FiniteDimensional F⟮X⟯ E⟮X⟯ :=
  .equiv (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F⟮X⟯ E⟮X⟯ K)).toLinearEquiv.symm

/--
theorem `finiteDimensional_of_constantExtension` / 定理 `finiteDimensional_of_constantExtension`

English:
theorem finiteDimensional_of_constantExtension
  statement: [IsScalarTower F[X] E[X] K]
  proof: have := finiteDimensional_ratFunc_of_constantExtension (F := F) (E := E) K
  Module.finite_of_finrank_pos ((finrank_ratFunc_ratFunc F E) ▸ Module.finrank_pos)

中文:
定理 finiteDimensional_of_constantExtension
  结论: [标量塔 F[X] E[X] K]
  证明: have := finiteDimensional_ratFunc_of_constantExtension (F := F) (E := E) K
  Module.finite_of_finrank_pos ((finrank_ratFunc_ratFunc F E) ▸ Module.finrank_pos)

Depends on / 依赖: Module, Module.finite_of_finrank_pos, Module.finrank_pos, finiteDimensional_ratFunc_of_constantExtension, finite_of_finrank_pos, finrank_pos, finrank_ratFunc_ratFunc
-/
theorem finiteDimensional_of_constantExtension [IsScalarTower F[X] E[X] K]
    [Algebra.IsAlgebraic F E] : FiniteDimensional F E :=
  have := finiteDimensional_ratFunc_of_constantExtension (F := F) (E := E) K
  Module.finite_of_finrank_pos ((finrank_ratFunc_ratFunc F E) ▸ Module.finrank_pos)

end Unbundled

section IntermediateField

variable [Algebra F K] (E : IntermediateField F K) [Algebra E[X] K] [FaithfulSMul E[X] K]
  [IsScalarTower F[X] E[X] K]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FiniteDimensional F⟮X⟯ E⟮X⟯
  body: finiteDimensional_ratFunc_of_constantExtension K

中文:
实例 :
  签名: 有限维 F⟮X⟯ E⟮X⟯
  定义体: finiteDimensional_ratFunc_of_constantExtension K

Depends on / 依赖: finiteDimensional_ratFunc_of_constantExtension
-/
instance : FiniteDimensional F⟮X⟯ E⟮X⟯ :=
  finiteDimensional_ratFunc_of_constantExtension K

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Algebra.IsAlgebraic
  signature: F E] : FiniteDimensional F E
  body: finiteDimensional_of_constantExtension K

中文:
实例 [代数.是代数
  签名: F E] : 有限维 F E
  定义体: finiteDimensional_of_constantExtension K

Depends on / 依赖: finiteDimensional_of_constantExtension
-/
instance [Algebra.IsAlgebraic F E] : FiniteDimensional F E :=
  finiteDimensional_of_constantExtension K

end IntermediateField

end constantExtension

end FunctionField
