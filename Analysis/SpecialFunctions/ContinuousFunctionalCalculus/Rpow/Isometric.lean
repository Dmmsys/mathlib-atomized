/-
Copyright (c) 2025 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity

/-! # Properties of `rpow` and `sqrt` over an algebra with an isometric CFC

This file collects results about `CFC.rpow`, `CFC.nnrpow` and `CFC.sqrt` that use facts that
rely on an isometric continuous functional calculus.

## Main theorems

* Various versions of `‖a ^ r‖ = ‖a‖ ^ r` and `‖CFC.sqrt a‖ = sqrt ‖a‖`.

## Tags

continuous functional calculus, rpow, sqrt
-/

public section

open scoped NNReal

namespace CFC

section nonunital

variable {A : Type*} [NonUnitalNormedRing A] [StarRing A] [NormedSpace Real A] [IsScalarTower Real A A]
  [SMulCommClass Real A A] [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass Real A]
  [NonUnitalIsometricContinuousFunctionalCalculus Real A IsSelfAdjoint]

/--
lemma `nnnorm_nnrpow` / 引理 `nnnorm_nnrpow`

English:
lemma nnnorm_nnrpow
  given: (a : A) {r : Real>=0} (hr : 0 < r) (ha : 0 <= a := by cfc_tac)
  proof: .nnnorm_cfcₙ _ _ .monotoneOn _ NNReal.monotone_nnrpow_const r

中文:
引理 nnnorm_nnrpow
  条件: (a : A) {r : 实数>=0} (hr : 0 < r) (ha : 0 <= a := by cfc_tac)
  证明: .nnnorm_cfcₙ _ _ .monotoneOn _ NNReal.monotone_nnrpow_const r

Depends on / 依赖: NNReal, NNReal.monotone_nnrpow_const, cfc_tac, monotoneOn, monotone_nnrpow_const
-/
lemma nnnorm_nnrpow (a : A) {r : Real>=0} (hr : 0 < r) (ha : 0 <= a := by cfc_tac) :
    ‖a ^ r‖₊ = ‖a‖₊ ^ (r : Real) :=
.nnnorm_cfcₙ _ _ .monotoneOn _ NNReal.monotone_nnrpow_const r

/--
lemma `norm_nnrpow` / 引理 `norm_nnrpow`

English:
lemma norm_nnrpow
  given: (a : A) {r : Real>=0} (hr : 0 < r) (ha : 0 <= a := by cfc_tac)
  proof: congr(NNReal.toReal $(nnnorm_nnrpow a hr ha))

中文:
引理 norm_nnrpow
  条件: (a : A) {r : 实数>=0} (hr : 0 < r) (ha : 0 <= a := by cfc_tac)
  证明: congr(NNReal.toReal $(nnnorm_nnrpow a hr ha))

Depends on / 依赖: HomologicalComplex, HomologicalComplex.extendMap_f, HomologicalComplex.extendSingleIso_hom_f, NNReal, NNReal.toReal, cat_disch, cfc_tac, extendMap_f, extendSingleIso_hom_f, nnnorm_nnrpow, toReal
-/
lemma norm_nnrpow (a : A) {r : Real>=0} (hr : 0 < r) (ha : 0 <= a := by cfc_tac) :
    ‖a ^ r‖ = ‖a‖ ^ (r : Real) :=
  congr(NNReal.toReal $(nnnorm_nnrpow a hr ha))

/--
lemma `nnnorm_sqrt` / 引理 `nnnorm_sqrt`

English:
lemma nnnorm_sqrt
  given: (a : A) (ha : 0 <= a := by cfc_tac)
  statement: ‖sqrt a‖₊ = NNReal.sqrt ‖a‖₊
  proof: by
  rw [sqrt_eq_nnrpow]; rw [NNReal.sqrt_eq_rpow]
  exact nnnorm_nnrpow a (by simp) ha

中文:
引理 nnnorm_sqrt
  条件: (a : A) (ha : 0 <= a := by cfc_tac)
  结论: ‖sqrt a‖₊ = 非负实数.sqrt ‖a‖₊
  证明: by
  rw [sqrt_eq_nnrpow]; rw [NNReal.sqrt_eq_rpow]
  exact nnnorm_nnrpow a (by simp) ha

Depends on / 依赖: NNReal, NNReal.sqrt, NNReal.sqrt_eq_rpow, cfc_tac, nnnorm_nnrpow, sqrt_eq_nnrpow, sqrt_eq_rpow
-/
lemma nnnorm_sqrt (a : A) (ha : 0 <= a := by cfc_tac) : ‖sqrt a‖₊ = NNReal.sqrt ‖a‖₊ := by
  rw [sqrt_eq_nnrpow]; rw [NNReal.sqrt_eq_rpow]
  exact nnnorm_nnrpow a (by simp) ha

/--
lemma `norm_sqrt` / 引理 `norm_sqrt`

English:
lemma norm_sqrt
  given: (a : A) (ha : 0 <= a := by cfc_tac)
  statement: ‖sqrt a‖ = √‖a‖
  proof: by
  simpa using congr(NNReal.toReal $(nnnorm_sqrt a ha))

中文:
引理 norm_sqrt
  条件: (a : A) (ha : 0 <= a := by cfc_tac)
  结论: ‖sqrt a‖ = √‖a‖
  证明: by
  simpa using congr(NNReal.toReal $(nnnorm_sqrt a ha))

Depends on / 依赖: NNReal, NNReal.toReal, cfc_tac, nnnorm_sqrt, toReal
-/
lemma norm_sqrt (a : A) (ha : 0 <= a := by cfc_tac) : ‖sqrt a‖ = √‖a‖ := by
  simpa using congr(NNReal.toReal $(nnnorm_sqrt a ha))

variable [ContinuousStar A] [CompleteSpace A]

/--
lemma `continuousOn_sqrt` / 引理 `continuousOn_sqrt`

English:
lemma continuousOn_sqrt
  statement: ContinuousOn sqrt {a : A | 0 <= a}
  proof: continuousOn_id.cfcₙ_nnreal_of_mem_nhdsSet _ Filter.univ_mem

中文:
引理 continuousOn_sqrt
  结论: ContinuousOn sqrt {a : A | 0 <= a}
  证明: continuousOn_id.cfcₙ_nnreal_of_mem_nhdsSet _ Filter.univ_mem

Depends on / 依赖: Filter, Filter.univ_mem, continuousOn_id, continuousOn_id.cfc, univ_mem
-/
lemma continuousOn_sqrt : ContinuousOn sqrt {a : A | 0 <= a} :=
  continuousOn_id.cfcₙ_nnreal_of_mem_nhdsSet _ Filter.univ_mem

/--
lemma `continuousOn_nnrpow` / 引理 `continuousOn_nnrpow`

English:
lemma continuousOn_nnrpow
  given: (r : Real>=0)
  statement: ContinuousOn (· ^ r) {a : A | 0 <= a}
  proof: by
  obtain (rfl | hr) := eq_zero_or_pos r
  · simpa using continuousOn_const
  · exact continuousOn_id.cfcₙ_nnreal_of_mem_nhdsSet _ Filter.univ_mem

中文:
引理 continuousOn_nnrpow
  条件: (r : 实数>=0)
  结论: ContinuousOn (· ^ r) {a : A | 0 <= a}
  证明: by
  obtain (rfl | hr) := eq_zero_or_pos r
  · simpa using continuousOn_const
  · exact continuousOn_id.cfcₙ_nnreal_of_mem_nhdsSet _ Filter.univ_mem

Depends on / 依赖: ComplexShape, ComplexShape.embeddingDownNat, Filter, Filter.univ_mem, HomologicalComplex, HomologicalComplex.extendMap_f, cochainComplexXIso, continuousOn_const, continuousOn_id, continuousOn_id.cfc, embeddingDownNat, eq_zero_or_pos, extendMap_f, univ_mem
-/
lemma continuousOn_nnrpow (r : Real>=0) : ContinuousOn (· ^ r) {a : A | 0 <= a} := by
  obtain (rfl | hr) := eq_zero_or_pos r
  · simpa using continuousOn_const
  · exact continuousOn_id.cfcₙ_nnreal_of_mem_nhdsSet _ Filter.univ_mem

end nonunital

section unital

variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra Real A]
  [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass Real A]
  [IsometricContinuousFunctionalCalculus Real A IsSelfAdjoint]

/--
lemma `nnnorm_rpow` / 引理 `nnnorm_rpow`

English:
lemma nnnorm_rpow
  given: (a : A) {r : Real} (hr : 0 < r) (ha : 0 <= a := by cfc_tac)
  proof: by
  lift r to Real>=0 using hr.le
  rw [← nnrpow_eq_rpow]; rw [← nnnorm_nnrpow a]
  all_goals simpa

中文:
引理 nnnorm_rpow
  条件: (a : A) {r : 实数} (hr : 0 < r) (ha : 0 <= a := by cfc_tac)
  证明: by
  lift r to Real>=0 using hr.le
  rw [← nnrpow_eq_rpow]; rw [← nnnorm_nnrpow a]
  all_goals simpa

Depends on / 依赖: CochainComplex, CochainComplex.singleFunctor, CochainComplex.singleFunctors, HomologicalComplex, HomologicalComplex.single, HomologicalComplex.singleObjXIsoOfEq, HomologicalComplex.singleObjXSelf, HomologicalComplex.to_single_hom_ext, _f_zero, all_goals, cfc_tac, hr.le, nnnorm_nnrpow, nnrpow_eq_rpow, single, singleFunctor, singleFunctors, singleObjXIsoOfEq, singleObjXSelf, to_single_hom_ext
-/
lemma nnnorm_rpow (a : A) {r : Real} (hr : 0 < r) (ha : 0 <= a := by cfc_tac) :
    ‖a ^ r‖₊ = ‖a‖₊ ^ r := by
  lift r to Real>=0 using hr.le
  rw [← nnrpow_eq_rpow]; rw [← nnnorm_nnrpow a]
  all_goals simpa

/--
lemma `norm_rpow` / 引理 `norm_rpow`

English:
lemma norm_rpow
  given: (a : A) {r : Real} (hr : 0 < r) (ha : 0 <= a := by cfc_tac)
  proof: congr(NNReal.toReal $(nnnorm_rpow a hr ha))

中文:
引理 norm_rpow
  条件: (a : A) {r : 实数} (hr : 0 < r) (ha : 0 <= a := by cfc_tac)
  证明: congr(NNReal.toReal $(nnnorm_rpow a hr ha))

Depends on / 依赖: NNReal, NNReal.toReal, cfc_tac, nnnorm_rpow, toReal
-/
lemma norm_rpow (a : A) {r : Real} (hr : 0 < r) (ha : 0 <= a := by cfc_tac) :
    ‖a ^ r‖ = ‖a‖ ^ r :=
  congr(NNReal.toReal $(nnnorm_rpow a hr ha))

/--
lemma `continuousOn_rpow` / 引理 `continuousOn_rpow`

English:
lemma continuousOn_rpow
  given: [ContinuousStar A] [CompleteSpace A] (r : Real)
  proof: by
  refine continuousOn_id.cfc_nnreal_of_mem_nhdsSet _ (s := {0}ᶜ) ?_
  simp_rw [nhdsSet_iUnion, Filter.mem_iSup, isOpen_compl_singleton.mem_nhdsSet]
  exact fun a ha => by simpa using spectrum.zero_notMem _ ha.isUnit

中文:
引理 continuousOn_rpow
  条件: [余ntinuousStar A] [完备空间 A] (r : 实数)
  证明: by
  refine continuousOn_id.cfc_nnreal_of_mem_nhdsSet _ (s := {0}ᶜ) ?_
  simp_rw [nhdsSet_iUnion, Filter.mem_iSup, isOpen_compl_singleton.mem_nhdsSet]
  exact fun a ha => by simpa using spectrum.zero_notMem _ ha.isUnit

Depends on / 依赖: Filter, Filter.mem_iSup, cfc_nnreal_of_mem_nhdsSet, continuousOn_id, continuousOn_id.cfc_nnreal_of_mem_nhdsSet, ha.isUnit, isOpen_compl_singleton, isOpen_compl_singleton.mem_nhdsSet, isUnit, mem_iSup, mem_nhdsSet, nhdsSet_iUnion, simp_rw, spectrum, spectrum.zero_notMem, zero_notMem
-/
lemma continuousOn_rpow [ContinuousStar A] [CompleteSpace A] (r : Real) :
    ContinuousOn (· ^ r) {a : A | IsStrictlyPositive a} := by
  refine continuousOn_id.cfc_nnreal_of_mem_nhdsSet _ (s := {0}ᶜ) ?_
  simp_rw [nhdsSet_iUnion, Filter.mem_iSup, isOpen_compl_singleton.mem_nhdsSet]
  exact fun a ha => by simpa using spectrum.zero_notMem _ ha.isUnit

end unital

section cstar

variable {A : Type*} [PartialOrder A] [NonUnitalNormedRing A] [StarRing A] [CStarRing A]
    [NormedSpace Real A] [SMulCommClass Real A A] [IsScalarTower Real A A] [StarOrderedRing A]
    [NonUnitalContinuousFunctionalCalculus Real A IsSelfAdjoint] [NonnegSpectrumClass Real A]

/--
lemma `norm_star_mul_mul_self_of_nonneg` / 引理 `norm_star_mul_mul_self_of_nonneg`

English:
lemma norm_star_mul_mul_self_of_nonneg
  given: {a : A} (b : A) (ha : 0 <= a := by cfc_tac)
  proof: by
  rw [sq]; rw [← CStarRing.norm_star_mul_self]; rw [star_mul]; rw [(CFC.sqrt_nonneg a).star_eq]; rw [← mul_assoc _ (CFC.sqrt a)]; rw [mul_assoc _ _ (CFC.sqrt a)]; rw [CFC.sqrt_mul_sqrt_self a]

中文:
引理 norm_star_mul_mul_self_of_nonneg
  条件: {a : A} (b : A) (ha : 0 <= a := by cfc_tac)
  证明: by
  rw [sq]; rw [← CStarRing.norm_star_mul_self]; rw [star_mul]; rw [(CFC.sqrt_nonneg a).star_eq]; rw [← mul_assoc _ (CFC.sqrt a)]; rw [mul_assoc _ _ (CFC.sqrt a)]; rw [CFC.sqrt_mul_sqrt_self a]

Depends on / 依赖: CFC.sqrt, CFC.sqrt_mul_sqrt_self, CFC.sqrt_nonneg, CStarRing, CStarRing.norm_star_mul_self, cfc_tac, mul_assoc, norm_star_mul_self, sqrt_mul_sqrt_self, sqrt_nonneg, star_eq, star_mul
-/
lemma norm_star_mul_mul_self_of_nonneg {a : A} (b : A) (ha : 0 <= a := by cfc_tac) :
    ‖star b * a * b‖ = ‖CFC.sqrt a * b‖ ^ 2 := by
  rw [sq]; rw [← CStarRing.norm_star_mul_self]; rw [star_mul]; rw [(CFC.sqrt_nonneg a).star_eq]; rw [← mul_assoc _ (CFC.sqrt a)]; rw [mul_assoc _ _ (CFC.sqrt a)]; rw [CFC.sqrt_mul_sqrt_self a]

/--
lemma `IsSelfAdjoint.norm_mul_mul_self_of_nonneg` / 引理 `IsSelfAdjoint.norm_mul_mul_self_of_nonneg`

English:
lemma IsSelfAdjoint.norm_mul_mul_self_of_nonneg
  statement: {a : A} (b : A)
  proof: by
  simpa [hb.star_eq] using norm_star_mul_mul_self_of_nonneg b ha

中文:
引理 IsSelfAdjoint.norm_mul_mul_self_of_nonneg
  结论: {a : A} (b : A)
  证明: by
  simpa [hb.star_eq] using norm_star_mul_mul_self_of_nonneg b ha

Depends on / 依赖: CFC.sqrt, cfc_tac, hb.star_eq, norm_star_mul_mul_self_of_nonneg, star_eq
-/
lemma IsSelfAdjoint.norm_mul_mul_self_of_nonneg {a : A} (b : A)
    (hb : IsSelfAdjoint b := by cfc_tac) (ha : 0 <= a := by cfc_tac) :
    ‖b * a * b‖ = ‖CFC.sqrt a * b‖ ^ 2 := by
  simpa [hb.star_eq] using norm_star_mul_mul_self_of_nonneg b ha

/--
lemma `norm_mul_mul_star_self_of_nonneg` / 引理 `norm_mul_mul_star_self_of_nonneg`

English:
lemma norm_mul_mul_star_self_of_nonneg
  given: {a : A} (b : A) (ha : 0 <= a := by cfc_tac)
  proof: by
  conv_rhs => rw [← (CFC.sqrt_nonneg a).star_eq, ← star_star b, ← star_mul, norm_star,
    ← norm_star_mul_mul_self_of_nonneg _ ha, star_star]

中文:
引理 norm_mul_mul_star_self_of_nonneg
  条件: {a : A} (b : A) (ha : 0 <= a := by cfc_tac)
  证明: by
  conv_rhs => rw [← (CFC.sqrt_nonneg a).star_eq, ← star_star b, ← star_mul, norm_star,
    ← norm_star_mul_mul_self_of_nonneg _ ha, star_star]

Depends on / 依赖: CFC.sqrt, CFC.sqrt_nonneg, cfc_tac, conv_rhs, norm_star, norm_star_mul_mul_self_of_nonneg, sqrt_nonneg, star_eq, star_mul, star_star
-/
lemma norm_mul_mul_star_self_of_nonneg {a : A} (b : A) (ha : 0 <= a := by cfc_tac) :
    ‖b * a * star b‖ = ‖b * CFC.sqrt a‖ ^ 2 := by
  conv_rhs => rw [← (CFC.sqrt_nonneg a).star_eq, ← star_star b, ← star_mul, norm_star,
    ← norm_star_mul_mul_self_of_nonneg _ ha, star_star]

/--
lemma `IsSelfAdjoint.norm_mul_mul_self_of_nonneg'` / 引理 `IsSelfAdjoint.norm_mul_mul_self_of_nonneg'`

English:
lemma IsSelfAdjoint.norm_mul_mul_self_of_nonneg'
  statement: {a : A} (b : A)
  proof: by
  simpa [hb.star_eq] using norm_mul_mul_star_self_of_nonneg b ha

中文:
引理 IsSelfAdjoint.norm_mul_mul_self_of_nonneg'
  结论: {a : A} (b : A)
  证明: by
  simpa [hb.star_eq] using norm_mul_mul_star_self_of_nonneg b ha

Depends on / 依赖: CFC.sqrt, cfc_tac, hb.star_eq, norm_mul_mul_star_self_of_nonneg, star_eq
-/
lemma IsSelfAdjoint.norm_mul_mul_self_of_nonneg' {a : A} (b : A)
    (hb : IsSelfAdjoint b := by cfc_tac) (ha : 0 <= a := by cfc_tac) :
    ‖b * a * b‖ = ‖b * CFC.sqrt a‖ ^ 2 := by
  simpa [hb.star_eq] using norm_mul_mul_star_self_of_nonneg b ha

end cstar

end CFC
