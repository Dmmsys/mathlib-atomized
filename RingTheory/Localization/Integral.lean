/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
module

public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Localization.Algebra

/-!
# Integral and algebraic elements of a fraction field

## Implementation notes

See `Mathlib/RingTheory/Localization/Basic.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/

@[expose] public section


variable {R : Type*} [CommRing R] (M : Submonoid R) {S : Type*} [CommRing S]
variable [Algebra R S]

open Polynomial

namespace IsLocalization

section IntegerNormalization

open Polynomial

variable [IsLocalization M S]

set_option backward.isDefEq.respectTransparency.types false in
attribute [local instance] Polynomial.algebra Polynomial.isLocalization in
/--
theorem `exists_integer_polynomial_multiple_and_support_subset` / 定理 `exists_integer_polynomial_multiple_and_support_subset`

English:
theorem exists_integer_polynomial_multiple_and_support_subset
  given: (p : S[X])
  proof: by
  obtain ⟨⟨_, b, hb, rfl⟩, h⟩ := exists_integer_multiple (Submonoid.map C M) p
  rw [Subtype.coe_mk]; rw [C_eq_algebraMap]; rw [algebraMap_smul] at h
  obtain ⟨q', h₁, h₂⟩ := exists_support_eq_of_mem_lifts h
  exact ⟨b, hb, q', h₁, h₂ ▸ support_smul b p⟩

中文:
定理 存在_integer_polynomial_multiple_and_support_subset
  条件: (p : S[X])
  证明: by
  obtain ⟨⟨_, b, hb, rfl⟩, h⟩ := exists_integer_multiple (Submonoid.map C M) p
  rw [Subtype.coe_mk]; rw [C_eq_algebraMap]; rw [algebraMap_smul] at h
  obtain ⟨q', h₁, h₂⟩ := exists_support_eq_of_mem_lifts h
  exact ⟨b, hb, q', h₁, h₂ ▸ support_smul b p⟩
-/
private theorem exists_integer_polynomial_multiple_and_support_subset (p : S[X]) :
    exists b in M, exists (q : R[X]), q.map (algebraMap R S) = b • p ∧ q.support subseteq p.support := by
  obtain ⟨⟨_, b, hb, rfl⟩, h⟩ := exists_integer_multiple (Submonoid.map C M) p
  rw [Subtype.coe_mk]; rw [C_eq_algebraMap]; rw [algebraMap_smul] at h
  obtain ⟨q', h₁, h₂⟩ := exists_support_eq_of_mem_lifts h
  exact ⟨b, hb, q', h₁, h₂ ▸ support_smul b p⟩

/--
Definition of `integerNormalization` / `integerNormalization` 的定义

English:
definition integerNormalization
  signature: (p : S[X])
  body: (exists_integer_polynomial_multiple_and_support_subset M p).choose_spec.2.choose

中文:
定义 integerNormalization
  签名: (p : S[X])
  定义体: (exists_integer_polynomial_multiple_and_support_subset M p).choose_spec.2.choose
-/
@[no_expose] noncomputable def integerNormalization (p : S[X]) : R[X] :=
  (exists_integer_polynomial_multiple_and_support_subset M p).choose_spec.2.choose

/--
theorem `integerNormalization_spec` / 定理 `integerNormalization_spec`

English:
theorem integerNormalization_spec
  given: (p : S[X])
  proof: let e := exists_integer_polynomial_multiple_and_support_subset M p
  ⟨e.choose, e.choose_spec.1, e.choose_spec.2.choose_spec.1⟩

中文:
定理 integerNormalization_spec
  条件: (p : S[X])
  证明: let e := exists_integer_polynomial_multiple_and_support_subset M p
  ⟨e.choose, e.choose_spec.1, e.choose_spec.2.choose_spec.1⟩

Depends on / 依赖: choose_spec, e.choose, e.choose_spec, exists_integer_polynomial_multiple_and_support_subset
-/
theorem integerNormalization_spec (p : S[X]) :
    exists b in M, (integerNormalization M p).map (algebraMap R S) = b • p :=
  let e := exists_integer_polynomial_multiple_and_support_subset M p
  ⟨e.choose, e.choose_spec.1, e.choose_spec.2.choose_spec.1⟩

/--
theorem `integerNormalization_support` / 定理 `integerNormalization_support`

English:
theorem integerNormalization_support
  given: (p : S[X])
  proof: (exists_integer_polynomial_multiple_and_support_subset M p).choose_spec.2.choose_spec.2

中文:
定理 integerNormalization_support
  条件: (p : S[X])
  证明: (exists_integer_polynomial_multiple_and_support_subset M p).choose_spec.2.choose_spec.2

Depends on / 依赖: choose_spec, exists_integer_polynomial_multiple_and_support_subset
-/
theorem integerNormalization_support (p : S[X]) :
    (integerNormalization M p).support subseteq p.support :=
  (exists_integer_polynomial_multiple_and_support_subset M p).choose_spec.2.choose_spec.2

/-- `coeffIntegerNormalization p` gives the coefficients of the polynomial
`integerNormalization p` -/
@[deprecated integerNormalization (since := "2026-02-05")]
/--
Definition of `coeffIntegerNormalization` / `coeffIntegerNormalization` 的定义

English:
definition coeffIntegerNormalization
  signature: (p : S[X]) (i : Nat)
  body: (integerNormalization M p).coeff i

@[deprecated integerNormalization_support (since := "2026-02-05")]

中文:
定义 coeff整数egerNormalization
  签名: (p : S[X]) (i : 自然数)
  定义体: (integerNormalization M p).coeff i

@[deprecated integerNormalization_support (since := "2026-02-05")]

Depends on / 依赖: integerNormalization
-/
noncomputable def coeffIntegerNormalization (p : S[X]) (i : Nat) : R :=
  (integerNormalization M p).coeff i

@[deprecated integerNormalization_support (since := "2026-02-05")]
/--
theorem `coeffIntegerNormalization_of_coeff_zero` / 定理 `coeffIntegerNormalization_of_coeff_zero`

English:
theorem coeffIntegerNormalization_of_coeff_zero
  given: (p : S[X]) (i : Nat) (h : coeff p i = 0)
  proof: notMem_support_iff.mp Finset.not_mem_subset (integerNormalization_support M p)
    notMem_support_iff.mpr h

@[deprecated integerNormalization_support (since := "2026-02-05")]

中文:
定理 coeff整数egerNormalization_of_coeff_zero
  条件: (p : S[X]) (i : 自然数) (h : coeff p i = 0)
  证明: notMem_support_iff.mp Finset.not_mem_subset (integerNormalization_support M p)
    notMem_support_iff.mpr h

@[deprecated integerNormalization_support (since := "2026-02-05")]

Depends on / 依赖: Finset, Finset.not_mem_subset, integerNormalization_support, notMem_support_iff, notMem_support_iff.mp, notMem_support_iff.mpr, not_mem_subset
-/
theorem coeffIntegerNormalization_of_coeff_zero (p : S[X]) (i : Nat) (h : coeff p i = 0) :
    coeffIntegerNormalization M p i = 0 :=
notMem_support_iff.mp Finset.not_mem_subset (integerNormalization_support M p)
    notMem_support_iff.mpr h

@[deprecated integerNormalization_support (since := "2026-02-05")]
/--
theorem `coeffIntegerNormalization_mem_support` / 定理 `coeffIntegerNormalization_mem_support`

English:
theorem coeffIntegerNormalization_mem_support
  statement: (p : S[X]) (i : Nat)
  proof: by
  contrapose h
  simp only [mem_support_iff, ne_eq, not_not] at h
  exact coeffIntegerNormalization_of_coeff_zero M p i h

@[deprecated integerNormalization_spec (since := "2026-02-05")]

中文:
定理 coeff整数egerNormalization_mem_support
  结论: (p : S[X]) (i : 自然数)
  证明: by
  contrapose h
  simp only [mem_support_iff, ne_eq, not_not] at h
  exact coeffIntegerNormalization_of_coeff_zero M p i h

@[deprecated integerNormalization_spec (since := "2026-02-05")]

Depends on / 依赖: coeffIntegerNormalization_of_coeff_zero, contrapose, mem_support_iff, ne_eq, not_not
-/
theorem coeffIntegerNormalization_mem_support (p : S[X]) (i : Nat)
    (h : coeffIntegerNormalization M p i != 0) : i in p.support := by
  contrapose h
  simp only [mem_support_iff, ne_eq, not_not] at h
  exact coeffIntegerNormalization_of_coeff_zero M p i h

@[deprecated integerNormalization_spec (since := "2026-02-05")]
/--
theorem `integerNormalization_coeff` / 定理 `integerNormalization_coeff`

English:
theorem integerNormalization_coeff
  given: (p : S[X]) (i : Nat)
  proof: rfl

中文:
定理 integerNormalization_coeff
  条件: (p : S[X]) (i : 自然数)
  证明: rfl
-/
theorem integerNormalization_coeff (p : S[X]) (i : Nat) :
    (integerNormalization M p).coeff i = coeffIntegerNormalization M p i :=
  rfl

variable {M} in
/--
theorem `integerNormalization_eq_zero_iff` / 定理 `integerNormalization_eq_zero_iff`

English:
theorem integerNormalization_eq_zero_iff
  given: [IsDomain R] (hM : M <= nonZeroDivisors R) (p : S[X])
  proof: by
  obtain ⟨_, hb₁, hb₂⟩ := integerNormalization_spec M p
  let := isDomain_of_le_nonZeroDivisors S hM
let := (faithfulSMul_iff_algebraMap_injective R S).mpr IsLocalization.injective S hM
let : Function.Injective mapRingHom (algebraMap R S) := by
    rw [coe_mapRingHom]; rw [map_injective_iff]
    exact IsLocalization.injective S hM
  rw [← _root_.map_eq_zero_iff (mapRingHom (algebraMap R S)) this]; rw [coe_mapRingHom]; rw [hb₂]
exact smul_eq_zero_iff_right nonZeroDivisors.ne_zero (hM hb₁)

@[deprecated integerNormalization_spec (since := "2026-02-05")]

中文:
定理 integerNormalization_eq_zero_iff
  条件: [是整环 R] (hM : M <= nonZeroDivisors R) (p : S[X])
  证明: by
  obtain ⟨_, hb₁, hb₂⟩ := integerNormalization_spec M p
  let := isDomain_of_le_nonZeroDivisors S hM
let := (faithfulSMul_iff_algebraMap_injective R S).mpr IsLocalization.injective S hM
let : Function.Injective mapRingHom (algebraMap R S) := by
    rw [coe_mapRingHom]; rw [map_injective_iff]
    exact IsLocalization.injective S hM
  rw [← _root_.map_eq_zero_iff (mapRingHom (algebraMap R S)) this]; rw [coe_mapRingHom]; rw [hb₂]
exact smul_eq_zero_iff_right nonZeroDivisors.ne_zero (hM hb₁)

@[deprecated integerNormalization_spec (since := "2026-02-05")]

Depends on / 依赖: Function, Function.Injective, Injective, IsLocalization, IsLocalization.injective, _root_, _root_.map_eq_zero_iff, algebraMap, coe_mapRingHom, faithfulSMul_iff_algebraMap_injective, injective, integerNormalization_spec, isDomain_of_le_nonZeroDivisors, mapRingHom, map_eq_zero_iff, map_injective_iff, ne_zero, nonZeroDivisors, nonZeroDivisors.ne_zero, smul_eq_zero_iff_right
-/
theorem integerNormalization_eq_zero_iff [IsDomain R] (hM : M <= nonZeroDivisors R) (p : S[X]) :
    integerNormalization M p = 0 ↔ p = 0 := by
  obtain ⟨_, hb₁, hb₂⟩ := integerNormalization_spec M p
  let := isDomain_of_le_nonZeroDivisors S hM
let := (faithfulSMul_iff_algebraMap_injective R S).mpr IsLocalization.injective S hM
let : Function.Injective mapRingHom (algebraMap R S) := by
    rw [coe_mapRingHom]; rw [map_injective_iff]
    exact IsLocalization.injective S hM
  rw [← _root_.map_eq_zero_iff (mapRingHom (algebraMap R S)) this]; rw [coe_mapRingHom]; rw [hb₂]
exact smul_eq_zero_iff_right nonZeroDivisors.ne_zero (hM hb₁)

@[deprecated integerNormalization_spec (since := "2026-02-05")]
/--
theorem `integerNormalization_map_to_map` / 定理 `integerNormalization_map_to_map`

English:
theorem integerNormalization_map_to_map
  given: (p : S[X])
  proof: by
  obtain ⟨b, hb₁, hb₂⟩ := integerNormalization_spec M p
  exact ⟨⟨b, hb₁⟩, hb₂⟩

中文:
定理 integerNormalization_map_to_map
  条件: (p : S[X])
  证明: by
  obtain ⟨b, hb₁, hb₂⟩ := integerNormalization_spec M p
  exact ⟨⟨b, hb₁⟩, hb₂⟩

Depends on / 依赖: integerNormalization_spec
-/
theorem integerNormalization_map_to_map (p : S[X]) :
    exists b : M, (integerNormalization M p).map (algebraMap R S) = (b : R) • p := by
  obtain ⟨b, hb₁, hb₂⟩ := integerNormalization_spec M p
  exact ⟨⟨b, hb₁⟩, hb₂⟩

variable {R' : Type*} [CommRing R']

/--
theorem `integerNormalization_eval₂_eq_zero` / 定理 `integerNormalization_eval₂_eq_zero`

English:
theorem integerNormalization_eval₂_eq_zero
  statement: (g : S ->+* R') (p : S[X]) {x : R'}
  proof: let ⟨b, hb₁, hb₂⟩ := integerNormalization_spec M p
  _root_.trans (eval₂_map (algebraMap R S) g x).symm
    (by rw [hb₂, ← IsScalarTower.algebraMap_smul S b p, eval₂_smul, hx, mul_zero])

中文:
定理 integerNormalization_eval₂_eq_zero
  结论: (g : S ->+* R') (p : S[X]) {x : R'}
  证明: let ⟨b, hb₁, hb₂⟩ := integerNormalization_spec M p
  _root_.trans (eval₂_map (algebraMap R S) g x).symm
    (by rw [hb₂, ← IsScalarTower.algebraMap_smul S b p, eval₂_smul, hx, mul_zero])

Depends on / 依赖: IsScalarTower, IsScalarTower.algebraMap_smul, _root_, _root_.trans, algebraMap, algebraMap_smul, integerNormalization_spec, mul_zero
-/
theorem integerNormalization_eval₂_eq_zero (g : S ->+* R') (p : S[X]) {x : R'}
    (hx : eval₂ g x p = 0) : eval₂ (g.comp (algebraMap R S)) x (integerNormalization M p) = 0 :=
  let ⟨b, hb₁, hb₂⟩ := integerNormalization_spec M p
  _root_.trans (eval₂_map (algebraMap R S) g x).symm
    (by rw [hb₂, ← IsScalarTower.algebraMap_smul S b p, eval₂_smul, hx, mul_zero])

/--
theorem `integerNormalization_aeval_eq_zero` / 定理 `integerNormalization_aeval_eq_zero`

English:
theorem integerNormalization_aeval_eq_zero
  statement: [Algebra R R'] [Algebra S R'] [IsScalarTower R S R']
  proof: by
  rwa [aeval_def, IsScalarTower.algebraMap_eq R S R', integerNormalization_eval₂_eq_zero]

中文:
定理 integerNormalization_aeval_eq_zero
  结论: [代数 R R'] [代数 S R'] [标量塔 R S R']
  证明: by
  rwa [aeval_def, IsScalarTower.algebraMap_eq R S R', integerNormalization_eval₂_eq_zero]

Depends on / 依赖: IsScalarTower, IsScalarTower.algebraMap_eq, aeval_def, algebraMap_eq
-/
theorem integerNormalization_aeval_eq_zero [Algebra R R'] [Algebra S R'] [IsScalarTower R S R']
    (p : S[X]) {x : R'} (hx : aeval x p = 0) : aeval x (integerNormalization M p) = 0 := by
  rwa [aeval_def, IsScalarTower.algebraMap_eq R S R', integerNormalization_eval₂_eq_zero]

end IntegerNormalization

end IsLocalization

namespace IsFractionRing

open IsLocalization

variable {A K C : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
variable [CommRing C]

/--
theorem `integerNormalization_eq_zero_iff` / 定理 `integerNormalization_eq_zero_iff`

English:
theorem integerNormalization_eq_zero_iff
  given: {p : K[X]}
  proof: IsLocalization.integerNormalization_eq_zero_iff le_rfl p

中文:
定理 integerNormalization_eq_zero_iff
  条件: {p : K[X]}
  证明: IsLocalization.integerNormalization_eq_zero_iff le_rfl p

Depends on / 依赖: IsLocalization, IsLocalization.integerNormalization_eq_zero_iff, integerNormalization_eq_zero_iff, le_rfl
-/
theorem integerNormalization_eq_zero_iff {p : K[X]} :
    integerNormalization (nonZeroDivisors A) p = 0 ↔ p = 0 :=
  IsLocalization.integerNormalization_eq_zero_iff le_rfl p

variable (A K C)

/--
theorem `isAlgebraic_iff` / 定理 `isAlgebraic_iff`

English:
theorem isAlgebraic_iff
  given: [Algebra A C] [Algebra K C] [IsScalarTower A K C] {x : C}
  proof: by
  constructor <;> rintro ⟨p, hp, px⟩
  · refine ⟨p.map (algebraMap A K), fun h => hp (Polynomial.ext fun i => ?_), ?_⟩
    · have : algebraMap A K (p.coeff i) = 0 :=
        _root_.trans (Polynomial.coeff_map _ _).symm (by simp [h])
      exact to_map_eq_zero_iff.mp this
    · exact (Polynomial.aeval_map_algebraMap K _ _).trans px
  · exact
      ⟨integerNormalization _ p, mt integerNormalization_eq_zero_iff.mp hp,
        integerNormalization_aeval_eq_zero _ p px⟩

中文:
定理 isAlgebraic_iff
  条件: [代数 A C] [代数 K C] [标量塔 A K C] {x : C}
  证明: by
  constructor <;> rintro ⟨p, hp, px⟩
  · refine ⟨p.map (algebraMap A K), fun h => hp (Polynomial.ext fun i => ?_), ?_⟩
    · have : algebraMap A K (p.coeff i) = 0 :=
        _root_.trans (Polynomial.coeff_map _ _).symm (by simp [h])
      exact to_map_eq_zero_iff.mp this
    · exact (Polynomial.aeval_map_algebraMap K _ _).trans px
  · exact
      ⟨integerNormalization _ p, mt integerNormalization_eq_zero_iff.mp hp,
        integerNormalization_aeval_eq_zero _ p px⟩

Depends on / 依赖: Polynomial, Polynomial.aeval_map_algebraMap, Polynomial.coeff_map, Polynomial.ext, _root_, _root_.trans, aeval_map_algebraMap, algebraMap, coeff_map, integerNormalization, integerNormalization_aeval_eq_zero, integerNormalization_eq_zero_iff, integerNormalization_eq_zero_iff.mp, p.coeff, p.map, to_map_eq_zero_iff, to_map_eq_zero_iff.mp
-/
theorem isAlgebraic_iff [Algebra A C] [Algebra K C] [IsScalarTower A K C] {x : C} :
    IsAlgebraic A x ↔ IsAlgebraic K x := by
  constructor <;> rintro ⟨p, hp, px⟩
  · refine ⟨p.map (algebraMap A K), fun h => hp (Polynomial.ext fun i => ?_), ?_⟩
    · have : algebraMap A K (p.coeff i) = 0 :=
        _root_.trans (Polynomial.coeff_map _ _).symm (by simp [h])
      exact to_map_eq_zero_iff.mp this
    · exact (Polynomial.aeval_map_algebraMap K _ _).trans px
  · exact
      ⟨integerNormalization _ p, mt integerNormalization_eq_zero_iff.mp hp,
        integerNormalization_aeval_eq_zero _ p px⟩

variable {A K C}

/--
theorem `comap_isAlgebraic_iff` / 定理 `comap_isAlgebraic_iff`

English:
theorem comap_isAlgebraic_iff
  given: [Algebra A C] [Algebra K C] [IsScalarTower A K C]
  proof: ⟨fun h => ⟨fun x => (isAlgebraic_iff A K C).mp (h.isAlgebraic x)⟩,
   fun h => ⟨fun x => (isAlgebraic_iff A K C).mpr (h.isAlgebraic x)⟩⟩

中文:
定理 comap_isAlgebraic_iff
  条件: [代数 A C] [代数 K C] [标量塔 A K C]
  证明: ⟨fun h => ⟨fun x => (isAlgebraic_iff A K C).mp (h.isAlgebraic x)⟩,
   fun h => ⟨fun x => (isAlgebraic_iff A K C).mpr (h.isAlgebraic x)⟩⟩

Depends on / 依赖: h.isAlgebraic, isAlgebraic, isAlgebraic_iff
-/
theorem comap_isAlgebraic_iff [Algebra A C] [Algebra K C] [IsScalarTower A K C] :
    Algebra.IsAlgebraic A C ↔ Algebra.IsAlgebraic K C :=
  ⟨fun h => ⟨fun x => (isAlgebraic_iff A K C).mp (h.isAlgebraic x)⟩,
   fun h => ⟨fun x => (isAlgebraic_iff A K C).mpr (h.isAlgebraic x)⟩⟩

end IsFractionRing

open IsLocalization

section IsIntegral

variable {Rₘ Sₘ : Type*} [CommRing Rₘ] [CommRing Sₘ]
variable [Algebra R Rₘ] [IsLocalization M Rₘ]
variable [Algebra S Sₘ] [IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ]
variable {M}

open Polynomial

/--
theorem `RingHom.isIntegralElem_localization_at_leadingCoeff` / 定理 `RingHom.isIntegralElem_localization_at_leadingCoeff`

English:
theorem RingHom.isIntegralElem_localization_at_leadingCoeff
  statement: {R S : Type*} [CommSemiring R]
  proof: by
  by_cases triv : (1 : Rₘ) = 0
  · exact ⟨0, ⟨_root_.trans leadingCoeff_zero triv.symm, eval₂_zero _ _⟩⟩
  have : Nontrivial Rₘ := nontrivial_of_ne 1 0 triv
  obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp (map_units Rₘ ⟨p.leadingCoeff, hM⟩)
  refine ⟨p.map (algebraMap R Rₘ) * C b, ⟨?_, ?_⟩⟩
  · refine monic_mul_C_of_leadingCoeff_mul_eq_one ?_
    rwa [leadingCoeff_map_of_leadingCoeff_ne_zero (algebraMap R Rₘ)]
    refine fun hfp => zero_ne_one
      (_root_.trans (zero_mul b).symm (hfp ▸ hb) : (0 : Rₘ) = 1)
  · refine eval₂_mul_eq_zero_of_left _ _ _ ?_
    rw [eval₂_map]; rw [IsLocalization.map_comp]; rw [← hom_eval₂ _ f (algebraMap S Sₘ) x]
    exact _root_.trans (congr_arg (algebraMap S Sₘ) hf) (map_zero _)

中文:
定理 环态射.is整数egralElem_localization_at_leadingCoeff
  结论: {R S : 类型} [交换半环 R]
  证明: by
  by_cases triv : (1 : Rₘ) = 0
  · exact ⟨0, ⟨_root_.trans leadingCoeff_zero triv.symm, eval₂_zero _ _⟩⟩
  have : Nontrivial Rₘ := nontrivial_of_ne 1 0 triv
  obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp (map_units Rₘ ⟨p.leadingCoeff, hM⟩)
  refine ⟨p.map (algebraMap R Rₘ) * C b, ⟨?_, ?_⟩⟩
  · refine monic_mul_C_of_leadingCoeff_mul_eq_one ?_
    rwa [leadingCoeff_map_of_leadingCoeff_ne_zero (algebraMap R Rₘ)]
    refine fun hfp => zero_ne_one
      (_root_.trans (zero_mul b).symm (hfp ▸ hb) : (0 : Rₘ) = 1)
  · refine eval₂_mul_eq_zero_of_left _ _ _ ?_
    rw [eval₂_map]; rw [IsLocalization.map_comp]; rw [← hom_eval₂ _ f (algebraMap S Sₘ) x]
    exact _root_.trans (congr_arg (algebraMap S Sₘ) hf) (map_zero _)

Depends on / 依赖: Nontrivial, _root_, _root_.trans, algebraMap, isUnit_iff_exists_inv, isUnit_iff_exists_inv.mp, leadingCoeff, leadingCoeff_map_of_leadingCoeff_ne_zero, leadingCoeff_zero, map_units, monic_mul_C_of_leadingCoeff_mul_eq_one, nontrivial_of_ne, p.leadingCoeff, p.map, triv.symm, zero_mul, zero_ne_one
-/
theorem RingHom.isIntegralElem_localization_at_leadingCoeff {R S : Type*} [CommSemiring R]
    [CommSemiring S] (f : R ->+* S) (x : S) (p : R[X]) (hf : p.eval₂ f x = 0) (M : Submonoid R)
    (hM : p.leadingCoeff in M) {Rₘ Sₘ : Type*} [CommRing Rₘ] [CommRing Sₘ] [Algebra R Rₘ]
    [IsLocalization M Rₘ] [Algebra S Sₘ] [IsLocalization (M.map f : Submonoid S) Sₘ] :
    (map Sₘ f M.le_comap_map : Rₘ ->+* _).IsIntegralElem (algebraMap S Sₘ x) := by
  by_cases triv : (1 : Rₘ) = 0
  · exact ⟨0, ⟨_root_.trans leadingCoeff_zero triv.symm, eval₂_zero _ _⟩⟩
  have : Nontrivial Rₘ := nontrivial_of_ne 1 0 triv
  obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp (map_units Rₘ ⟨p.leadingCoeff, hM⟩)
  refine ⟨p.map (algebraMap R Rₘ) * C b, ⟨?_, ?_⟩⟩
  · refine monic_mul_C_of_leadingCoeff_mul_eq_one ?_
    rwa [leadingCoeff_map_of_leadingCoeff_ne_zero (algebraMap R Rₘ)]
    refine fun hfp => zero_ne_one
      (_root_.trans (zero_mul b).symm (hfp ▸ hb) : (0 : Rₘ) = 1)
  · refine eval₂_mul_eq_zero_of_left _ _ _ ?_
    rw [eval₂_map]; rw [IsLocalization.map_comp]; rw [← hom_eval₂ _ f (algebraMap S Sₘ) x]
    exact _root_.trans (congr_arg (algebraMap S Sₘ) hf) (map_zero _)

/--
theorem `is_integral_localization_at_leadingCoeff` / 定理 `is_integral_localization_at_leadingCoeff`

English:
theorem is_integral_localization_at_leadingCoeff
  statement: {x : S} (p : R[X]) (hp : aeval x p = 0)
  proof: haveI : IsLocalization (Submonoid.map (algebraMap R S) M) Sₘ :=
    inferInstanceAs (IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ)
  (algebraMap R S).isIntegralElem_localization_at_leadingCoeff x p hp M hM

中文:
定理 is_integral_localization_at_leadingCoeff
  结论: {x : S} (p : R[X]) (hp : aeval x p = 0)
  证明: haveI : IsLocalization (Submonoid.map (algebraMap R S) M) Sₘ :=
    inferInstanceAs (IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ)
  (algebraMap R S).isIntegralElem_localization_at_leadingCoeff x p hp M hM

Depends on / 依赖: Algebra, Algebra.algebraMapSubmonoid, IsLocalization, Submonoid, Submonoid.map, algebraMap, algebraMapSubmonoid, isIntegralElem_localization_at_leadingCoeff
-/
theorem is_integral_localization_at_leadingCoeff {x : S} (p : R[X]) (hp : aeval x p = 0)
    (hM : p.leadingCoeff in M) :
    (map Sₘ (algebraMap R S)
            (show _ <= (Algebra.algebraMapSubmonoid S M).comap _ from M.le_comap_map) :
          Rₘ ->+* _).IsIntegralElem
      (algebraMap S Sₘ x) :=
  haveI : IsLocalization (Submonoid.map (algebraMap R S) M) Sₘ :=
    inferInstanceAs (IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ)
  (algebraMap R S).isIntegralElem_localization_at_leadingCoeff x p hp M hM

/--
theorem `isIntegral_localization` / 定理 `isIntegral_localization`

English:
theorem isIntegral_localization
  given: [Algebra.IsIntegral R S]
  proof: by
  intro x
  obtain ⟨⟨s, ⟨u, hu⟩⟩, hx⟩ := surj (Algebra.algebraMapSubmonoid S M) x
  obtain ⟨v, hv⟩ := hu
  obtain ⟨v', hv'⟩ := isUnit_iff_exists_inv'.1 (map_units Rₘ ⟨v, hv.1⟩)
  refine @IsIntegral.of_mul_unit Rₘ _ _ _ (localizationAlgebra M S) x (algebraMap S Sₘ u) v' ?_ ?_
  · replace hv' := congr_arg (@algebraMap Rₘ Sₘ _ _ (localizationAlgebra M S)) hv'
    rw [map_mul]; rw [map_one]; rw [localizationAlgebraMap_def]; rw [IsLocalization.map_eq] at hv'
    exact hv.2 ▸ hv'
  · obtain ⟨p, hp⟩ := Algebra.IsIntegral.isIntegral (R := R) s
    exact hx.symm ▸ is_integral_localization_at_leadingCoeff p hp.2 (hp.1.symm ▸ M.one_mem)

中文:
定理 is整数egral_localization
  条件: [代数.是整 R S]
  证明: by
  intro x
  obtain ⟨⟨s, ⟨u, hu⟩⟩, hx⟩ := surj (Algebra.algebraMapSubmonoid S M) x
  obtain ⟨v, hv⟩ := hu
  obtain ⟨v', hv'⟩ := isUnit_iff_exists_inv'.1 (map_units Rₘ ⟨v, hv.1⟩)
  refine @IsIntegral.of_mul_unit Rₘ _ _ _ (localizationAlgebra M S) x (algebraMap S Sₘ u) v' ?_ ?_
  · replace hv' := congr_arg (@algebraMap Rₘ Sₘ _ _ (localizationAlgebra M S)) hv'
    rw [map_mul]; rw [map_one]; rw [localizationAlgebraMap_def]; rw [IsLocalization.map_eq] at hv'
    exact hv.2 ▸ hv'
  · obtain ⟨p, hp⟩ := Algebra.IsIntegral.isIntegral (R := R) s
    exact hx.symm ▸ is_integral_localization_at_leadingCoeff p hp.2 (hp.1.symm ▸ M.one_mem)

Depends on / 依赖: Algebra, Algebra.IsIntegral, Algebra.algebraMapSubmonoid, IsIntegral, IsIntegral.of_mul_unit, IsLocalization, IsLocalization.map_eq, algebraMap, algebraMapSubmonoid, congr_arg, isUnit_iff_exists_inv, localizationAlgebra, localizationAlgebraMap_def, map_eq, map_mul, map_one, map_units, of_mul_unit, replace
-/
theorem isIntegral_localization [Algebra.IsIntegral R S] :
    (map Sₘ (algebraMap R S)
          (show _ <= (Algebra.algebraMapSubmonoid S M).comap _ from M.le_comap_map) :
        Rₘ ->+* _).IsIntegral := by
  intro x
  obtain ⟨⟨s, ⟨u, hu⟩⟩, hx⟩ := surj (Algebra.algebraMapSubmonoid S M) x
  obtain ⟨v, hv⟩ := hu
  obtain ⟨v', hv'⟩ := isUnit_iff_exists_inv'.1 (map_units Rₘ ⟨v, hv.1⟩)
  refine @IsIntegral.of_mul_unit Rₘ _ _ _ (localizationAlgebra M S) x (algebraMap S Sₘ u) v' ?_ ?_
  · replace hv' := congr_arg (@algebraMap Rₘ Sₘ _ _ (localizationAlgebra M S)) hv'
    rw [map_mul]; rw [map_one]; rw [localizationAlgebraMap_def]; rw [IsLocalization.map_eq] at hv'
    exact hv.2 ▸ hv'
  · obtain ⟨p, hp⟩ := Algebra.IsIntegral.isIntegral (R := R) s
    exact hx.symm ▸ is_integral_localization_at_leadingCoeff p hp.2 (hp.1.symm ▸ M.one_mem)

/--
theorem `isIntegral_localization'` / 定理 `isIntegral_localization'`

English:
theorem isIntegral_localization'
  statement: {R S : Type*} [CommRing R] [CommRing S] {f : R ->+* S}
  proof: let _ := f.toAlgebra
  have : Algebra.IsIntegral R S := ⟨hf⟩
  have : IsLocalization (Algebra.algebraMapSubmonoid S M)
    (Localization (Submonoid.map (f : R ->* S) M)) := Localization.isLocalization
  isIntegral_localization

中文:
定理 is整数egral_localization'
  结论: {R S : 类型} [交换环 R] [交换环 S] {f : R ->+* S}
  证明: let _ := f.toAlgebra
  have : Algebra.IsIntegral R S := ⟨hf⟩
  have : IsLocalization (Algebra.algebraMapSubmonoid S M)
    (Localization (Submonoid.map (f : R ->* S) M)) := Localization.isLocalization
  isIntegral_localization

Depends on / 依赖: Algebra, Algebra.IsIntegral, Algebra.algebraMapSubmonoid, IsIntegral, IsLocalization, Localization, Localization.isLocalization, Submonoid, Submonoid.map, algebraMapSubmonoid, f.toAlgebra, isIntegral_localization, isLocalization, toAlgebra
-/
theorem isIntegral_localization' {R S : Type*} [CommRing R] [CommRing S] {f : R ->+* S}
    (hf : f.IsIntegral) (M : Submonoid R) :
    (map (Localization (M.map (f : R ->* S))) f
          (M.le_comap_map : _ <= Submonoid.comap (f : R ->* S) _) :
        Localization M ->+* _).IsIntegral :=
  let _ := f.toAlgebra
  have : Algebra.IsIntegral R S := ⟨hf⟩
  have : IsLocalization (Algebra.algebraMapSubmonoid S M)
    (Localization (Submonoid.map (f : R ->* S) M)) := Localization.isLocalization
  isIntegral_localization

variable (M)

/--
theorem `IsLocalization.scaleRoots_commonDenom_mem_lifts` / 定理 `IsLocalization.scaleRoots_commonDenom_mem_lifts`

English:
theorem IsLocalization.scaleRoots_commonDenom_mem_lifts
  statement: (p : Rₘ[X])
  proof: by
  rw [Polynomial.lifts_iff_coeff_lifts]
  intro n
  rw [Polynomial.coeff_scaleRoots]
  by_cases h₁ : n in p.support
  on_goal 1 => by_cases h₂ : n = p.natDegree
  · rwa [h₂, Polynomial.coeff_natDegree, tsub_self, pow_zero, _root_.mul_one]
  · have : n + 1 <= p.natDegree := lt_of_le_of_ne (Polynomial.le_natDegree_of_mem_supp _ h₁) h₂
    rw [← tsub_add_cancel_of_le (le_tsub_of_add_le_left this)]; rw [pow_add]; rw [pow_one]; rw [mul_comm]; rw [_root_.mul_assoc]; rw [← map_pow]
    change _ in (algebraMap R Rₘ).range
    apply mul_mem
    · exact RingHom.mem_range_self _ _
    · rw [← Algebra.smul_def]
      exact ⟨_, IsLocalization.map_integerMultiple M p.support p.coeff ⟨n, h₁⟩⟩
  · rw [Polynomial.notMem_support_iff] at h₁
    rw [h₁]; rw [zero_mul]
    exact zero_mem (algebraMap R Rₘ).range

中文:
定理 是Localization.scaleRoots_commonDenom_mem_lifts
  结论: (p : Rₘ[X])
  证明: by
  rw [Polynomial.lifts_iff_coeff_lifts]
  intro n
  rw [Polynomial.coeff_scaleRoots]
  by_cases h₁ : n in p.support
  on_goal 1 => by_cases h₂ : n = p.natDegree
  · rwa [h₂, Polynomial.coeff_natDegree, tsub_self, pow_zero, _root_.mul_one]
  · have : n + 1 <= p.natDegree := lt_of_le_of_ne (Polynomial.le_natDegree_of_mem_supp _ h₁) h₂
    rw [← tsub_add_cancel_of_le (le_tsub_of_add_le_left this)]; rw [pow_add]; rw [pow_one]; rw [mul_comm]; rw [_root_.mul_assoc]; rw [← map_pow]
    change _ in (algebraMap R Rₘ).range
    apply mul_mem
    · exact RingHom.mem_range_self _ _
    · rw [← Algebra.smul_def]
      exact ⟨_, IsLocalization.map_integerMultiple M p.support p.coeff ⟨n, h₁⟩⟩
  · rw [Polynomial.notMem_support_iff] at h₁
    rw [h₁]; rw [zero_mul]
    exact zero_mem (algebraMap R Rₘ).range

Depends on / 依赖: GroupFilterBasis, Polynomial, Polynomial.coeff_natDegree, Polynomial.coeff_scaleRoots, Polynomial.le_natDegree_of_mem_supp, Polynomial.lifts_iff_coeff_lifts, _root_, _root_.mul_assoc, _root_.mul_one, algebraMap, coeff_natDegree, coeff_scaleRoots, isTopologicalGroup, le_natDegree_of_mem_supp, le_tsub_of_add_le_left, lifts_iff_coeff_lifts, lt_of_le_of_ne, map_pow, mul_assoc, mul_comm
-/
theorem IsLocalization.scaleRoots_commonDenom_mem_lifts (p : Rₘ[X])
    (hp : p.leadingCoeff in (algebraMap R Rₘ).range) :
    p.scaleRoots (algebraMap R Rₘ <| IsLocalization.commonDenom M p.support p.coeff) in
      Polynomial.lifts (algebraMap R Rₘ) := by
  rw [Polynomial.lifts_iff_coeff_lifts]
  intro n
  rw [Polynomial.coeff_scaleRoots]
  by_cases h₁ : n in p.support
  on_goal 1 => by_cases h₂ : n = p.natDegree
  · rwa [h₂, Polynomial.coeff_natDegree, tsub_self, pow_zero, _root_.mul_one]
  · have : n + 1 <= p.natDegree := lt_of_le_of_ne (Polynomial.le_natDegree_of_mem_supp _ h₁) h₂
    rw [← tsub_add_cancel_of_le (le_tsub_of_add_le_left this)]; rw [pow_add]; rw [pow_one]; rw [mul_comm]; rw [_root_.mul_assoc]; rw [← map_pow]
    change _ in (algebraMap R Rₘ).range
    apply mul_mem
    · exact RingHom.mem_range_self _ _
    · rw [← Algebra.smul_def]
      exact ⟨_, IsLocalization.map_integerMultiple M p.support p.coeff ⟨n, h₁⟩⟩
  · rw [Polynomial.notMem_support_iff] at h₁
    rw [h₁]; rw [zero_mul]
    exact zero_mem (algebraMap R Rₘ).range

/--
theorem `IsIntegral.exists_multiple_integral_of_isLocalization` / 定理 `IsIntegral.exists_multiple_integral_of_isLocalization`

English:
theorem IsIntegral.exists_multiple_integral_of_isLocalization
  statement: [Algebra Rₘ S] [IsScalarTower R Rₘ S]
  proof: by
  rcases subsingleton_or_nontrivial Rₘ with _ | nontriv
  · have := (algebraMap Rₘ S).codomain_trivial
    exact ⟨1, Polynomial.X, Polynomial.monic_X, Subsingleton.elim _ _⟩
  obtain ⟨p, hp₁, hp₂⟩ := hx
  -- Porting note: obtain doesn't support side goals
  have :=
    lifts_and_natDegree_eq_and_monic (IsLocalization.scaleRoots_commonDenom_mem_lifts M p ?_) ?_
  · obtain ⟨p', hp'₁, -, hp'₂⟩ := this
    refine ⟨IsLocalization.commonDenom M p.support p.coeff, p', hp'₂, ?_⟩
    rw [IsScalarTower.algebraMap_eq R Rₘ S]; rw [← Polynomial.eval₂_map]; rw [hp'₁]; rw [Submonoid.smul_def]; rw [Algebra.smul_def]; rw [IsScalarTower.algebraMap_apply R Rₘ S]
    exact Polynomial.scaleRoots_eval₂_eq_zero _ hp₂
  · rw [hp₁.leadingCoeff]
    exact one_mem _
  · rwa [Polynomial.monic_scaleRoots_iff]

中文:
定理 是整.存在_multiple_integral_of_isLocalization
  结论: [代数 Rₘ S] [标量塔 R Rₘ S]
  证明: by
  rcases subsingleton_or_nontrivial Rₘ with _ | nontriv
  · have := (algebraMap Rₘ S).codomain_trivial
    exact ⟨1, Polynomial.X, Polynomial.monic_X, Subsingleton.elim _ _⟩
  obtain ⟨p, hp₁, hp₂⟩ := hx
  -- Porting note: obtain doesn't support side goals
  have :=
    lifts_and_natDegree_eq_and_monic (IsLocalization.scaleRoots_commonDenom_mem_lifts M p ?_) ?_
  · obtain ⟨p', hp'₁, -, hp'₂⟩ := this
    refine ⟨IsLocalization.commonDenom M p.support p.coeff, p', hp'₂, ?_⟩
    rw [IsScalarTower.algebraMap_eq R Rₘ S]; rw [← Polynomial.eval₂_map]; rw [hp'₁]; rw [Submonoid.smul_def]; rw [Algebra.smul_def]; rw [IsScalarTower.algebraMap_apply R Rₘ S]
    exact Polynomial.scaleRoots_eval₂_eq_zero _ hp₂
  · rw [hp₁.leadingCoeff]
    exact one_mem _
  · rwa [Polynomial.monic_scaleRoots_iff]

Depends on / 依赖: Polynomial, Polynomial.X, Polynomial.monic_X, Subsingleton, Subsingleton.elim, algebraMap, codomain_trivial, monic_X, nontriv, subsingleton_or_nontrivial
-/
theorem IsIntegral.exists_multiple_integral_of_isLocalization [Algebra Rₘ S] [IsScalarTower R Rₘ S]
    (x : S) (hx : IsIntegral Rₘ x) : exists m : M, IsIntegral R (m • x) := by
  rcases subsingleton_or_nontrivial Rₘ with _ | nontriv
  · have := (algebraMap Rₘ S).codomain_trivial
    exact ⟨1, Polynomial.X, Polynomial.monic_X, Subsingleton.elim _ _⟩
  obtain ⟨p, hp₁, hp₂⟩ := hx
  -- Porting note: obtain doesn't support side goals
  have :=
    lifts_and_natDegree_eq_and_monic (IsLocalization.scaleRoots_commonDenom_mem_lifts M p ?_) ?_
  · obtain ⟨p', hp'₁, -, hp'₂⟩ := this
    refine ⟨IsLocalization.commonDenom M p.support p.coeff, p', hp'₂, ?_⟩
    rw [IsScalarTower.algebraMap_eq R Rₘ S]; rw [← Polynomial.eval₂_map]; rw [hp'₁]; rw [Submonoid.smul_def]; rw [Algebra.smul_def]; rw [IsScalarTower.algebraMap_apply R Rₘ S]
    exact Polynomial.scaleRoots_eval₂_eq_zero _ hp₂
  · rw [hp₁.leadingCoeff]
    exact one_mem _
  · rwa [Polynomial.monic_scaleRoots_iff]

/--
lemma `IsLocalization.exists_isIntegral_smul_of_isIntegral_map` / 引理 `IsLocalization.exists_isIntegral_smul_of_isIntegral_map`

English:
lemma IsLocalization.exists_isIntegral_smul_of_isIntegral_map
  proof: by
  obtain ⟨p, hpm, hp⟩ := hx
  simp only [IsScalarTower.algebraMap_eq R S Sₘ, ← hom_eval₂,
    IsLocalization.map_eq_zero_iff (Algebra.algebraMapSubmonoid S M), Algebra.algebraMapSubmonoid,
    Subtype.exists, Submonoid.mem_map, exists_prop, exists_exists_and_eq_and] at hp
  obtain ⟨m, hm, e⟩ := hp
  exact ⟨m, hm, by simpa [Algebra.smul_def, leadingCoeff_mul_monic hpm] using!
    RingHom.isIntegralElem_leadingCoeff_mul (algebraMap R S) (C m * p) x (by simpa)⟩

中文:
引理 是Localization.存在_is整数egral_smul_of_is整数egral_map
  证明: by
  obtain ⟨p, hpm, hp⟩ := hx
  simp only [IsScalarTower.algebraMap_eq R S Sₘ, ← hom_eval₂,
    IsLocalization.map_eq_zero_iff (Algebra.algebraMapSubmonoid S M), Algebra.algebraMapSubmonoid,
    Subtype.exists, Submonoid.mem_map, exists_prop, exists_exists_and_eq_and] at hp
  obtain ⟨m, hm, e⟩ := hp
  exact ⟨m, hm, by simpa [Algebra.smul_def, leadingCoeff_mul_monic hpm] using!
    RingHom.isIntegralElem_leadingCoeff_mul (algebraMap R S) (C m * p) x (by simpa)⟩

Depends on / 依赖: Algebra, Algebra.algebraMapSubmonoid, Algebra.smul_def, IsLocalization, IsLocalization.map_eq_zero_iff, IsScalarTower, IsScalarTower.algebraMap_eq, RingHom, RingHom.isIntegralElem_leadingCoeff_mul, Submonoid, Submonoid.mem_map, Subtype, Subtype.exists, algebraMap, algebraMapSubmonoid, algebraMap_eq, exists_exists_and_eq_and, exists_prop, isIntegralElem_leadingCoeff_mul, leadingCoeff_mul_monic
-/
lemma IsLocalization.exists_isIntegral_smul_of_isIntegral_map
    {R S Sₘ : Type*} [CommRing R] [CommRing S] [CommRing Sₘ] [Algebra R S] [Algebra S Sₘ]
    [Algebra R Sₘ] [IsScalarTower R S Sₘ] (M : Submonoid R)
    [IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ] {x : S}
    (hx : IsIntegral R (algebraMap S Sₘ x)) : exists m in M, IsIntegral R (m • x) := by
  obtain ⟨p, hpm, hp⟩ := hx
  simp only [IsScalarTower.algebraMap_eq R S Sₘ, ← hom_eval₂,
    IsLocalization.map_eq_zero_iff (Algebra.algebraMapSubmonoid S M), Algebra.algebraMapSubmonoid,
    Subtype.exists, Submonoid.mem_map, exists_prop, exists_exists_and_eq_and] at hp
  obtain ⟨m, hm, e⟩ := hp
  exact ⟨m, hm, by simpa [Algebra.smul_def, leadingCoeff_mul_monic hpm] using!
    RingHom.isIntegralElem_leadingCoeff_mul (algebraMap R S) (C m * p) x (by simpa)⟩

/--
lemma `IsLocalization.Away.exists_isIntegral_mul_of_isIntegral_algebraMap` / 引理 `IsLocalization.Away.exists_isIntegral_mul_of_isIntegral_algebraMap`

English:
lemma IsLocalization.Away.exists_isIntegral_mul_of_isIntegral_algebraMap
  proof: by
  nontriviality S
  obtain ⟨p, hpm, hp⟩ := hx
  simp only [IsScalarTower.algebraMap_eq R S Sₘ, ← hom_eval₂,
    IsLocalization.map_eq_zero_iff (.powers r), Subtype.exists, Submonoid.mem_powers_iff,
    exists_prop, exists_exists_eq_and] at hp
  obtain ⟨m, hm⟩ := hp
  have := isIntegral_trans (R := R) _ (isIntegral_leadingCoeff_smul (R := integralClosure R S)
    (C ⟨r, hr⟩ ^ m * p.map (algebraMap _ _)) x (by simpa [← aeval_def] using hm))
  rw [← map_pow]; rw [(hpm.map _).leadingCoeff_C_mul] at this
  exact ⟨m, this⟩

中文:
引理 是Localization.Away.存在_is整数egral_mul_of_is整数egral_algebraMap
  证明: by
  nontriviality S
  obtain ⟨p, hpm, hp⟩ := hx
  simp only [IsScalarTower.algebraMap_eq R S Sₘ, ← hom_eval₂,
    IsLocalization.map_eq_zero_iff (.powers r), Subtype.exists, Submonoid.mem_powers_iff,
    exists_prop, exists_exists_eq_and] at hp
  obtain ⟨m, hm⟩ := hp
  have := isIntegral_trans (R := R) _ (isIntegral_leadingCoeff_smul (R := integralClosure R S)
    (C ⟨r, hr⟩ ^ m * p.map (algebraMap _ _)) x (by simpa [← aeval_def] using hm))
  rw [← map_pow]; rw [(hpm.map _).leadingCoeff_C_mul] at this
  exact ⟨m, this⟩

Depends on / 依赖: IsLocalization, IsLocalization.map_eq_zero_iff, IsScalarTower, IsScalarTower.algebraMap_eq, Submonoid, Submonoid.mem_powers_iff, Subtype, Subtype.exists, aeval_def, algebraMap, algebraMap_eq, exists_exists_eq_and, exists_prop, hpm.map, integralClosure, isIntegral_leadingCoeff_smul, isIntegral_trans, leadingCoeff_C_mul, map_eq_zero_iff, map_pow
-/
lemma IsLocalization.Away.exists_isIntegral_mul_of_isIntegral_algebraMap
    {R S Sₘ : Type*} [CommRing R] [CommRing S] [CommRing Sₘ] [Algebra R S] [Algebra S Sₘ]
    [Algebra R Sₘ] [IsScalarTower R S Sₘ] {r : S} (hr : IsIntegral R r)
    [IsLocalization.Away r Sₘ] {x : S}
    (hx : IsIntegral R (algebraMap S Sₘ x)) : exists n, IsIntegral R (r ^ n * x) := by
  nontriviality S
  obtain ⟨p, hpm, hp⟩ := hx
  simp only [IsScalarTower.algebraMap_eq R S Sₘ, ← hom_eval₂,
    IsLocalization.map_eq_zero_iff (.powers r), Subtype.exists, Submonoid.mem_powers_iff,
    exists_prop, exists_exists_eq_and] at hp
  obtain ⟨m, hm⟩ := hp
  have := isIntegral_trans (R := R) _ (isIntegral_leadingCoeff_smul (R := integralClosure R S)
    (C ⟨r, hr⟩ ^ m * p.map (algebraMap _ _)) x (by simpa [← aeval_def] using hm))
  rw [← map_pow]; rw [(hpm.map _).leadingCoeff_C_mul] at this
  exact ⟨m, this⟩

/--
lemma `IsLocalization.Away.exists_isIntegral_mul_of_isIntegral_mk'` / 引理 `IsLocalization.Away.exists_isIntegral_mul_of_isIntegral_mk'`

English:
lemma IsLocalization.Away.exists_isIntegral_mul_of_isIntegral_mk'
  proof: by
  refine IsLocalization.Away.exists_isIntegral_mul_of_isIntegral_algebraMap (Sₘ := Sₘ) hr ?_
  obtain ⟨_, ⟨n, rfl⟩⟩ := a
  convert! (hr.pow n).algebraMap.mul hx
  exact (mk'_spec'_mk ..).symm

中文:
引理 是Localization.Away.存在_is整数egral_mul_of_is整数egral_mk'
  证明: by
  refine IsLocalization.Away.exists_isIntegral_mul_of_isIntegral_algebraMap (Sₘ := Sₘ) hr ?_
  obtain ⟨_, ⟨n, rfl⟩⟩ := a
  convert! (hr.pow n).algebraMap.mul hx
  exact (mk'_spec'_mk ..).symm

Depends on / 依赖: IsLocalization, IsLocalization.Away.exists_isIntegral_mul_of_isIntegral_algebraMap, _spec, algebraMap, algebraMap.mul, convert, exists_isIntegral_mul_of_isIntegral_algebraMap, hr.pow
-/
lemma IsLocalization.Away.exists_isIntegral_mul_of_isIntegral_mk'
    {R S Sₘ : Type*} [CommRing R] [CommRing S] [CommRing Sₘ] [Algebra R S] [Algebra S Sₘ]
    [Algebra R Sₘ] [IsScalarTower R S Sₘ] {r : S} (hr : IsIntegral R r)
    [IsLocalization.Away r Sₘ] {x : S} {a : Submonoid.powers r}
    (hx : IsIntegral R (IsLocalization.mk' Sₘ x a)) : exists n, IsIntegral R (r ^ n * x) := by
  refine IsLocalization.Away.exists_isIntegral_mul_of_isIntegral_algebraMap (Sₘ := Sₘ) hr ?_
  obtain ⟨_, ⟨n, rfl⟩⟩ := a
  convert! (hr.pow n).algebraMap.mul hx
  exact (mk'_spec'_mk ..).symm

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `isIntegral_of_isIntegral_adjoin_of_mul_eq_one` / 引理 `isIntegral_of_isIntegral_adjoin_of_mul_eq_one`

English:
lemma isIntegral_of_isIntegral_adjoin_of_mul_eq_one
  proof: by
  nontriviality S
  let φ := aeval (R := R) s
  obtain ⟨q, hqm, hqt⟩ : φ.IsIntegralElem t := by
    obtain ⟨p, hpm, hpt⟩ := ht
    have : p.map (algebraMap _ S) in lifts φ.toRingHom := (lifts_iff_coeff_lifts _).mpr
      (by simp [← AlgHom.mem_range, φ, ← Algebra.adjoin_singleton_eq_range_aeval])
    obtain ⟨q, hqp, hqd, hqm⟩ := lifts_and_degree_eq_and_monic this (hpm.map _)
    exact ⟨q, hqm, by rw [← eval_map, hqp, eval_map, hpt]⟩
  let N := q.support.sup (q.coeff · |>.natDegree)
  have hN (i : _) : (q.coeff i).natDegree <= N := by
    by_cases hi : i in q.support
    · exact Finset.le_sup (f := (q.coeff · |>.natDegree)) hi
    · simp_all
  let q' := q.sum fun i r => X ^ i * r.reflect N
  have (i : _) : aeval t (reflect N (q.coeff i)) = t ^ N * (aeval s (q.coeff i)) := by
    let : Invertible t := ⟨s, hst, (mul_comm _ _).trans hst⟩
    rw [aeval_def]; rw [← eval₂_reflect_mul_pow _ _ N _ ((natDegree_reflect_le ..).trans (by simp [hN]))]
    simp +instances [mul_comm, this, aeval_def]
  refine ⟨q', ?_, ?_⟩
  · refine monic_of_natDegree_le_of_coeff_eq_one (q.natDegree + N) ?_ ?_
    · refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
      grw [natDegree_mul_le, natDegree_pow_le, natDegree_X_le, natDegree_reflect_le]
      simp [max_eq_left (hN _), le_natDegree_of_mem_supp _ hi]
    · simp only [sum, finsetSum_coeff, coeff_X_pow_mul', coeff_reflect, q']
      rw [Finset.sum_eq_single q.natDegree]
      · simp [hqm.leadingCoeff]
      · intro i hi₁ hi₂
        have : N + i < q.natDegree + N :=
          add_comm N i ▸ add_lt_add_left ((le_natDegree_of_mem_supp _ hi₁).lt_of_ne hi₂) _
        simpa [(le_natDegree_of_mem_supp _ hi₁).trans, revAt, this.not_ge] using
          coeff_eq_zero_of_natDegree_lt (by grind)
      · simp +contextual
  · trans t ^ N * q.sum (t ^ · * φ.toRingHom ·)
    · simp [φ, q', Polynomial.sum, ← aeval_def, this, mul_left_comm _ (t ^ N), ← Finset.mul_sum]
    · simp_rw [mul_comm (t ^ _), ← eval₂_eq_sum, hqt, zero_mul]

中文:
引理 is整数egral_of_is整数egral_adjoin_of_mul_eq_one
  证明: by
  nontriviality S
  let φ := aeval (R := R) s
  obtain ⟨q, hqm, hqt⟩ : φ.IsIntegralElem t := by
    obtain ⟨p, hpm, hpt⟩ := ht
    have : p.map (algebraMap _ S) in lifts φ.toRingHom := (lifts_iff_coeff_lifts _).mpr
      (by simp [← AlgHom.mem_range, φ, ← Algebra.adjoin_singleton_eq_range_aeval])
    obtain ⟨q, hqp, hqd, hqm⟩ := lifts_and_degree_eq_and_monic this (hpm.map _)
    exact ⟨q, hqm, by rw [← eval_map, hqp, eval_map, hpt]⟩
  let N := q.support.sup (q.coeff · |>.natDegree)
  have hN (i : _) : (q.coeff i).natDegree <= N := by
    by_cases hi : i in q.support
    · exact Finset.le_sup (f := (q.coeff · |>.natDegree)) hi
    · simp_all
  let q' := q.sum fun i r => X ^ i * r.reflect N
  have (i : _) : aeval t (reflect N (q.coeff i)) = t ^ N * (aeval s (q.coeff i)) := by
    let : Invertible t := ⟨s, hst, (mul_comm _ _).trans hst⟩
    rw [aeval_def]; rw [← eval₂_reflect_mul_pow _ _ N _ ((natDegree_reflect_le ..).trans (by simp [hN]))]
    simp +instances [mul_comm, this, aeval_def]
  refine ⟨q', ?_, ?_⟩
  · refine monic_of_natDegree_le_of_coeff_eq_one (q.natDegree + N) ?_ ?_
    · refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
      grw [natDegree_mul_le, natDegree_pow_le, natDegree_X_le, natDegree_reflect_le]
      simp [max_eq_left (hN _), le_natDegree_of_mem_supp _ hi]
    · simp only [sum, finsetSum_coeff, coeff_X_pow_mul', coeff_reflect, q']
      rw [Finset.sum_eq_single q.natDegree]
      · simp [hqm.leadingCoeff]
      · intro i hi₁ hi₂
        have : N + i < q.natDegree + N :=
          add_comm N i ▸ add_lt_add_left ((le_natDegree_of_mem_supp _ hi₁).lt_of_ne hi₂) _
        simpa [(le_natDegree_of_mem_supp _ hi₁).trans, revAt, this.not_ge] using
          coeff_eq_zero_of_natDegree_lt (by grind)
      · simp +contextual
  · trans t ^ N * q.sum (t ^ · * φ.toRingHom ·)
    · simp [φ, q', Polynomial.sum, ← aeval_def, this, mul_left_comm _ (t ^ N), ← Finset.mul_sum]
    · simp_rw [mul_comm (t ^ _), ← eval₂_eq_sum, hqt, zero_mul]

Depends on / 依赖: AlgHom, AlgHom.mem_range, Algebra, Algebra.adjoin_singleton_eq_range_aeval, IsIntegralElem, adjoin_singleton_eq_range_aeval, algebraMap, eval_map, hpm.map, lifts_and_degree_eq_and_monic, lifts_iff_coeff_lifts, mem_range, natDegree, nontriviality, p.map, q.coeff, q.support.sup, support, toRingHom
-/
lemma isIntegral_of_isIntegral_adjoin_of_mul_eq_one
    (t s : S) (hst : s * t = 1) (ht : IsIntegral (Algebra.adjoin R {s}) t) :
    IsIntegral R t := by
  nontriviality S
  let φ := aeval (R := R) s
  obtain ⟨q, hqm, hqt⟩ : φ.IsIntegralElem t := by
    obtain ⟨p, hpm, hpt⟩ := ht
    have : p.map (algebraMap _ S) in lifts φ.toRingHom := (lifts_iff_coeff_lifts _).mpr
      (by simp [← AlgHom.mem_range, φ, ← Algebra.adjoin_singleton_eq_range_aeval])
    obtain ⟨q, hqp, hqd, hqm⟩ := lifts_and_degree_eq_and_monic this (hpm.map _)
    exact ⟨q, hqm, by rw [← eval_map, hqp, eval_map, hpt]⟩
  let N := q.support.sup (q.coeff · |>.natDegree)
  have hN (i : _) : (q.coeff i).natDegree <= N := by
    by_cases hi : i in q.support
    · exact Finset.le_sup (f := (q.coeff · |>.natDegree)) hi
    · simp_all
  let q' := q.sum fun i r => X ^ i * r.reflect N
  have (i : _) : aeval t (reflect N (q.coeff i)) = t ^ N * (aeval s (q.coeff i)) := by
    let : Invertible t := ⟨s, hst, (mul_comm _ _).trans hst⟩
    rw [aeval_def]; rw [← eval₂_reflect_mul_pow _ _ N _ ((natDegree_reflect_le ..).trans (by simp [hN]))]
    simp +instances [mul_comm, this, aeval_def]
  refine ⟨q', ?_, ?_⟩
  · refine monic_of_natDegree_le_of_coeff_eq_one (q.natDegree + N) ?_ ?_
    · refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
      grw [natDegree_mul_le, natDegree_pow_le, natDegree_X_le, natDegree_reflect_le]
      simp [max_eq_left (hN _), le_natDegree_of_mem_supp _ hi]
    · simp only [sum, finsetSum_coeff, coeff_X_pow_mul', coeff_reflect, q']
      rw [Finset.sum_eq_single q.natDegree]
      · simp [hqm.leadingCoeff]
      · intro i hi₁ hi₂
        have : N + i < q.natDegree + N :=
          add_comm N i ▸ add_lt_add_left ((le_natDegree_of_mem_supp _ hi₁).lt_of_ne hi₂) _
        simpa [(le_natDegree_of_mem_supp _ hi₁).trans, revAt, this.not_ge] using
          coeff_eq_zero_of_natDegree_lt (by grind)
      · simp +contextual
  · trans t ^ N * q.sum (t ^ · * φ.toRingHom ·)
    · simp [φ, q', Polynomial.sum, ← aeval_def, this, mul_left_comm _ (t ^ N), ← Finset.mul_sum]
    · simp_rw [mul_comm (t ^ _), ← eval₂_eq_sum, hqt, zero_mul]

/--
lemma `IsLocalization.Away.isIntegral_of_isIntegral_map` / 引理 `IsLocalization.Away.isIntegral_of_isIntegral_map`

English:
lemma IsLocalization.Away.isIntegral_of_isIntegral_map
  proof: by
  obtain ⟨p, hpm, hp⟩ := hx
  simp only [IsScalarTower.algebraMap_eq R S Sₘ, IsLocalization.map_eq_zero_iff (.powers x),
    Subtype.exists, Submonoid.mem_powers_iff, ← hom_eval₂, exists_prop, exists_exists_eq_and] at hp
  obtain ⟨n, hn⟩ := hp
  exact ⟨X ^ n * p, (monic_X_pow n).mul hpm, by simpa⟩

中文:
引理 是Localization.Away.is整数egral_of_is整数egral_map
  证明: by
  obtain ⟨p, hpm, hp⟩ := hx
  simp only [IsScalarTower.algebraMap_eq R S Sₘ, IsLocalization.map_eq_zero_iff (.powers x),
    Subtype.exists, Submonoid.mem_powers_iff, ← hom_eval₂, exists_prop, exists_exists_eq_and] at hp
  obtain ⟨n, hn⟩ := hp
  exact ⟨X ^ n * p, (monic_X_pow n).mul hpm, by simpa⟩

Depends on / 依赖: IsLocalization, IsLocalization.map_eq_zero_iff, IsScalarTower, IsScalarTower.algebraMap_eq, Submonoid, Submonoid.mem_powers_iff, Subtype, Subtype.exists, algebraMap_eq, exists_exists_eq_and, exists_prop, map_eq_zero_iff, mem_powers_iff, monic_X_pow, powers
-/
lemma IsLocalization.Away.isIntegral_of_isIntegral_map
    {R S Sₘ : Type*} [CommRing R] [CommRing S] [CommRing Sₘ] [Algebra R S] [Algebra S Sₘ]
    [Algebra R Sₘ] [IsScalarTower R S Sₘ] (x : S) [IsLocalization.Away x Sₘ]
    (hx : IsIntegral R (algebraMap S Sₘ x)) : IsIntegral R x := by
  obtain ⟨p, hpm, hp⟩ := hx
  simp only [IsScalarTower.algebraMap_eq R S Sₘ, IsLocalization.map_eq_zero_iff (.powers x),
    Subtype.exists, Submonoid.mem_powers_iff, ← hom_eval₂, exists_prop, exists_exists_eq_and] at hp
  obtain ⟨n, hn⟩ := hp
  exact ⟨X ^ n * p, (monic_X_pow n).mul hpm, by simpa⟩

end IsIntegral

variable {A K : Type*} [CommRing A]

namespace IsIntegralClosure

variable (A)
variable {L : Type*} [Field K] [Field L] [Algebra A K] [Algebra A L] [IsFractionRing A K]
variable (C : Type*) [CommRing C] [IsDomain C] [Algebra C L] [IsIntegralClosure C A L]
variable [Algebra A C] [IsScalarTower A C L]

open Algebra

/--
theorem `isFractionRing_of_algebraic` / 定理 `isFractionRing_of_algebraic`

English:
theorem isFractionRing_of_algebraic
  statement: [Algebra.IsAlgebraic A L]
  proof: { map_units := fun ⟨y, hy⟩ =>
      IsUnit.mk0 _
        (show algebraMap C L y != 0 from fun h =>
          mem_nonZeroDivisors_iff_ne_zero.mp hy
            ((injective_iff_map_eq_zero (algebraMap C L)).mp (algebraMap_injective C A L) _ h))
    surj := fun z =>
      let ⟨x, hx, int⟩ := (Algebra.IsAlgebraic.isAlgebraic z).exists_integral_multiple
      ⟨⟨mk' C _ int, algebraMap _ _ x, mem_nonZeroDivisors_of_ne_zero fun h =>
        hx (inj _ <| by rw [IsScalarTower.algebraMap_apply A C L, h, map_zero])⟩, by
        rw [algebraMap_mk']; rw [← IsScalarTower.algebraMap_apply A C L]; rw [Algebra.smul_def]; rw [mul_comm]⟩
    exists_of_eq := fun {x y} h => ⟨1, by simpa using algebraMap_injective C A L h⟩ }

中文:
定理 isFractionRing_of_algebraic
  结论: [代数.是代数 A L]
  证明: { map_units := fun ⟨y, hy⟩ =>
      IsUnit.mk0 _
        (show algebraMap C L y != 0 from fun h =>
          mem_nonZeroDivisors_iff_ne_zero.mp hy
            ((injective_iff_map_eq_zero (algebraMap C L)).mp (algebraMap_injective C A L) _ h))
    surj := fun z =>
      let ⟨x, hx, int⟩ := (Algebra.IsAlgebraic.isAlgebraic z).exists_integral_multiple
      ⟨⟨mk' C _ int, algebraMap _ _ x, mem_nonZeroDivisors_of_ne_zero fun h =>
        hx (inj _ <| by rw [IsScalarTower.algebraMap_apply A C L, h, map_zero])⟩, by
        rw [algebraMap_mk']; rw [← IsScalarTower.algebraMap_apply A C L]; rw [Algebra.smul_def]; rw [mul_comm]⟩
    exists_of_eq := fun {x y} h => ⟨1, by simpa using algebraMap_injective C A L h⟩ }

Depends on / 依赖: Algebra, Algebra.IsAlgebraic.isAlgebraic, IsAlgebraic, IsScalarTower, IsScalarTower.alge, IsScalarTower.algebraMap_apply, IsUnit, IsUnit.mk0, algebraMap, algebraMap_apply, algebraMap_injective, algebraMap_mk, exists_integral_multiple, injective_iff_map_eq_zero, isAlgebraic, map_units, map_zero, mem_nonZeroDivisors_iff_ne_zero, mem_nonZeroDivisors_iff_ne_zero.mp, mem_nonZeroDivisors_of_ne_zero
-/
theorem isFractionRing_of_algebraic [Algebra.IsAlgebraic A L]
    (inj : forall x, algebraMap A L x = 0 -> x = 0) : IsFractionRing C L :=
  { map_units := fun ⟨y, hy⟩ =>
      IsUnit.mk0 _
        (show algebraMap C L y != 0 from fun h =>
          mem_nonZeroDivisors_iff_ne_zero.mp hy
            ((injective_iff_map_eq_zero (algebraMap C L)).mp (algebraMap_injective C A L) _ h))
    surj := fun z =>
      let ⟨x, hx, int⟩ := (Algebra.IsAlgebraic.isAlgebraic z).exists_integral_multiple
      ⟨⟨mk' C _ int, algebraMap _ _ x, mem_nonZeroDivisors_of_ne_zero fun h =>
        hx (inj _ <| by rw [IsScalarTower.algebraMap_apply A C L, h, map_zero])⟩, by
        rw [algebraMap_mk']; rw [← IsScalarTower.algebraMap_apply A C L]; rw [Algebra.smul_def]; rw [mul_comm]⟩
    exists_of_eq := fun {x y} h => ⟨1, by simpa using algebraMap_injective C A L h⟩ }

variable (K L)

/--
theorem `isFractionRing_of_finite_extension` / 定理 `isFractionRing_of_finite_extension`

English:
theorem isFractionRing_of_finite_extension
  statement: [IsDomain A] [Algebra K L] [IsScalarTower A K L]
  proof: have : Algebra.IsAlgebraic A L := IsFractionRing.comap_isAlgebraic_iff.mpr
    (inferInstance : Algebra.IsAlgebraic K L)
  isFractionRing_of_algebraic A C
    fun _ hx =>
    IsFractionRing.to_map_eq_zero_iff.mp
      ((map_eq_zero <| algebraMap K L).mp <| (IsScalarTower.algebraMap_apply _ _ _ _).symm.trans hx)

中文:
定理 isFractionRing_of_finite_extension
  结论: [是整环 A] [代数 K L] [标量塔 A K L]
  证明: have : Algebra.IsAlgebraic A L := IsFractionRing.comap_isAlgebraic_iff.mpr
    (inferInstance : Algebra.IsAlgebraic K L)
  isFractionRing_of_algebraic A C
    fun _ hx =>
    IsFractionRing.to_map_eq_zero_iff.mp
      ((map_eq_zero <| algebraMap K L).mp <| (IsScalarTower.algebraMap_apply _ _ _ _).symm.trans hx)

Depends on / 依赖: Algebra, Algebra.IsAlgebraic, IsAlgebraic, IsFractionRing, IsFractionRing.comap_isAlgebraic_iff.mpr, IsFractionRing.to_map_eq_zero_iff.mp, IsScalarTower, IsScalarTower.algebraMap_apply, RingFilterBasis, algebraMap, algebraMap_apply, comap_isAlgebraic_iff, isFractionRing_of_algebraic, isTopologicalRing, map_eq_zero, symm.trans, to_map_eq_zero_iff
-/
theorem isFractionRing_of_finite_extension [IsDomain A] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L] : IsFractionRing C L :=
  have : Algebra.IsAlgebraic A L := IsFractionRing.comap_isAlgebraic_iff.mpr
    (inferInstance : Algebra.IsAlgebraic K L)
  isFractionRing_of_algebraic A C
    fun _ hx =>
    IsFractionRing.to_map_eq_zero_iff.mp
      ((map_eq_zero <| algebraMap K L).mp <| (IsScalarTower.algebraMap_apply _ _ _ _).symm.trans hx)

end IsIntegralClosure

namespace integralClosure

variable {L : Type*} [Field K] [Field L] [Algebra A K] [IsFractionRing A K]

open Algebra

/--
theorem `isFractionRing_of_algebraic` / 定理 `isFractionRing_of_algebraic`

English:
theorem isFractionRing_of_algebraic
  statement: [Algebra A L] [Algebra.IsAlgebraic A L]
  proof: IsIntegralClosure.isFractionRing_of_algebraic A (integralClosure A L) inj

中文:
定理 isFractionRing_of_algebraic
  结论: [代数 A L] [代数.是代数 A L]
  证明: IsIntegralClosure.isFractionRing_of_algebraic A (integralClosure A L) inj

Depends on / 依赖: IsIntegralClosure, IsIntegralClosure.isFractionRing_of_algebraic, integralClosure, isFractionRing_of_algebraic
-/
theorem isFractionRing_of_algebraic [Algebra A L] [Algebra.IsAlgebraic A L]
    (inj : forall x, algebraMap A L x = 0 -> x = 0) : IsFractionRing (integralClosure A L) L :=
  IsIntegralClosure.isFractionRing_of_algebraic A (integralClosure A L) inj

variable (K L)

/--
theorem `isFractionRing_of_finite_extension` / 定理 `isFractionRing_of_finite_extension`

English:
theorem isFractionRing_of_finite_extension
  statement: [IsDomain A] [Algebra A L] [Algebra K L]
  proof: IsIntegralClosure.isFractionRing_of_finite_extension A K L (integralClosure A L)

中文:
定理 isFractionRing_of_finite_extension
  结论: [是整环 A] [代数 A L] [代数 K L]
  证明: IsIntegralClosure.isFractionRing_of_finite_extension A K L (integralClosure A L)

Depends on / 依赖: IsIntegralClosure, IsIntegralClosure.isFractionRing_of_finite_extension, integralClosure, isFractionRing_of_finite_extension
-/
theorem isFractionRing_of_finite_extension [IsDomain A] [Algebra A L] [Algebra K L]
    [IsScalarTower A K L] [FiniteDimensional K L] : IsFractionRing (integralClosure A L) L :=
  IsIntegralClosure.isFractionRing_of_finite_extension A K L (integralClosure A L)

end integralClosure

section

variable {Rf Sf : Type*} [CommRing Rf] [CommRing Sf] [Algebra R Rf] [Algebra S Sf]
    [Algebra Rf Sf] [Algebra R Sf] [IsScalarTower R S Sf] [IsScalarTower R Rf Sf]

-- We take in an arbitrary `Algebra (integralClosure R S) (integralClosure Rf Sf)` instance
-- so that it applies more easily.
/--
lemma `IsLocalization.integralClosure` / 引理 `IsLocalization.integralClosure`

English:
lemma IsLocalization.integralClosure
  proof: by
  refine ⟨⟨?_, ?_, ?_⟩⟩
  · rintro ⟨_, f, hf, rfl⟩
    convert!
      (IsLocalization.map_units (S := Rf) ⟨f, hf⟩).map (algebraMap Rf (integralClosure Rf Sf))
    simp [← IsScalarTower.algebraMap_apply]
  · rintro ⟨s, hs⟩
    obtain ⟨⟨x, _, m₁, hm₁, rfl⟩, e⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid S M) s
    simp only [← IsScalarTower.algebraMap_apply] at e
    obtain ⟨⟨m₂, hm₂⟩, hm₂s⟩ := IsIntegral.exists_multiple_integral_of_isLocalization M _ hs
    simp only [Submonoid.smul_def, Algebra.smul_def] at hm₂s
    obtain ⟨m₃, hm₃, hm₃s⟩ := IsLocalization.exists_isIntegral_smul_of_isIntegral_map (Sₘ := Sf)
M (x := m₂ • x) by
        simp only [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, ← e, ← mul_assoc]
        exact hm₂s.mul (.algebraMap (Algebra.IsIntegral.isIntegral _))
    refine ⟨⟨⟨_, hm₃s⟩, _, _, mul_mem hm₁ (mul_mem hm₂ hm₃), rfl⟩, ?_⟩
    · apply (FaithfulSMul.algebraMap_injective (integralClosure Rf Sf) Sf)
      simp [← IsScalarTower.algebraMap_apply, e, ← mul_assoc, Algebra.smul_def]
      ring
  · rintro ⟨a, ha⟩ ⟨b, hb⟩ e
    have := congr(algebraMap _ Sf $e)
    have : algebraMap S Sf a = algebraMap S Sf b := by
      simpa only [← IsScalarTower.algebraMap_apply] using! this
    obtain ⟨⟨_, m, hm, rfl⟩, h⟩ :=
      (IsLocalization.eq_iff_exists (Algebra.algebraMapSubmonoid S M) _).mp this
    refine ⟨⟨_, m, hm, rfl⟩, FaithfulSMul.algebraMap_injective (integralClosure R S) S ?_⟩
    simpa only [← IsScalarTower.algebraMap_apply]

中文:
引理 是Localization.integralClosure
  证明: by
  refine ⟨⟨?_, ?_, ?_⟩⟩
  · rintro ⟨_, f, hf, rfl⟩
    convert!
      (IsLocalization.map_units (S := Rf) ⟨f, hf⟩).map (algebraMap Rf (integralClosure Rf Sf))
    simp [← IsScalarTower.algebraMap_apply]
  · rintro ⟨s, hs⟩
    obtain ⟨⟨x, _, m₁, hm₁, rfl⟩, e⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid S M) s
    simp only [← IsScalarTower.algebraMap_apply] at e
    obtain ⟨⟨m₂, hm₂⟩, hm₂s⟩ := IsIntegral.exists_multiple_integral_of_isLocalization M _ hs
    simp only [Submonoid.smul_def, Algebra.smul_def] at hm₂s
    obtain ⟨m₃, hm₃, hm₃s⟩ := IsLocalization.exists_isIntegral_smul_of_isIntegral_map (Sₘ := Sf)
M (x := m₂ • x) by
        simp only [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, ← e, ← mul_assoc]
        exact hm₂s.mul (.algebraMap (Algebra.IsIntegral.isIntegral _))
    refine ⟨⟨⟨_, hm₃s⟩, _, _, mul_mem hm₁ (mul_mem hm₂ hm₃), rfl⟩, ?_⟩
    · apply (FaithfulSMul.algebraMap_injective (integralClosure Rf Sf) Sf)
      simp [← IsScalarTower.algebraMap_apply, e, ← mul_assoc, Algebra.smul_def]
      ring
  · rintro ⟨a, ha⟩ ⟨b, hb⟩ e
    have := congr(algebraMap _ Sf $e)
    have : algebraMap S Sf a = algebraMap S Sf b := by
      simpa only [← IsScalarTower.algebraMap_apply] using! this
    obtain ⟨⟨_, m, hm, rfl⟩, h⟩ :=
      (IsLocalization.eq_iff_exists (Algebra.algebraMapSubmonoid S M) _).mp this
    refine ⟨⟨_, m, hm, rfl⟩, FaithfulSMul.algebraMap_injective (integralClosure R S) S ?_⟩
    simpa only [← IsScalarTower.algebraMap_apply]
-/
protected lemma IsLocalization.integralClosure
    (M : Submonoid R) [IsLocalization M Rf] [IsLocalization (Algebra.algebraMapSubmonoid S M) Sf]
    [Algebra (integralClosure R S) (integralClosure Rf Sf)]
    [IsScalarTower (integralClosure R S) (integralClosure Rf Sf) Sf]
    [IsScalarTower R (integralClosure R S) (integralClosure Rf Sf)] :
    IsLocalization (Algebra.algebraMapSubmonoid (integralClosure R S) M)
      (integralClosure Rf Sf) := by
  refine ⟨⟨?_, ?_, ?_⟩⟩
  · rintro ⟨_, f, hf, rfl⟩
    convert!
      (IsLocalization.map_units (S := Rf) ⟨f, hf⟩).map (algebraMap Rf (integralClosure Rf Sf))
    simp [← IsScalarTower.algebraMap_apply]
  · rintro ⟨s, hs⟩
    obtain ⟨⟨x, _, m₁, hm₁, rfl⟩, e⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid S M) s
    simp only [← IsScalarTower.algebraMap_apply] at e
    obtain ⟨⟨m₂, hm₂⟩, hm₂s⟩ := IsIntegral.exists_multiple_integral_of_isLocalization M _ hs
    simp only [Submonoid.smul_def, Algebra.smul_def] at hm₂s
    obtain ⟨m₃, hm₃, hm₃s⟩ := IsLocalization.exists_isIntegral_smul_of_isIntegral_map (Sₘ := Sf)
M (x := m₂ • x) by
        simp only [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, ← e, ← mul_assoc]
        exact hm₂s.mul (.algebraMap (Algebra.IsIntegral.isIntegral _))
    refine ⟨⟨⟨_, hm₃s⟩, _, _, mul_mem hm₁ (mul_mem hm₂ hm₃), rfl⟩, ?_⟩
    · apply (FaithfulSMul.algebraMap_injective (integralClosure Rf Sf) Sf)
      simp [← IsScalarTower.algebraMap_apply, e, ← mul_assoc, Algebra.smul_def]
      ring
  · rintro ⟨a, ha⟩ ⟨b, hb⟩ e
    have := congr(algebraMap _ Sf $e)
    have : algebraMap S Sf a = algebraMap S Sf b := by
      simpa only [← IsScalarTower.algebraMap_apply] using! this
    obtain ⟨⟨_, m, hm, rfl⟩, h⟩ :=
      (IsLocalization.eq_iff_exists (Algebra.algebraMapSubmonoid S M) _).mp this
    refine ⟨⟨_, m, hm, rfl⟩, FaithfulSMul.algebraMap_injective (integralClosure R S) S ?_⟩
    simpa only [← IsScalarTower.algebraMap_apply]

-- We take in an arbitrary `Algebra (integralClosure R S) (integralClosure Rf Sf)` instance
-- so that it applies more easily.
/--
lemma `IsLocalization.Away.integralClosure` / 引理 `IsLocalization.Away.integralClosure`

English:
lemma IsLocalization.Away.integralClosure
  proof: by
  convert! IsLocalization.integralClosure (S := S) (Rf := Rf) (Sf := Sf) (.powers f)
  simp

中文:
引理 是Localization.Away.integralClosure
  证明: by
  convert! IsLocalization.integralClosure (S := S) (Rf := Rf) (Sf := Sf) (.powers f)
  simp
-/
protected lemma IsLocalization.Away.integralClosure
    (f : R) [IsLocalization.Away f Rf] [IsLocalization.Away (algebraMap R S f) Sf]
    [Algebra (integralClosure R S) (integralClosure Rf Sf)]
    [IsScalarTower (integralClosure R S) (integralClosure Rf Sf) Sf]
    [IsScalarTower R (integralClosure R S) (integralClosure Rf Sf)] :
    IsLocalization.Away (algebraMap R (integralClosure R S) f) (integralClosure Rf Sf) := by
  convert! IsLocalization.integralClosure (S := S) (Rf := Rf) (Sf := Sf) (.powers f)
  simp

end
namespace IsFractionRing

variable (R S K)

/--
theorem `isAlgebraic_iff'` / 定理 `isAlgebraic_iff'`

English:
theorem isAlgebraic_iff'
  statement: [Field K] [IsDomain R] [Algebra R K] [Algebra S K]
  proof: by
  simp only [Algebra.isAlgebraic_def]
  constructor
  · intro h x
    let := MulActionWithZero.nontrivial S K
    let := FractionRing.liftAlgebra R K
    have := FractionRing.isScalarTower_liftAlgebra R K
    rw [IsFractionRing.isAlgebraic_iff R (FractionRing R) K]; rw [isAlgebraic_iff_isIntegral]
    obtain ⟨a : S, b, ha, rfl⟩ := div_surjective S x
    obtain ⟨f, hf₁, hf₂⟩ := h b
    rw [div_eq_mul_inv]
refine .mul ?_ (.inv ?_) <;> exact isAlgebraic_iff_isIntegral.mp
      (h _).algebraMap.extendScalars (FaithfulSMul.algebraMap_injective R _)
  · intro h x
    obtain ⟨f, hf₁, hf₂⟩ := h (algebraMap S K x)
    use f, hf₁
    rw [Polynomial.aeval_algebraMap_apply] at hf₂
    exact
      (injective_iff_map_eq_zero (algebraMap S K)).1 (FaithfulSMul.algebraMap_injective _ _) _
        hf₂

中文:
定理 isAlgebraic_iff'
  结论: [域 K] [是整环 R] [代数 R K] [代数 S K]
  证明: by
  simp only [Algebra.isAlgebraic_def]
  constructor
  · intro h x
    let := MulActionWithZero.nontrivial S K
    let := FractionRing.liftAlgebra R K
    have := FractionRing.isScalarTower_liftAlgebra R K
    rw [IsFractionRing.isAlgebraic_iff R (FractionRing R) K]; rw [isAlgebraic_iff_isIntegral]
    obtain ⟨a : S, b, ha, rfl⟩ := div_surjective S x
    obtain ⟨f, hf₁, hf₂⟩ := h b
    rw [div_eq_mul_inv]
refine .mul ?_ (.inv ?_) <;> exact isAlgebraic_iff_isIntegral.mp
      (h _).algebraMap.extendScalars (FaithfulSMul.algebraMap_injective R _)
  · intro h x
    obtain ⟨f, hf₁, hf₂⟩ := h (algebraMap S K x)
    use f, hf₁
    rw [Polynomial.aeval_algebraMap_apply] at hf₂
    exact
      (injective_iff_map_eq_zero (algebraMap S K)).1 (FaithfulSMul.algebraMap_injective _ _) _
        hf₂

Depends on / 依赖: Algebra, Algebra.isAlgebraic_def, FaithfulSMul, FaithfulSMul.algebraMap_in, FractionRing, FractionRing.isScalarTower_liftAlgebra, FractionRing.liftAlgebra, IsFractionRing, IsFractionRing.isAlgebraic_iff, MulActionWithZero, MulActionWithZero.nontrivial, algebraMap, algebraMap.extendScalars, algebraMap_in, div_eq_mul_inv, div_surjective, extendScalars, isAlgebraic_def, isAlgebraic_iff, isAlgebraic_iff_isIntegral
-/
theorem isAlgebraic_iff' [Field K] [IsDomain R] [Algebra R K] [Algebra S K]
    [Module.IsTorsionFree R K] [IsFractionRing S K] [IsScalarTower R S K] :
    Algebra.IsAlgebraic R S ↔ Algebra.IsAlgebraic R K := by
  simp only [Algebra.isAlgebraic_def]
  constructor
  · intro h x
    let := MulActionWithZero.nontrivial S K
    let := FractionRing.liftAlgebra R K
    have := FractionRing.isScalarTower_liftAlgebra R K
    rw [IsFractionRing.isAlgebraic_iff R (FractionRing R) K]; rw [isAlgebraic_iff_isIntegral]
    obtain ⟨a : S, b, ha, rfl⟩ := div_surjective S x
    obtain ⟨f, hf₁, hf₂⟩ := h b
    rw [div_eq_mul_inv]
refine .mul ?_ (.inv ?_) <;> exact isAlgebraic_iff_isIntegral.mp
      (h _).algebraMap.extendScalars (FaithfulSMul.algebraMap_injective R _)
  · intro h x
    obtain ⟨f, hf₁, hf₂⟩ := h (algebraMap S K x)
    use f, hf₁
    rw [Polynomial.aeval_algebraMap_apply] at hf₂
    exact
      (injective_iff_map_eq_zero (algebraMap S K)).1 (FaithfulSMul.algebraMap_injective _ _) _
        hf₂

open nonZeroDivisors

variable {S K}

/--
theorem `ideal_span_singleton_map_subset` / 定理 `ideal_span_singleton_map_subset`

English:
theorem ideal_span_singleton_map_subset
  statement: {L : Type*} [IsDomain R] [IsDomain S] [Field K] [Field L]
  proof: by
  intro x hx
  obtain ⟨x', rfl⟩ := Ideal.mem_span_singleton.mp hx
  obtain ⟨y', z', rfl⟩ := IsLocalization.exists_mk'_eq S⁰ x'
  obtain ⟨y, z, hz0, yz_eq⟩ :=
    Algebra.IsAlgebraic.exists_smul_eq_mul R y' (nonZeroDivisors.coe_ne_zero z')
  have injRS : Function.Injective (algebraMap R S) := by
    refine
      Function.Injective.of_comp (show Function.Injective (algebraMap S L ∘ algebraMap R S) from ?_)
    rwa [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq]
  have hz0' : algebraMap R S z in S⁰ :=
    map_mem_nonZeroDivisors (algebraMap R S) injRS (mem_nonZeroDivisors_of_ne_zero hz0)
  have mk_yz_eq : IsLocalization.mk' L y' z' = IsLocalization.mk' L y ⟨_, hz0'⟩ := by
    rw [Algebra.smul_def]; rw [mul_comm _ y]; rw [mul_comm _ y'] at yz_eq
    exact IsLocalization.mk'_eq_of_eq (by rw [mul_comm _ y, mul_comm _ y', yz_eq])
  suffices hy : algebraMap S L (a * y) in Submodule.span K ((algebraMap S L) '' b) by
    rw [mk_yz_eq]; rw [IsFractionRing.mk'_eq_div]; rw [← IsScalarTower.algebraMap_apply]; rw [IsScalarTower.algebraMap_apply R K L]; rw [div_eq_mul_inv]; rw [← mul_assoc]; rw [mul_comm]; rw [← map_inv₀]; rw [←
      Algebra.smul_def]; rw [← map_mul]
    exact (Submodule.span K _).smul_mem _ hy
  refine Submodule.span_subset_span R K _ ?_
  rw [Submodule.span_algebraMap_image_of_tower]
  -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to specify the value of `f` here:
  exact Submodule.mem_map_of_mem (f := LinearMap.restrictScalars _ _)
    (h (Ideal.mem_span_singleton.mpr ⟨y, rfl⟩))

中文:
定理 ideal_span_singleton_map_subset
  结论: {L : 类型} [是整环 R] [是整环 S] [域 K] [域 L]
  证明: by
  intro x hx
  obtain ⟨x', rfl⟩ := Ideal.mem_span_singleton.mp hx
  obtain ⟨y', z', rfl⟩ := IsLocalization.exists_mk'_eq S⁰ x'
  obtain ⟨y, z, hz0, yz_eq⟩ :=
    Algebra.IsAlgebraic.exists_smul_eq_mul R y' (nonZeroDivisors.coe_ne_zero z')
  have injRS : Function.Injective (algebraMap R S) := by
    refine
      Function.Injective.of_comp (show Function.Injective (algebraMap S L ∘ algebraMap R S) from ?_)
    rwa [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq]
  have hz0' : algebraMap R S z in S⁰ :=
    map_mem_nonZeroDivisors (algebraMap R S) injRS (mem_nonZeroDivisors_of_ne_zero hz0)
  have mk_yz_eq : IsLocalization.mk' L y' z' = IsLocalization.mk' L y ⟨_, hz0'⟩ := by
    rw [Algebra.smul_def]; rw [mul_comm _ y]; rw [mul_comm _ y'] at yz_eq
    exact IsLocalization.mk'_eq_of_eq (by rw [mul_comm _ y, mul_comm _ y', yz_eq])
  suffices hy : algebraMap S L (a * y) in Submodule.span K ((algebraMap S L) '' b) by
    rw [mk_yz_eq]; rw [IsFractionRing.mk'_eq_div]; rw [← IsScalarTower.algebraMap_apply]; rw [IsScalarTower.algebraMap_apply R K L]; rw [div_eq_mul_inv]; rw [← mul_assoc]; rw [mul_comm]; rw [← map_inv₀]; rw [←
      Algebra.smul_def]; rw [← map_mul]
    exact (Submodule.span K _).smul_mem _ hy
  refine Submodule.span_subset_span R K _ ?_
  rw [Submodule.span_algebraMap_image_of_tower]
  -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to specify the value of `f` here:
  exact Submodule.mem_map_of_mem (f := LinearMap.restrictScalars _ _)
    (h (Ideal.mem_span_singleton.mpr ⟨y, rfl⟩))

Depends on / 依赖: Algebra, Algebra.IsAlgebraic.exists_smul_eq_mul, Function, Function.Injective, Function.Injective.of_comp, Ideal.mem_span_singleton.mp, Injective, IsAlgebraic, IsLocalization, IsLocalization.exists_mk, IsScalarTower, IsScalarTower.algebraMap_eq, RingHom, RingHom.coe_comp, algebraMap, algebraMap_eq, coe_comp, coe_ne_zero, exists_mk, exists_smul_eq_mul
-/
theorem ideal_span_singleton_map_subset {L : Type*} [IsDomain R] [IsDomain S] [Field K] [Field L]
    [Algebra R K] [Algebra R L] [Algebra S L] [Algebra.IsAlgebraic R S] [IsFractionRing S L]
    [Algebra K L] [IsScalarTower R S L] [IsScalarTower R K L] {a : S} {b : Set S}
    (inj : Function.Injective (algebraMap R L))
    (h : (Ideal.span ({a} : Set S) : Set S) subseteq Submodule.span R b) :
    (Ideal.span ({algebraMap S L a} : Set L) : Set L) subseteq Submodule.span K (algebraMap S L '' b) := by
  intro x hx
  obtain ⟨x', rfl⟩ := Ideal.mem_span_singleton.mp hx
  obtain ⟨y', z', rfl⟩ := IsLocalization.exists_mk'_eq S⁰ x'
  obtain ⟨y, z, hz0, yz_eq⟩ :=
    Algebra.IsAlgebraic.exists_smul_eq_mul R y' (nonZeroDivisors.coe_ne_zero z')
  have injRS : Function.Injective (algebraMap R S) := by
    refine
      Function.Injective.of_comp (show Function.Injective (algebraMap S L ∘ algebraMap R S) from ?_)
    rwa [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq]
  have hz0' : algebraMap R S z in S⁰ :=
    map_mem_nonZeroDivisors (algebraMap R S) injRS (mem_nonZeroDivisors_of_ne_zero hz0)
  have mk_yz_eq : IsLocalization.mk' L y' z' = IsLocalization.mk' L y ⟨_, hz0'⟩ := by
    rw [Algebra.smul_def]; rw [mul_comm _ y]; rw [mul_comm _ y'] at yz_eq
    exact IsLocalization.mk'_eq_of_eq (by rw [mul_comm _ y, mul_comm _ y', yz_eq])
  suffices hy : algebraMap S L (a * y) in Submodule.span K ((algebraMap S L) '' b) by
    rw [mk_yz_eq]; rw [IsFractionRing.mk'_eq_div]; rw [← IsScalarTower.algebraMap_apply]; rw [IsScalarTower.algebraMap_apply R K L]; rw [div_eq_mul_inv]; rw [← mul_assoc]; rw [mul_comm]; rw [← map_inv₀]; rw [←
      Algebra.smul_def]; rw [← map_mul]
    exact (Submodule.span K _).smul_mem _ hy
  refine Submodule.span_subset_span R K _ ?_
  rw [Submodule.span_algebraMap_image_of_tower]
  -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to specify the value of `f` here:
  exact Submodule.mem_map_of_mem (f := LinearMap.restrictScalars _ _)
    (h (Ideal.mem_span_singleton.mpr ⟨y, rfl⟩))

end IsFractionRing

open nonZeroDivisors in
/--
lemma `isAlgebraic_of_isFractionRing` / 引理 `isAlgebraic_of_isFractionRing`

English:
lemma isAlgebraic_of_isFractionRing
  statement: (R S K L) [CommRing R] [CommRing S] [Field K] [CommRing L]
  proof: by
  constructor
  intro x
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq S⁰ x
  apply IsIntegral.isAlgebraic
  rw [IsLocalization.mk'_eq_mul_mk'_one]
  apply RingHom.IsIntegralElem.mul
  · apply IsIntegral.tower_top (R := R)
    apply IsIntegral.map (IsScalarTower.toAlgHom R S L)
    exact Algebra.IsIntegral.isIntegral x
  · change IsIntegral _ _
    rw [← isAlgebraic_iff_isIntegral]; rw [← IsAlgebraic.invOf_iff]; rw [isAlgebraic_iff_isIntegral]
    apply IsIntegral.tower_top (R := R)
    apply IsIntegral.map (IsScalarTower.toAlgHom R S L)
    exact Algebra.IsIntegral.isIntegral (s : S)

中文:
引理 isAlgebraic_of_isFractionRing
  结论: (R S K L) [交换环 R] [交换环 S] [域 K] [交换环 L]
  证明: by
  constructor
  intro x
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq S⁰ x
  apply IsIntegral.isAlgebraic
  rw [IsLocalization.mk'_eq_mul_mk'_one]
  apply RingHom.IsIntegralElem.mul
  · apply IsIntegral.tower_top (R := R)
    apply IsIntegral.map (IsScalarTower.toAlgHom R S L)
    exact Algebra.IsIntegral.isIntegral x
  · change IsIntegral _ _
    rw [← isAlgebraic_iff_isIntegral]; rw [← IsAlgebraic.invOf_iff]; rw [isAlgebraic_iff_isIntegral]
    apply IsIntegral.tower_top (R := R)
    apply IsIntegral.map (IsScalarTower.toAlgHom R S L)
    exact Algebra.IsIntegral.isIntegral (s : S)

Depends on / 依赖: Algebra, Algebra.IsIntegral.isIntegral, IsAlgebraic, IsAlgebraic.invOf_iff, IsIntegral, IsIntegral.isAlgebraic, IsIntegral.map, IsIntegral.tower_top, IsIntegralElem, IsLocalization, IsLocalization.exists_mk, IsLocalization.mk, IsScalarTower, IsScalarTower.toAlgHom, RingHom, RingHom.IsIntegralElem.mul, _eq_mul_mk, _one, exists_mk, invOf_iff
-/
lemma isAlgebraic_of_isFractionRing (R S K L) [CommRing R] [CommRing S] [Field K] [CommRing L]
    [Algebra R S] [Algebra R K] [Algebra R L] [Algebra S L] [Algebra K L] [IsScalarTower R S L]
    [IsScalarTower R K L] [IsFractionRing S L]
    [Algebra.IsIntegral R S] : Algebra.IsAlgebraic K L := by
  constructor
  intro x
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq S⁰ x
  apply IsIntegral.isAlgebraic
  rw [IsLocalization.mk'_eq_mul_mk'_one]
  apply RingHom.IsIntegralElem.mul
  · apply IsIntegral.tower_top (R := R)
    apply IsIntegral.map (IsScalarTower.toAlgHom R S L)
    exact Algebra.IsIntegral.isIntegral x
  · change IsIntegral _ _
    rw [← isAlgebraic_iff_isIntegral]; rw [← IsAlgebraic.invOf_iff]; rw [isAlgebraic_iff_isIntegral]
    apply IsIntegral.tower_top (R := R)
    apply IsIntegral.map (IsScalarTower.toAlgHom R S L)
    exact Algebra.IsIntegral.isIntegral (s : S)
