/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Johan Commelin
-/
module

public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.RingTheory.Algebraic.Integral

/-!
# Minimal polynomials on an algebra over a field

This file specializes the theory of minpoly to the setting of field extensions
and derives some well-known properties, amongst which the fact that minimal polynomials
are irreducible, and uniquely determined by their defining property.

-/

@[expose] public section


open Polynomial Set Function minpoly

namespace minpoly

variable {A B : Type*}
variable (A) [Field A]

section Ring

variable [Ring B] [Algebra A B] (x : B)

/--
theorem `degree_le_of_ne_zero` / 定理 `degree_le_of_ne_zero`

English:
theorem degree_le_of_ne_zero
  given: {p : A[X]} (pnz : p != 0) (hp : Polynomial.aeval x p = 0)
  proof: calc
    degree (minpoly A x) <= degree (p * C (leadingCoeff p)⁻¹) :=
      min A x (monic_mul_leadingCoeff_inv pnz) (by simp [hp])
    _ = degree p := degree_mul_leadingCoeff_inv p pnz

中文:
定理 degree_le_of_ne_zero
  条件: {p : A[X]} (pnz : p != 0) (hp : Polynomial.aeval x p = 0)
  证明: calc
    degree (minpoly A x) <= degree (p * C (leadingCoeff p)⁻¹) :=
      min A x (monic_mul_leadingCoeff_inv pnz) (by simp [hp])
    _ = degree p := degree_mul_leadingCoeff_inv p pnz

Depends on / 依赖: degree, degree_mul_leadingCoeff_inv, leadingCoeff, minpoly, monic_mul_leadingCoeff_inv
-/
theorem degree_le_of_ne_zero {p : A[X]} (pnz : p != 0) (hp : Polynomial.aeval x p = 0) :
    degree (minpoly A x) <= degree p :=
  calc
    degree (minpoly A x) <= degree (p * C (leadingCoeff p)⁻¹) :=
      min A x (monic_mul_leadingCoeff_inv pnz) (by simp [hp])
    _ = degree p := degree_mul_leadingCoeff_inv p pnz

/--
theorem `ne_zero_of_finite` / 定理 `ne_zero_of_finite`

English:
theorem ne_zero_of_finite
  given: (e : B) [FiniteDimensional A B]
  statement: minpoly A e != 0
  proof: minpoly.ne_zero .of_finite A _

中文:
定理 ne_zero_of_finite
  条件: (e : B) [FiniteDimensional A B]
  结论: minpoly A e != 0
  证明: minpoly.ne_zero .of_finite A _

Depends on / 依赖: minpoly, minpoly.ne_zero, ne_zero, of_finite
-/
theorem ne_zero_of_finite (e : B) [FiniteDimensional A B] : minpoly A e != 0 :=
minpoly.ne_zero .of_finite A _

/--
theorem `unique` / 定理 `unique`

English:
theorem unique
  statement: {p : A[X]} (pmonic : p.Monic) (hp : Polynomial.aeval x p = 0)
  proof: by
  have hx : IsIntegral A x := ⟨p, pmonic, hp⟩
  symm; apply eq_of_sub_eq_zero
  by_contra hnz
.not_gt apply degree_le_of_ne_zero A x hnz (by simp [hp])
  apply degree_sub_lt_left _ (minpoly.ne_zero hx)
  · rw [(monic hx).leadingCoeff, pmonic.leadingCoeff]
  · exact le_antisymm (min A x pmonic hp)

中文:
定理 unique
  结论: {p : A[X]} (pmonic : p.Monic) (hp : Polynomial.aeval x p = 0)
  证明: by
  have hx : IsIntegral A x := ⟨p, pmonic, hp⟩
  symm; apply eq_of_sub_eq_zero
  by_contra hnz
.not_gt apply degree_le_of_ne_zero A x hnz (by simp [hp])
  apply degree_sub_lt_left _ (minpoly.ne_zero hx)
  · rw [(monic hx).leadingCoeff, pmonic.leadingCoeff]
  · exact le_antisymm (min A x pmonic hp)

Depends on / 依赖: IsIntegral, degree_le_of_ne_zero, degree_sub_lt_left, eq_of_sub_eq_zero, le_antisymm, leadingCoeff, minpoly, minpoly.ne_zero, ne_zero, not_gt, pmonic, pmonic.leadingCoeff
-/
theorem unique {p : A[X]} (pmonic : p.Monic) (hp : Polynomial.aeval x p = 0)
    (pmin : forall q : A[X], q.Monic -> Polynomial.aeval x q = 0 -> degree p <= degree q) :
    p = minpoly A x := by
  have hx : IsIntegral A x := ⟨p, pmonic, hp⟩
  symm; apply eq_of_sub_eq_zero
  by_contra hnz
.not_gt apply degree_le_of_ne_zero A x hnz (by simp [hp])
  apply degree_sub_lt_left _ (minpoly.ne_zero hx)
  · rw [(monic hx).leadingCoeff, pmonic.leadingCoeff]
  · exact le_antisymm (min A x pmonic hp) (pmin (minpoly A x) (monic hx) (aeval A x))

/--
theorem `unique_of_degree_le_degree_minpoly` / 定理 `unique_of_degree_le_degree_minpoly`

English:
theorem unique_of_degree_le_degree_minpoly
  statement: {p : A[X]} (pmonic : p.Monic) (hp : p.aeval x = 0)
  proof: unique _ _ pmonic hp fun _ qm hq => pmin.trans min _ _ qm hq

中文:
定理 unique_of_degree_le_degree_minpoly
  结论: {p : A[X]} (pmonic : p.Monic) (hp : p.aeval x = 0)
  证明: unique _ _ pmonic hp fun _ qm hq => pmin.trans min _ _ qm hq

Depends on / 依赖: pmin.trans, pmonic, unique
-/
theorem unique_of_degree_le_degree_minpoly {p : A[X]} (pmonic : p.Monic) (hp : p.aeval x = 0)
    (pmin : p.degree <= (minpoly A x).degree) : p = minpoly A x :=
unique _ _ pmonic hp fun _ qm hq => pmin.trans min _ _ qm hq

/--
theorem `dvd` / 定理 `dvd`

English:
theorem dvd
  given: {p : A[X]} (hp : Polynomial.aeval x p = 0)
  statement: minpoly A x ∣ p
  proof: by
  by_cases hp0 : p = 0
  · simp only [hp0, dvd_zero]
  have hx : IsIntegral A x := IsAlgebraic.isIntegral ⟨p, hp0, hp⟩
  rw [← modByMonic_eq_zero_iff_dvd (monic hx)]
  by_contra hnz
  apply degree_le_of_ne_zero A x hnz
.not_gt ((aeval_modByMonic_eq_self_of_root (aeval _ _)).trans hp)
  exact degr

中文:
定理 dvd
  条件: {p : A[X]} (hp : Polynomial.aeval x p = 0)
  结论: minpoly A x ∣ p
  证明: by
  by_cases hp0 : p = 0
  · simp only [hp0, dvd_zero]
  have hx : IsIntegral A x := IsAlgebraic.isIntegral ⟨p, hp0, hp⟩
  rw [← modByMonic_eq_zero_iff_dvd (monic hx)]
  by_contra hnz
  apply degree_le_of_ne_zero A x hnz
.not_gt ((aeval_modByMonic_eq_self_of_root (aeval _ _)).trans hp)
  exact degr

Depends on / 依赖: IsAlgebraic, IsAlgebraic.isIntegral, IsIntegral, aeval_modByMonic_eq_self_of_root, degree_le_of_ne_zero, degree_modByMonic_lt, dvd_zero, isIntegral, modByMonic_eq_zero_iff_dvd, not_gt
-/
theorem dvd {p : A[X]} (hp : Polynomial.aeval x p = 0) : minpoly A x ∣ p := by
  by_cases hp0 : p = 0
  · simp only [hp0, dvd_zero]
  have hx : IsIntegral A x := IsAlgebraic.isIntegral ⟨p, hp0, hp⟩
  rw [← modByMonic_eq_zero_iff_dvd (monic hx)]
  by_contra hnz
  apply degree_le_of_ne_zero A x hnz
.not_gt ((aeval_modByMonic_eq_self_of_root (aeval _ _)).trans hp)
  exact degree_modByMonic_lt _ (monic hx)

variable {A x} in
/--
lemma `dvd_iff` / 引理 `dvd_iff`

English:
lemma dvd_iff
  given: {p : A[X]}
  statement: minpoly A x ∣ p ↔ Polynomial.aeval x p = 0
  proof: ⟨fun ⟨q, hq⟩ => by rw [hq, map_mul, aeval, zero_mul], minpoly.dvd A x⟩

中文:
引理 dvd_iff
  条件: {p : A[X]}
  结论: minpoly A x ∣ p ↔ Polynomial.aeval x p = 0
  证明: ⟨fun ⟨q, hq⟩ => by rw [hq, map_mul, aeval, zero_mul], minpoly.dvd A x⟩

Depends on / 依赖: map_mul, minpoly, minpoly.dvd, zero_mul
-/
lemma dvd_iff {p : A[X]} : minpoly A x ∣ p ↔ Polynomial.aeval x p = 0 :=
  ⟨fun ⟨q, hq⟩ => by rw [hq, map_mul, aeval, zero_mul], minpoly.dvd A x⟩

/--
theorem `isRadical` / 定理 `isRadical`

English:
theorem isRadical
  given: [IsReduced B]
  statement: IsRadical (minpoly A x)
  proof: fun n p dvd => by
  rw [dvd_iff] at dvd ⊢; rw [map_pow] at dvd; exact IsReduced.eq_zero _ ⟨n, dvd⟩

中文:
定理 isRadical
  条件: [IsReduced B]
  结论: IsRadical (minpoly A x)
  证明: fun n p dvd => by
  rw [dvd_iff] at dvd ⊢; rw [map_pow] at dvd; exact IsReduced.eq_zero _ ⟨n, dvd⟩

Depends on / 依赖: IsReduced, IsReduced.eq_zero, dvd_iff, eq_zero, map_pow
-/
theorem isRadical [IsReduced B] : IsRadical (minpoly A x) := fun n p dvd => by
  rw [dvd_iff] at dvd ⊢; rw [map_pow] at dvd; exact IsReduced.eq_zero _ ⟨n, dvd⟩

/--
theorem `dvd_map_of_isScalarTower` / 定理 `dvd_map_of_isScalarTower`

English:
theorem dvd_map_of_isScalarTower
  statement: (A K : Type*) {R : Type*} [CommRing A] [Field K] [Ring R]
  proof: by
  refine minpoly.dvd K x ?_
  rw [aeval_map_algebraMap]; rw [minpoly.aeval]

中文:
定理 dvd_map_of_isScalarTower
  结论: (A K : 类型) {R : 类型} [CommRing A] [Field K] [Ring R]
  证明: by
  refine minpoly.dvd K x ?_
  rw [aeval_map_algebraMap]; rw [minpoly.aeval]

Depends on / 依赖: aeval_map_algebraMap, minpoly, minpoly.aeval, minpoly.dvd
-/
theorem dvd_map_of_isScalarTower (A K : Type*) {R : Type*} [CommRing A] [Field K] [Ring R]
    [Algebra A K] [Algebra A R] [Algebra K R] [IsScalarTower A K R] (x : R) :
    minpoly K x ∣ (minpoly A x).map (algebraMap A K) := by
  refine minpoly.dvd K x ?_
  rw [aeval_map_algebraMap]; rw [minpoly.aeval]

/--
theorem `dvd_map_of_isScalarTower'` / 定理 `dvd_map_of_isScalarTower'`

English:
theorem dvd_map_of_isScalarTower'
  statement: (R : Type*) {S : Type*} (K L : Type*) [CommRing R]
  proof: by
  apply minpoly.dvd K (algebraMap S L s)
  rw [← map_aeval_eq_aeval_map]; rw [minpoly.aeval]; rw [map_zero]
  rw [← IsScalarTower.algebraMap_eq]; rw [← IsScalarTower.algebraMap_eq]

中文:
定理 dvd_map_of_isScalarTower'
  结论: (R : 类型) {S : 类型} (K L : 类型) [CommRing R]
  证明: by
  apply minpoly.dvd K (algebraMap S L s)
  rw [← map_aeval_eq_aeval_map]; rw [minpoly.aeval]; rw [map_zero]
  rw [← IsScalarTower.algebraMap_eq]; rw [← IsScalarTower.algebraMap_eq]

Depends on / 依赖: IsScalarTower, IsScalarTower.algebraMap_eq, algebraMap, algebraMap_eq, map_aeval_eq_aeval_map, map_zero, minpoly, minpoly.aeval, minpoly.dvd
-/
theorem dvd_map_of_isScalarTower' (R : Type*) {S : Type*} (K L : Type*) [CommRing R]
    [CommRing S] [Field K] [Ring L] [Algebra R S] [Algebra R K] [Algebra S L] [Algebra K L]
    [Algebra R L] [IsScalarTower R K L] [IsScalarTower R S L] (s : S) :
    minpoly K (algebraMap S L s) ∣ map (algebraMap R K) (minpoly R s) := by
  apply minpoly.dvd K (algebraMap S L s)
  rw [← map_aeval_eq_aeval_map]; rw [minpoly.aeval]; rw [map_zero]
  rw [← IsScalarTower.algebraMap_eq]; rw [← IsScalarTower.algebraMap_eq]

/--
theorem `aeval_of_isScalarTower` / 定理 `aeval_of_isScalarTower`

English:
theorem aeval_of_isScalarTower
  statement: (R : Type*) {K T U : Type*} [CommRing R] [Field K] [CommRing T]
  proof: aeval_map_algebraMap K y (minpoly R x) ▸
    eval₂_eq_zero_of_dvd_of_eval₂_eq_zero (algebraMap K U) y
      (minpoly.dvd_map_of_isScalarTower R K x) hy

中文:
定理 aeval_of_isScalarTower
  结论: (R : 类型) {K T U : 类型} [CommRing R] [Field K] [CommRing T]
  证明: aeval_map_algebraMap K y (minpoly R x) ▸
    eval₂_eq_zero_of_dvd_of_eval₂_eq_zero (algebraMap K U) y
      (minpoly.dvd_map_of_isScalarTower R K x) hy

Depends on / 依赖: aeval_map_algebraMap, algebraMap, dvd_map_of_isScalarTower, minpoly, minpoly.dvd_map_of_isScalarTower
-/
theorem aeval_of_isScalarTower (R : Type*) {K T U : Type*} [CommRing R] [Field K] [CommRing T]
    [Algebra R K] [Algebra K T] [Algebra R T] [IsScalarTower R K T] [CommSemiring U] [Algebra K U]
    [Algebra R U] [IsScalarTower R K U] (x : T) (y : U)
    (hy : Polynomial.aeval y (minpoly K x) = 0) : Polynomial.aeval y (minpoly R x) = 0 :=
  aeval_map_algebraMap K y (minpoly R x) ▸
    eval₂_eq_zero_of_dvd_of_eval₂_eq_zero (algebraMap K U) y
      (minpoly.dvd_map_of_isScalarTower R K x) hy

/--
theorem `map_algebraMap` / 定理 `map_algebraMap`

English:
theorem map_algebraMap
  statement: {F E A : Type*} [Field F] [Field E] [CommRing A]
  proof: by
  refine eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic ha.tower_top)
    ((algebraMap F E).injective.monic_map_iff.mp <| minpoly.monic ha)
    (minpoly.dvd E a (by simp)) ?_
  obtain ⟨g, hg, hgdeg, hgmon⟩ := lifts_and_natDegree_eq_and_monic h (minpoly.monic ha.tower_top)
  rw [natDegree_map];

中文:
定理 map_algebraMap
  结论: {F E A : 类型} [Field F] [Field E] [CommRing A]
  证明: by
  refine eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic ha.tower_top)
    ((algebraMap F E).injective.monic_map_iff.mp <| minpoly.monic ha)
    (minpoly.dvd E a (by simp)) ?_
  obtain ⟨g, hg, hgdeg, hgmon⟩ := lifts_and_natDegree_eq_and_monic h (minpoly.monic ha.tower_top)
  rw [natDegree_map];

Depends on / 依赖: IsScalarTower, IsScalarTower.algebraMap_eq, RingHom, RingHom.comp_app, aeval_map_algebraMap, algebraMap, algebraMap_eq, coe_mapRingHom, comp_app, eq_of_monic_of_dvd_of_natDegree_le, ha.tower_top, hgmon.ne_zero, injective, injective.monic_map_iff.mp, lifts_and_natDegree_eq_and_monic, mapRingHom_comp, minpoly, minpoly.dvd, minpoly.monic, monic_map_iff
-/
theorem map_algebraMap {F E A : Type*} [Field F] [Field E] [CommRing A]
    [Algebra F E] [Algebra E A] [Algebra F A] [IsScalarTower F E A]
    {a : A} (ha : IsIntegral F a) (h : minpoly E a in lifts (algebraMap F E)) :
    (minpoly F a).map (algebraMap F E) = minpoly E a := by
  refine eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic ha.tower_top)
    ((algebraMap F E).injective.monic_map_iff.mp <| minpoly.monic ha)
    (minpoly.dvd E a (by simp)) ?_
  obtain ⟨g, hg, hgdeg, hgmon⟩ := lifts_and_natDegree_eq_and_monic h (minpoly.monic ha.tower_top)
  rw [natDegree_map]; rw [← hgdeg]
  refine natDegree_le_of_dvd (minpoly.dvd F a ?_) hgmon.ne_zero
  rw [← aeval_map_algebraMap A]; rw [IsScalarTower.algebraMap_eq F E A]; rw [← coe_mapRingHom]; rw [← mapRingHom_comp]; rw [RingHom.comp_apply]; rw [coe_mapRingHom]; rw [coe_mapRingHom]; rw [hg]; rw [aeval_map_algebraMap]; rw [minpoly.aeval]

/-- See also `minpoly.ker_eval` which relaxes the assumptions on `A` in exchange for
stronger assumptions on `B`. -/
@[simp]
/--
lemma `ker_aeval_eq_span_minpoly` / 引理 `ker_aeval_eq_span_minpoly`

English:
lemma ker_aeval_eq_span_minpoly
  proof: by
  ext p
  simp_rw [RingHom.mem_ker, ← minpoly.dvd_iff, Submodule.mem_span_singleton,
    dvd_iff_exists_eq_mul_left, smul_eq_mul, eq_comm (a := p)]

中文:
引理 ker_aeval_eq_span_minpoly
  证明: by
  ext p
  simp_rw [RingHom.mem_ker, ← minpoly.dvd_iff, Submodule.mem_span_singleton,
    dvd_iff_exists_eq_mul_left, smul_eq_mul, eq_comm (a := p)]

Depends on / 依赖: RingHom, RingHom.mem_ker, Submodule, Submodule.mem_span_singleton, dvd_iff, dvd_iff_exists_eq_mul_left, eq_comm, mem_ker, mem_span_singleton, minpoly, minpoly.dvd_iff, simp_rw, smul_eq_mul
-/
lemma ker_aeval_eq_span_minpoly :
    RingHom.ker (Polynomial.aeval x) = A[X] ∙ minpoly A x := by
  ext p
  simp_rw [RingHom.mem_ker, ← minpoly.dvd_iff, Submodule.mem_span_singleton,
    dvd_iff_exists_eq_mul_left, smul_eq_mul, eq_comm (a := p)]

variable {A x}

/--
theorem `eq_of_irreducible_of_monic` / 定理 `eq_of_irreducible_of_monic`

English:
theorem eq_of_irreducible_of_monic
  statement: [Nontrivial B] {p : A[X]} (hp1 : Irreducible p)
  proof: let ⟨_, hq⟩ := dvd A x hp2
eq_of_monic_of_associated hp3 (monic ⟨p, ⟨hp3, hp2⟩⟩)
    mul_one (minpoly A x) ▸ hq.symm ▸ Associated.mul_left _
      (associated_one_iff_isUnit.2 <| (hp1.isUnit_or_isUnit hq).resolve_left <| not_isUnit A x)

中文:
定理 eq_of_irreducible_of_monic
  结论: [Nontrivial B] {p : A[X]} (hp1 : Irreducible p)
  证明: let ⟨_, hq⟩ := dvd A x hp2
eq_of_monic_of_associated hp3 (monic ⟨p, ⟨hp3, hp2⟩⟩)
    mul_one (minpoly A x) ▸ hq.symm ▸ Associated.mul_left _
      (associated_one_iff_isUnit.2 <| (hp1.isUnit_or_isUnit hq).resolve_left <| not_isUnit A x)

Depends on / 依赖: Associated, Associated.mul_left, associated_one_iff_isUnit, eq_of_monic_of_associated, hp1.isUnit_or_isUnit, hq.symm, isUnit_or_isUnit, minpoly, mul_left, mul_one, not_isUnit, resolve_left
-/
theorem eq_of_irreducible_of_monic [Nontrivial B] {p : A[X]} (hp1 : Irreducible p)
    (hp2 : Polynomial.aeval x p = 0) (hp3 : p.Monic) : p = minpoly A x :=
  let ⟨_, hq⟩ := dvd A x hp2
eq_of_monic_of_associated hp3 (monic ⟨p, ⟨hp3, hp2⟩⟩)
    mul_one (minpoly A x) ▸ hq.symm ▸ Associated.mul_left _
      (associated_one_iff_isUnit.2 <| (hp1.isUnit_or_isUnit hq).resolve_left <| not_isUnit A x)

/--
theorem `eq_iff_aeval_eq_zero` / 定理 `eq_iff_aeval_eq_zero`

English:
theorem eq_iff_aeval_eq_zero
  given: [Nontrivial B] {p : A[X]} (irr : Irreducible p) (monic : p.Monic)
  proof: ⟨(· ▸ aeval A x), (eq_of_irreducible_of_monic irr · monic)⟩

中文:
定理 eq_iff_aeval_eq_zero
  条件: [Nontrivial B] {p : A[X]} (irr : Irreducible p) (monic : p.Monic)
  证明: ⟨(· ▸ aeval A x), (eq_of_irreducible_of_monic irr · monic)⟩

Depends on / 依赖: eq_of_irreducible_of_monic
-/
theorem eq_iff_aeval_eq_zero [Nontrivial B] {p : A[X]} (irr : Irreducible p) (monic : p.Monic) :
    p = minpoly A x ↔ Polynomial.aeval x p = 0 :=
  ⟨(· ▸ aeval A x), (eq_of_irreducible_of_monic irr · monic)⟩

/--
theorem `eq_iff_aeval_minpoly_eq_zero` / 定理 `eq_iff_aeval_minpoly_eq_zero`

English:
theorem eq_iff_aeval_minpoly_eq_zero
  statement: [IsDomain B] {C} [Ring C] [Algebra A C] [Nontrivial C]
  proof: eq_iff_aeval_eq_zero (irreducible h) (monic h)

中文:
定理 eq_iff_aeval_minpoly_eq_zero
  结论: [IsDomain B] {C} [Ring C] [Algebra A C] [Nontrivial C]
  证明: eq_iff_aeval_eq_zero (irreducible h) (monic h)

Depends on / 依赖: eq_iff_aeval_eq_zero, irreducible
-/
theorem eq_iff_aeval_minpoly_eq_zero [IsDomain B] {C} [Ring C] [Algebra A C] [Nontrivial C]
    {b : B} (h : IsIntegral A b) {c : C} :
    minpoly A b = minpoly A c ↔ Polynomial.aeval c (minpoly A b) = 0 :=
  eq_iff_aeval_eq_zero (irreducible h) (monic h)

/--
theorem `eq_of_irreducible` / 定理 `eq_of_irreducible`

English:
theorem eq_of_irreducible
  statement: [Nontrivial B] {p : A[X]} (hp1 : Irreducible p)
  proof: by
  have : p.leadingCoeff != 0 := leadingCoeff_ne_zero.mpr hp1.ne_zero
  apply eq_of_irreducible_of_monic
  · exact Associated.irreducible ⟨⟨C p.leadingCoeff⁻¹, C p.leadingCoeff,
      by rwa [← C_mul, inv_mul_cancel₀, C_1], by rwa [← C_mul, mul_inv_cancel₀, C_1]⟩, rfl⟩ hp1
  · rw [aeval_mul, hp2, 

中文:
定理 eq_of_irreducible
  结论: [Nontrivial B] {p : A[X]} (hp1 : Irreducible p)
  证明: by
  have : p.leadingCoeff != 0 := leadingCoeff_ne_zero.mpr hp1.ne_zero
  apply eq_of_irreducible_of_monic
  · exact Associated.irreducible ⟨⟨C p.leadingCoeff⁻¹, C p.leadingCoeff,
      by rwa [← C_mul, inv_mul_cancel₀, C_1], by rwa [← C_mul, mul_inv_cancel₀, C_1]⟩, rfl⟩ hp1
  · rw [aeval_mul, hp2, 

Depends on / 依赖: Associated, Associated.irreducible, C_mul, Polynomial, Polynomial.Monic, aeval_mul, eq_of_irreducible_of_monic, hp1.ne_zero, irreducible, leadingCoeff, leadingCoeff_C, leadingCoeff_mul, leadingCoeff_ne_zero, leadingCoeff_ne_zero.mpr, ne_zero, p.leadingCoeff, zero_mul
-/
theorem eq_of_irreducible [Nontrivial B] {p : A[X]} (hp1 : Irreducible p)
    (hp2 : Polynomial.aeval x p = 0) : p * C p.leadingCoeff⁻¹ = minpoly A x := by
  have : p.leadingCoeff != 0 := leadingCoeff_ne_zero.mpr hp1.ne_zero
  apply eq_of_irreducible_of_monic
  · exact Associated.irreducible ⟨⟨C p.leadingCoeff⁻¹, C p.leadingCoeff,
      by rwa [← C_mul, inv_mul_cancel₀, C_1], by rwa [← C_mul, mul_inv_cancel₀, C_1]⟩, rfl⟩ hp1
  · rw [aeval_mul, hp2, zero_mul]
  · rwa [Polynomial.Monic, leadingCoeff_mul, leadingCoeff_C, mul_inv_cancel₀]

/--
theorem `Irreducible.eq_minpoly` / 定理 `Irreducible.eq_minpoly`

English:
theorem Irreducible.eq_minpoly
  statement: [Nontrivial B] {p : A[X]} (hi : Irreducible p)
  proof: by
  rw [← minpoly.eq_of_irreducible hi hx]; rw [mul_comm]; rw [mul_assoc]; rw [← C_mul]; rw [inv_mul_cancel₀ (leadingCoeff_ne_zero.mpr hi.ne_zero)]; rw [C_1]; rw [mul_one]

中文:
定理 Irreducible.eq_minpoly
  结论: [Nontrivial B] {p : A[X]} (hi : Irreducible p)
  证明: by
  rw [← minpoly.eq_of_irreducible hi hx]; rw [mul_comm]; rw [mul_assoc]; rw [← C_mul]; rw [inv_mul_cancel₀ (leadingCoeff_ne_zero.mpr hi.ne_zero)]; rw [C_1]; rw [mul_one]

Depends on / 依赖: C_mul, eq_of_irreducible, hi.ne_zero, leadingCoeff_ne_zero, leadingCoeff_ne_zero.mpr, minpoly, minpoly.eq_of_irreducible, mul_assoc, mul_comm, mul_one, ne_zero
-/
theorem Irreducible.eq_minpoly [Nontrivial B] {p : A[X]} (hi : Irreducible p)
    (hx : Polynomial.aeval x p = 0) : p = C p.leadingCoeff * minpoly A x := by
  rw [← minpoly.eq_of_irreducible hi hx]; rw [mul_comm]; rw [mul_assoc]; rw [← C_mul]; rw [inv_mul_cancel₀ (leadingCoeff_ne_zero.mpr hi.ne_zero)]; rw [C_1]; rw [mul_one]

/--
theorem `_root_.Irreducible.dvd_iff_aeval_eq_zero` / 定理 `_root_.Irreducible.dvd_iff_aeval_eq_zero`

English:
theorem _root_.Irreducible.dvd_iff_aeval_eq_zero
  statement: [Nontrivial B] {p q : A[X]} (hi : Irreducible p)
  proof: by
  refine ⟨fun hga => dvd_trans ?_ (minpoly.dvd A b hga), ?_⟩
  · rw [← minpoly.eq_of_irreducible hi hfa]
    exact dvd_mul_right _ _
  · rintro ⟨g, rfl⟩
    simp [hfa]

中文:
定理 _root_.Irreducible.dvd_iff_aeval_eq_zero
  结论: [Nontrivial B] {p q : A[X]} (hi : Irreducible p)
  证明: by
  refine ⟨fun hga => dvd_trans ?_ (minpoly.dvd A b hga), ?_⟩
  · rw [← minpoly.eq_of_irreducible hi hfa]
    exact dvd_mul_right _ _
  · rintro ⟨g, rfl⟩
    simp [hfa]

Depends on / 依赖: dvd_mul_right, dvd_trans, eq_of_irreducible, minpoly, minpoly.dvd, minpoly.eq_of_irreducible
-/
theorem _root_.Irreducible.dvd_iff_aeval_eq_zero [Nontrivial B] {p q : A[X]} (hi : Irreducible p)
    {b : B} (hfa : p.aeval b = 0) : q.aeval b = 0 ↔ p ∣ q := by
  refine ⟨fun hga => dvd_trans ?_ (minpoly.dvd A b hga), ?_⟩
  · rw [← minpoly.eq_of_irreducible hi hfa]
    exact dvd_mul_right _ _
  · rintro ⟨g, rfl⟩
    simp [hfa]

/--
theorem `add_algebraMap` / 定理 `add_algebraMap`

English:
theorem add_algebraMap
  statement: {B : Type*} [CommRing B] [Algebra A B] (x : B)
  proof: by
  by_cases hx : IsIntegral A x
  · refine (minpoly.unique _ _ ((minpoly.monic hx).comp_X_sub_C _) ?_ fun q qmo hq => ?_).symm
    · simp [aeval_comp]
    · have : (Polynomial.aeval x) (q.comp (X + C a)) = 0 := by simpa [aeval_comp] using hq
      have H := minpoly.min A x (qmo.comp_X_add_C _) thi

中文:
定理 add_algebraMap
  结论: {B : 类型} [CommRing B] [Algebra A B] (x : B)
  证明: by
  by_cases hx : IsIntegral A x
  · refine (minpoly.unique _ _ ((minpoly.monic hx).comp_X_sub_C _) ?_ fun q qmo hq => ?_).symm
    · simp [aeval_comp]
    · have : (Polynomial.aeval x) (q.comp (X + C a)) = 0 := by simpa [aeval_comp] using hq
      have H := minpoly.min A x (qmo.comp_X_add_C _) thi

Depends on / 依赖: IsIntegral, Polynomial, Polynomial.aeval, aeval_comp, comp_X_add_C, comp_X_sub_C, degree_eq_natDegree, minpoly, minpoly.min, minpoly.monic, minpoly.ne_zero, minpoly.unique, mul_one, natDegree_X_sub_C, natDegree_comp, ne_zero, q.comp, qmo.comp_X_add_C, qmo.ne_zero, unique
-/
theorem add_algebraMap {B : Type*} [CommRing B] [Algebra A B] (x : B)
    (a : A) : minpoly A (x + algebraMap A B a) = (minpoly A x).comp (X - C a) := by
  by_cases hx : IsIntegral A x
  · refine (minpoly.unique _ _ ((minpoly.monic hx).comp_X_sub_C _) ?_ fun q qmo hq => ?_).symm
    · simp [aeval_comp]
    · have : (Polynomial.aeval x) (q.comp (X + C a)) = 0 := by simpa [aeval_comp] using hq
      have H := minpoly.min A x (qmo.comp_X_add_C _) this
      rw [degree_eq_natDegree qmo.ne_zero]; rw [degree_eq_natDegree ((minpoly.monic hx).comp_X_sub_C _).ne_zero]; rw [natDegree_comp]; rw [natDegree_X_sub_C]; rw [mul_one]
      rwa [degree_eq_natDegree (minpoly.ne_zero hx),
        degree_eq_natDegree (qmo.comp_X_add_C _).ne_zero, natDegree_comp,
        natDegree_X_add_C, mul_one] at H
  · rw [minpoly.eq_zero hx, minpoly.eq_zero, zero_comp]
    refine fun h => hx ?_
    simpa only [add_sub_cancel_right] using IsIntegral.sub h (isIntegral_algebraMap (x := a))

/--
theorem `sub_algebraMap` / 定理 `sub_algebraMap`

English:
theorem sub_algebraMap
  statement: {B : Type*} [CommRing B] [Algebra A B] (x : B)
  proof: by
  simpa [sub_eq_add_neg] using add_algebraMap x (-a)

中文:
定理 sub_algebraMap
  结论: {B : 类型} [CommRing B] [Algebra A B] (x : B)
  证明: by
  simpa [sub_eq_add_neg] using add_algebraMap x (-a)

Depends on / 依赖: add_algebraMap, sub_eq_add_neg
-/
theorem sub_algebraMap {B : Type*} [CommRing B] [Algebra A B] (x : B)
    (a : A) : minpoly A (x - algebraMap A B a) = (minpoly A x).comp (X + C a) := by
  simpa [sub_eq_add_neg] using add_algebraMap x (-a)

/--
theorem `neg` / 定理 `neg`

English:
theorem neg
  given: {B : Type*} [Ring B] [Algebra A B] (x : B)
  proof: by
  by_cases hx : IsIntegral A x
  · refine (minpoly.unique _ _ ((minpoly.monic hx).neg_one_pow_natDegree_mul_comp_neg_X)
        ?_ fun q qmo hq => ?_).symm
    · simp [aeval_comp]
    · have : (Polynomial.aeval x) ((-1) ^ q.natDegree * q.comp (-X)) = 0 := by
        simpa [aeval_comp] using hq
  

中文:
定理 neg
  条件: {B : 类型} [Ring B] [Algebra A B] (x : B)
  证明: by
  by_cases hx : IsIntegral A x
  · refine (minpoly.unique _ _ ((minpoly.monic hx).neg_one_pow_natDegree_mul_comp_neg_X)
        ?_ fun q qmo hq => ?_).symm
    · simp [aeval_comp]
    · have : (Polynomial.aeval x) ((-1) ^ q.natDegree * q.comp (-X)) = 0 := by
        simpa [aeval_comp] using hq
  

Depends on / 依赖: IsIntegral, IsIntegral.neg_iff.not.mpr, Polynomial, Polynomial.aeval, aeval_comp, eq_zero, minpoly, minpoly.eq_zero, minpoly.min, minpoly.monic, minpoly.unique, mul_zero, natDegree, natDegree_zero, neg_iff, neg_one_pow_natDegree_mul_comp_neg_X, pow_zero, q.comp, q.natDegree, qmo.neg_one_pow_natDegree_mul_comp_neg_X
-/
theorem neg {B : Type*} [Ring B] [Algebra A B] (x : B) :
    minpoly A (-x) = (-1) ^ (natDegree (minpoly A x)) * (minpoly A x).comp (-X) := by
  by_cases hx : IsIntegral A x
  · refine (minpoly.unique _ _ ((minpoly.monic hx).neg_one_pow_natDegree_mul_comp_neg_X)
        ?_ fun q qmo hq => ?_).symm
    · simp [aeval_comp]
    · have : (Polynomial.aeval x) ((-1) ^ q.natDegree * q.comp (-X)) = 0 := by
        simpa [aeval_comp] using hq
      have H := minpoly.min A x qmo.neg_one_pow_natDegree_mul_comp_neg_X this
      simp_all
  · rw [minpoly.eq_zero hx, minpoly.eq_zero, zero_comp]
    · simp only [natDegree_zero, pow_zero, mul_zero]
    · exact IsIntegral.neg_iff.not.mpr hx

/--
theorem `map_eq_of_equiv_equiv` / 定理 `map_eq_of_equiv_equiv`

English:
theorem map_eq_of_equiv_equiv
  statement: {R S T : Type*} [CommRing R] [IsDomain R] [Ring S] [Ring T]
  proof: by
  refine minpoly.eq_of_irreducible_of_monic ?_ ?_ ?_
  · rw [← mapEquiv_apply, MulEquiv.irreducible_iff]
    exact minpoly.irreducible (Algebra.IsIntegral.isIntegral x)
  · simpa using (map_aeval_eq_aeval_map hcomp (minpoly R x) x).symm
  · exact (monic (Algebra.IsIntegral.isIntegral x)).map _

中文:
定理 map_eq_of_equiv_equiv
  结论: {R S T : 类型} [CommRing R] [IsDomain R] [Ring S] [Ring T]
  证明: by
  refine minpoly.eq_of_irreducible_of_monic ?_ ?_ ?_
  · rw [← mapEquiv_apply, MulEquiv.irreducible_iff]
    exact minpoly.irreducible (Algebra.IsIntegral.isIntegral x)
  · simpa using (map_aeval_eq_aeval_map hcomp (minpoly R x) x).symm
  · exact (monic (Algebra.IsIntegral.isIntegral x)).map _

Depends on / 依赖: Algebra, Algebra.IsIntegral.isIntegral, IsIntegral, MulEquiv, MulEquiv.irreducible_iff, eq_of_irreducible_of_monic, irreducible, irreducible_iff, isIntegral, mapEquiv_apply, map_aeval_eq_aeval_map, minpoly, minpoly.eq_of_irreducible_of_monic, minpoly.irreducible
-/
theorem map_eq_of_equiv_equiv {R S T : Type*} [CommRing R] [IsDomain R] [Ring S] [Ring T]
    [IsDomain S] [IsDomain T] [Algebra R S] [Algebra A T] [Algebra.IsIntegral R S]
    {f : R ≃+* A} {g : S ≃+* T}
    (hcomp : (algebraMap A T).comp f = (g : S ->+* T).comp (algebraMap R S)) (x : S) :
    map f (minpoly R x) = minpoly A (g x) := by
  refine minpoly.eq_of_irreducible_of_monic ?_ ?_ ?_
  · rw [← mapEquiv_apply, MulEquiv.irreducible_iff]
    exact minpoly.irreducible (Algebra.IsIntegral.isIntegral x)
  · simpa using (map_aeval_eq_aeval_map hcomp (minpoly R x) x).symm
  · exact (monic (Algebra.IsIntegral.isIntegral x)).map _

section AlgHomFintype

open scoped Classical in
/-- A technical finiteness result. -/
@[instance_reducible]
/--
Definition of `Fintype.subtypeProd` / `Fintype.subtypeProd` 的定义

English:
definition Fintype.subtypeProd
  signature: {E : Type*} {X : Set E} (hX : X.Finite) {L : Type*}
  body: @Pi.instFintype _ _ _ (Finite.fintype hX) _

中文:
定义 Fintype.subtypeProd
  签名: {E : 类型} {X : Set E} (hX : X.Finite) {L : 类型}
  定义体: @Pi.instFintype _ _ _ (Finite.fintype hX) _

Depends on / 依赖: Finite, Finite.fintype, Pi.instFintype, fintype, instFintype
-/
noncomputable def Fintype.subtypeProd {E : Type*} {X : Set E} (hX : X.Finite) {L : Type*}
    (F : E -> Multiset L) : Fintype (forall x : X, { l : L // l in F x }) :=
  @Pi.instFintype _ _ _ (Finite.fintype hX) _

variable (F E K : Type*) [Field F] [Ring E] [CommRing K] [IsDomain K] [Algebra F E] [Algebra F K]
  [FiniteDimensional F E]

/--
Definition of `rootsOfMinPolyPiType` / `rootsOfMinPolyPiType` 的定义

English:
definition rootsOfMinPolyPiType
  signature: (φ : E ->ₐ[F] K)
  body: ⟨φ x, by
    rw [mem_roots_map (minpoly.ne_zero_of_finite F x.val)]; rw [← aeval_def]; rw [aeval_algHom_apply]; rw [minpoly.aeval]; rw [map_zero]⟩

中文:
定义 rootsOfMinPolyPiType
  签名: (φ : E ->ₐ[F] K)
  定义体: ⟨φ x, by
    rw [mem_roots_map (minpoly.ne_zero_of_finite F x.val)]; rw [← aeval_def]; rw [aeval_algHom_apply]; rw [minpoly.aeval]; rw [map_zero]⟩

Depends on / 依赖: aeval_algHom_apply, aeval_def, map_zero, mem_roots_map, minpoly, minpoly.aeval, minpoly.ne_zero_of_finite, ne_zero_of_finite, x.val
-/
def rootsOfMinPolyPiType (φ : E ->ₐ[F] K)
    (x : range (Module.finBasis F E : _ -> E)) :
    { l : K // l in (minpoly F x.1).aroots K } :=
  ⟨φ x, by
    rw [mem_roots_map (minpoly.ne_zero_of_finite F x.val)]; rw [← aeval_def]; rw [aeval_algHom_apply]; rw [minpoly.aeval]; rw [map_zero]⟩

/--
theorem `aux_inj_roots_of_min_poly` / 定理 `aux_inj_roots_of_min_poly`

English:
theorem aux_inj_roots_of_min_poly
  statement: Injective (rootsOfMinPolyPiType F E K)
  proof: by
  intro f g h
  -- needs explicit coercion on the RHS
  suffices (f : E ->ₗ[F] K) = (g : E ->ₗ[F] K) by rwa [DFunLike.ext'_iff] at this ⊢
  rw [funext_iff] at h
  exact LinearMap.ext_on (Module.finBasis F E).span_eq fun e he =>
    Subtype.ext_iff.mp (h ⟨e, he⟩)

中文:
定理 aux_inj_roots_of_min_poly
  结论: Injective (rootsOfMinPolyPiType F E K)
  证明: by
  intro f g h
  -- needs explicit coercion on the RHS
  suffices (f : E ->ₗ[F] K) = (g : E ->ₗ[F] K) by rwa [DFunLike.ext'_iff] at this ⊢
  rw [funext_iff] at h
  exact LinearMap.ext_on (Module.finBasis F E).span_eq fun e he =>
    Subtype.ext_iff.mp (h ⟨e, he⟩)
-/
theorem aux_inj_roots_of_min_poly : Injective (rootsOfMinPolyPiType F E K) := by
  intro f g h
  -- needs explicit coercion on the RHS
  suffices (f : E ->ₗ[F] K) = (g : E ->ₗ[F] K) by rwa [DFunLike.ext'_iff] at this ⊢
  rw [funext_iff] at h
  exact LinearMap.ext_on (Module.finBasis F E).span_eq fun e he =>
    Subtype.ext_iff.mp (h ⟨e, he⟩)

/--
Instance `AlgHom.fintype` / 实例 `AlgHom.fintype`

English:
instance AlgHom.fintype
  signature: : Fintype (E ->ₐ[F] K)
  body: @Fintype.ofInjective _ _
    (Fintype.subtypeProd (finite_range (Module.finBasis F E)) fun e =>
      (minpoly F e).aroots K)
    _ (aux_inj_roots_of_min_poly F E K)

中文:
实例 AlgHom.fintype
  签名: : Fintype (E ->ₐ[F] K)
  定义体: @Fintype.ofInjective _ _
    (Fintype.subtypeProd (finite_range (Module.finBasis F E)) fun e =>
      (minpoly F e).aroots K)
    _ (aux_inj_roots_of_min_poly F E K)

Depends on / 依赖: Fintype, Fintype.ofInjective, Fintype.subtypeProd, Module, Module.finBasis, aroots, aux_inj_roots_of_min_poly, finBasis, finite_range, minpoly, ofInjective, subtypeProd
-/
noncomputable instance AlgHom.fintype : Fintype (E ->ₐ[F] K) :=
  @Fintype.ofInjective _ _
    (Fintype.subtypeProd (finite_range (Module.finBasis F E)) fun e =>
      (minpoly F e).aroots K)
    _ (aux_inj_roots_of_min_poly F E K)

end AlgHomFintype

variable (B) [Nontrivial B]

/--
theorem `eq_X_sub_C` / 定理 `eq_X_sub_C`

English:
theorem eq_X_sub_C
  given: (a : A)
  statement: minpoly A (algebraMap A B a) = X - C a
  proof: eq_X_sub_C_of_algebraMap_inj a (algebraMap A B).injective

中文:
定理 eq_X_sub_C
  条件: (a : A)
  结论: minpoly A (algebraMap A B a) = X - C a
  证明: eq_X_sub_C_of_algebraMap_inj a (algebraMap A B).injective

Depends on / 依赖: algebraMap, eq_X_sub_C_of_algebraMap_inj, injective
-/
theorem eq_X_sub_C (a : A) : minpoly A (algebraMap A B a) = X - C a :=
  eq_X_sub_C_of_algebraMap_inj a (algebraMap A B).injective

/--
theorem `eq_X_sub_C'` / 定理 `eq_X_sub_C'`

English:
theorem eq_X_sub_C'
  given: (a : A)
  statement: minpoly A a = X - C a
  proof: eq_X_sub_C A a

中文:
定理 eq_X_sub_C'
  条件: (a : A)
  结论: minpoly A a = X - C a
  证明: eq_X_sub_C A a

Depends on / 依赖: eq_X_sub_C
-/
theorem eq_X_sub_C' (a : A) : minpoly A a = X - C a :=
  eq_X_sub_C A a

variable (A)

/-- The minimal polynomial of `0` is `X`. -/
@[simp]
/--
theorem `zero` / 定理 `zero`

English:
theorem zero
  statement: minpoly A (0 : B) = X
  proof: by
  simpa only [add_zero, C_0, sub_eq_add_neg, neg_zero, map_zero] using eq_X_sub_C B (0 : A)

中文:
定理 zero
  结论: minpoly A (0 : B) = X
  证明: by
  simpa only [add_zero, C_0, sub_eq_add_neg, neg_zero, map_zero] using eq_X_sub_C B (0 : A)

Depends on / 依赖: add_zero, eq_X_sub_C, map_zero, neg_zero, sub_eq_add_neg
-/
theorem zero : minpoly A (0 : B) = X := by
  simpa only [add_zero, C_0, sub_eq_add_neg, neg_zero, map_zero] using eq_X_sub_C B (0 : A)

/-- The minimal polynomial of `1` is `X - 1`. -/
@[simp]
/--
theorem `one` / 定理 `one`

English:
theorem one
  statement: minpoly A (1 : B) = X - 1
  proof: by
  simpa only [map_one, C_1, sub_eq_add_neg] using eq_X_sub_C B (1 : A)

中文:
定理 one
  结论: minpoly A (1 : B) = X - 1
  证明: by
  simpa only [map_one, C_1, sub_eq_add_neg] using eq_X_sub_C B (1 : A)

Depends on / 依赖: eq_X_sub_C, map_one, sub_eq_add_neg
-/
theorem one : minpoly A (1 : B) = X - 1 := by
  simpa only [map_one, C_1, sub_eq_add_neg] using eq_X_sub_C B (1 : A)

end Ring

section IsDomain

variable [Ring B] [IsDomain B] [Algebra A B]
variable {A} {x : B}

/--
theorem `prime` / 定理 `prime`

English:
theorem prime
  given: (hx : IsIntegral A x)
  statement: Prime (minpoly A x)
  proof: by
  refine ⟨minpoly.ne_zero hx, not_isUnit A x, ?_⟩
  rintro p q ⟨d, h⟩
  have : Polynomial.aeval x (p * q) = 0 := by simp [h, aeval A x]
  replace : Polynomial.aeval x p = 0 ∨ Polynomial.aeval x q = 0 := by simpa
  exact Or.imp (dvd A x) (dvd A x) this

中文:
定理 prime
  条件: (hx : Is整数egral A x)
  结论: Prime (minpoly A x)
  证明: by
  refine ⟨minpoly.ne_zero hx, not_isUnit A x, ?_⟩
  rintro p q ⟨d, h⟩
  have : Polynomial.aeval x (p * q) = 0 := by simp [h, aeval A x]
  replace : Polynomial.aeval x p = 0 ∨ Polynomial.aeval x q = 0 := by simpa
  exact Or.imp (dvd A x) (dvd A x) this

Depends on / 依赖: Or.imp, Polynomial, Polynomial.aeval, minpoly, minpoly.ne_zero, ne_zero, not_isUnit, replace
-/
theorem prime (hx : IsIntegral A x) : Prime (minpoly A x) := by
  refine ⟨minpoly.ne_zero hx, not_isUnit A x, ?_⟩
  rintro p q ⟨d, h⟩
  have : Polynomial.aeval x (p * q) = 0 := by simp [h, aeval A x]
  replace : Polynomial.aeval x p = 0 ∨ Polynomial.aeval x q = 0 := by simpa
  exact Or.imp (dvd A x) (dvd A x) this

/--
theorem `root` / 定理 `root`

English:
theorem root
  given: {x : B} (hx : IsIntegral A x) {y : A} (h : IsRoot (minpoly A x) y)
  proof: by
  have key : minpoly A x = X - C y := eq_of_monic_of_associated (monic hx) (monic_X_sub_C y)
    (associated_of_dvd_dvd ((irreducible_X_sub_C y).dvd_symm (irreducible hx) (dvd_iff_isRoot.2 h))
      (dvd_iff_isRoot.2 h))
  have := aeval A x
  rwa [key, map_sub, aeval_X, aeval_C, sub_eq_zero, eq_c

中文:
定理 root
  条件: {x : B} (hx : Is整数egral A x) {y : A} (h : IsRoot (minpoly A x) y)
  证明: by
  have key : minpoly A x = X - C y := eq_of_monic_of_associated (monic hx) (monic_X_sub_C y)
    (associated_of_dvd_dvd ((irreducible_X_sub_C y).dvd_symm (irreducible hx) (dvd_iff_isRoot.2 h))
      (dvd_iff_isRoot.2 h))
  have := aeval A x
  rwa [key, map_sub, aeval_X, aeval_C, sub_eq_zero, eq_c

Depends on / 依赖: aeval_C, aeval_X, associated_of_dvd_dvd, dvd_iff_isRoot, dvd_symm, eq_comm, eq_of_monic_of_associated, irreducible, irreducible_X_sub_C, map_sub, minpoly, monic_X_sub_C, sub_eq_zero
-/
theorem root {x : B} (hx : IsIntegral A x) {y : A} (h : IsRoot (minpoly A x) y) :
    algebraMap A B y = x := by
  have key : minpoly A x = X - C y := eq_of_monic_of_associated (monic hx) (monic_X_sub_C y)
    (associated_of_dvd_dvd ((irreducible_X_sub_C y).dvd_symm (irreducible hx) (dvd_iff_isRoot.2 h))
      (dvd_iff_isRoot.2 h))
  have := aeval A x
  rwa [key, map_sub, aeval_X, aeval_C, sub_eq_zero, eq_comm] at this

/-- The constant coefficient of the minimal polynomial of `x` is `0` if and only if `x = 0`. -/
@[simp]
/--
theorem `coeff_zero_eq_zero` / 定理 `coeff_zero_eq_zero`

English:
theorem coeff_zero_eq_zero
  given: (hx : IsIntegral A x)
  statement: coeff (minpoly A x) 0 = 0 ↔ x = 0
  proof: by
  constructor
  · intro h
    have zero_root := zero_isRoot_of_coeff_zero_eq_zero h
    rw [← root hx zero_root]
    exact map_zero _
  · rintro rfl
    simp

中文:
定理 coeff_zero_eq_zero
  条件: (hx : Is整数egral A x)
  结论: coeff (minpoly A x) 0 = 0 ↔ x = 0
  证明: by
  constructor
  · intro h
    have zero_root := zero_isRoot_of_coeff_zero_eq_zero h
    rw [← root hx zero_root]
    exact map_zero _
  · rintro rfl
    simp

Depends on / 依赖: map_zero, zero_isRoot_of_coeff_zero_eq_zero, zero_root
-/
theorem coeff_zero_eq_zero (hx : IsIntegral A x) : coeff (minpoly A x) 0 = 0 ↔ x = 0 := by
  constructor
  · intro h
    have zero_root := zero_isRoot_of_coeff_zero_eq_zero h
    rw [← root hx zero_root]
    exact map_zero _
  · rintro rfl
    simp

/--
theorem `coeff_zero_ne_zero` / 定理 `coeff_zero_ne_zero`

English:
theorem coeff_zero_ne_zero
  given: (hx : IsIntegral A x) (h : x != 0)
  statement: coeff (minpoly A x) 0 != 0
  proof: by
  contrapose h
  simpa only [hx, coeff_zero_eq_zero] using h

中文:
定理 coeff_zero_ne_zero
  条件: (hx : Is整数egral A x) (h : x != 0)
  结论: coeff (minpoly A x) 0 != 0
  证明: by
  contrapose h
  simpa only [hx, coeff_zero_eq_zero] using h

Depends on / 依赖: coeff_zero_eq_zero, contrapose
-/
theorem coeff_zero_ne_zero (hx : IsIntegral A x) (h : x != 0) : coeff (minpoly A x) 0 != 0 := by
  contrapose h
  simpa only [hx, coeff_zero_eq_zero] using h

end IsDomain

end minpoly

section AlgHom

variable {K L} [Field K] [CommRing L] [IsDomain L] [Algebra K L]

/--
lemma `minpoly_algEquiv_toLinearMap` / 引理 `minpoly_algEquiv_toLinearMap`

English:
lemma minpoly_algEquiv_toLinearMap
  given: (σ : L ≃ₐ[K] L) (hσ : IsOfFinOrder σ)
  proof: by
  refine (minpoly.unique _ _ (monic_X_pow_sub_C _ hσ.orderOf_pos.ne.symm) ?_ ?_).symm
  · simp [← AlgEquiv.pow_toLinearMap, pow_orderOf_eq_one]
  · intro q hq hs
    rw [degree_eq_natDegree hq.ne_zero]; rw [degree_X_pow_sub_C hσ.orderOf_pos]; rw [Nat.cast_le]; rw [← not_lt]
    intro H
    rw [ae

中文:
引理 minpoly_algEquiv_toLinearMap
  条件: (σ : L ≃ₐ[K] L) (hσ : IsOfFinOrder σ)
  证明: by
  refine (minpoly.unique _ _ (monic_X_pow_sub_C _ hσ.orderOf_pos.ne.symm) ?_ ?_).symm
  · simp [← AlgEquiv.pow_toLinearMap, pow_orderOf_eq_one]
  · intro q hq hs
    rw [degree_eq_natDegree hq.ne_zero]; rw [degree_X_pow_sub_C hσ.orderOf_pos]; rw [Nat.cast_le]; rw [← not_lt]
    intro H
    rw [ae

Depends on / 依赖: AlgEquiv, AlgEquiv.pow_toLinearMap, Fin.sum_univ_eq_sum_range, Fintype, Fintype.linearIndependent_iff.mp, Nat.cast_le, aeval_eq_sum_range, cast_le, degree_X_pow_sub_C, degree_eq_natDegree, hq.ne_zero, linearIndependent_algHom_toLinearMap, linearIndependent_iff, minpoly, minpoly.unique, monic_X_pow_sub_C, ne_zero, not_lt, orderOf_pos, orderOf_pos.ne.symm
-/
lemma minpoly_algEquiv_toLinearMap (σ : L ≃ₐ[K] L) (hσ : IsOfFinOrder σ) :
    minpoly K σ.toLinearMap = X ^ (orderOf σ) - C 1 := by
  refine (minpoly.unique _ _ (monic_X_pow_sub_C _ hσ.orderOf_pos.ne.symm) ?_ ?_).symm
  · simp [← AlgEquiv.pow_toLinearMap, pow_orderOf_eq_one]
  · intro q hq hs
    rw [degree_eq_natDegree hq.ne_zero]; rw [degree_X_pow_sub_C hσ.orderOf_pos]; rw [Nat.cast_le]; rw [← not_lt]
    intro H
    rw [aeval_eq_sum_range' H]; rw [← Fin.sum_univ_eq_sum_range] at hs
    simp_rw [← AlgEquiv.pow_toLinearMap] at hs
    apply hq.ne_zero
    simpa using Fintype.linearIndependent_iff.mp
      (((linearIndependent_algHom_toLinearMap' K L L).comp _ AlgEquiv.coe_toAlgHom_injective).comp _
        (Subtype.val_injective.comp ((finEquivPowers hσ).injective)))
      (q.coeff ∘ (↑)) hs ⟨_, H⟩

/--
lemma `minpoly_algHom_toLinearMap` / 引理 `minpoly_algHom_toLinearMap`

English:
lemma minpoly_algHom_toLinearMap
  given: (σ : L ->ₐ[K] L) (hσ : IsOfFinOrder σ)
  proof: by
  have : orderOf σ = orderOf (AlgEquiv.algHomUnitsEquiv _ _ hσ.unit) := by
    rw [← MonoidHom.coe_coe]; rw [orderOf_injective]; rw [← orderOf_units]; rw [IsOfFinOrder.val_unit]
    exact (AlgEquiv.algHomUnitsEquiv K L).injective
  rw [this]; rw [← minpoly_algEquiv_toLinearMap]
  · apply congr_ar

中文:
引理 minpoly_algHom_toLinearMap
  条件: (σ : L ->ₐ[K] L) (hσ : IsOfFinOrder σ)
  证明: by
  have : orderOf σ = orderOf (AlgEquiv.algHomUnitsEquiv _ _ hσ.unit) := by
    rw [← MonoidHom.coe_coe]; rw [orderOf_injective]; rw [← orderOf_units]; rw [IsOfFinOrder.val_unit]
    exact (AlgEquiv.algHomUnitsEquiv K L).injective
  rw [this]; rw [← minpoly_algEquiv_toLinearMap]
  · apply congr_ar

Depends on / 依赖: AlgEquiv, AlgEquiv.algHomUnitsEquiv, IsOfFinOrder, IsOfFinOrder.val_unit, MonoidHom, MonoidHom.coe_coe, algHomUnitsEquiv, coe_coe, congr_arg, injective, minpoly_algEquiv_toLinearMap, orderOf, orderOf_injective, orderOf_pos_iff, orderOf_units, val_unit
-/
lemma minpoly_algHom_toLinearMap (σ : L ->ₐ[K] L) (hσ : IsOfFinOrder σ) :
    minpoly K σ.toLinearMap = X ^ (orderOf σ) - C 1 := by
  have : orderOf σ = orderOf (AlgEquiv.algHomUnitsEquiv _ _ hσ.unit) := by
    rw [← MonoidHom.coe_coe]; rw [orderOf_injective]; rw [← orderOf_units]; rw [IsOfFinOrder.val_unit]
    exact (AlgEquiv.algHomUnitsEquiv K L).injective
  rw [this]; rw [← minpoly_algEquiv_toLinearMap]
  · apply congr_arg
    ext
    simp
  · rwa [← orderOf_pos_iff, ← this, orderOf_pos_iff]

end AlgHom
