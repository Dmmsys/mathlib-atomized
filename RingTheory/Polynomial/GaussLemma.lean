/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.FieldTheory.SplittingField.Construction
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Polynomial.Content

/-!
# Gauss's Lemma

Gauss's Lemma is one of a few results pertaining to irreducibility of primitive polynomials.

## Main Results

- `IsIntegrallyClosed.eq_map_mul_C_of_dvd`: if `R` is integrally closed, `K = Frac(R)` and
  `g : K[X]` divides a monic polynomial with coefficients in `R`, then `g * (C g.leadingCoeff⁻¹)`
  has coefficients in `R`
- `Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map`:
  A monic polynomial over an integrally closed domain is irreducible iff it is irreducible in a
  fraction field
- `isIntegrallyClosed_iff'`:
  Integrally closed domains are precisely the domains for in which Gauss's lemma holds
  for monic polynomials
- `Polynomial.IsPrimitive.irreducible_iff_irreducible_map_fraction_map`:
  A primitive polynomial over a GCD domain is irreducible iff it is irreducible in a fraction field
- `Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast`:
  A primitive polynomial over `ℤ` is irreducible iff it is irreducible over `ℚ`.
- `Polynomial.IsPrimitive.dvd_iff_fraction_map_dvd_fraction_map`:
  Two primitive polynomials over a GCD domain divide each other iff they do in a fraction field.
- `Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast`:
  Two primitive polynomials over `ℤ` divide each other if they do in `ℚ`.

-/

public section


open scoped nonZeroDivisors Polynomial

variable {R : Type*} [CommRing R]

section IsIntegrallyClosed

open Polynomial

open integralClosure

open IsIntegrallyClosed

variable (K : Type*) [Field K] [Algebra R K]

/--
theorem `integralClosure.mem_lifts_of_monic_of_dvd_map` / 定理 `integralClosure.mem_lifts_of_monic_of_dvd_map`

English:
theorem integralClosure.mem_lifts_of_monic_of_dvd_map
  statement: {f : R[X]} (hf : f.Monic) {g : K[X]}
  proof: by
  have := (SplittingField.splits g).mem_lift_of_roots_mem_range (hg.map _)
    (algebraMap (integralClosure R g.SplittingField) g.SplittingField)
     fun a ha =>
(SetLike.ext_iff.mp (integralClosure R g.SplittingField).range_algebraMap _).mpr
        roots_mem_integralClosure hf ?_
  · rw [lifts

中文:
定理 integralClosure.mem_lifts_of_monic_of_dvd_map
  结论: {f : R[X]} (hf : f.Monic) {g : K[X]}
  证明: by
  have := (SplittingField.splits g).mem_lift_of_roots_mem_range (hg.map _)
    (algebraMap (integralClosure R g.SplittingField) g.SplittingField)
     fun a ha =>
(SetLike.ext_iff.mp (integralClosure R g.SplittingField).range_algebraMap _).mpr
        roots_mem_integralClosure hf ?_
  · rw [lifts

Depends on / 依赖: RingHom, RingHom.coe_range, SetLike, SetLike.ext_iff.mp, SetLike.mem_coe.m, SplittingField, SplittingField.splits, Subalgebra, Subalgebra.range_algebraMap, algebraMap, coe_range, ext_iff, g.SplittingField, hg.map, integralClosure, lifts_iff_coeff_lifts, mem_coe, mem_lift_of_roots_mem_range, range_algebraMap, roots_mem_integralClosure
-/
theorem integralClosure.mem_lifts_of_monic_of_dvd_map {f : R[X]} (hf : f.Monic) {g : K[X]}
    (hg : g.Monic) (hd : g ∣ f.map (algebraMap R K)) :
    g in lifts (algebraMap (integralClosure R K) K) := by
  have := (SplittingField.splits g).mem_lift_of_roots_mem_range (hg.map _)
    (algebraMap (integralClosure R g.SplittingField) g.SplittingField)
     fun a ha =>
(SetLike.ext_iff.mp (integralClosure R g.SplittingField).range_algebraMap _).mpr
        roots_mem_integralClosure hf ?_
  · rw [lifts_iff_coeff_lifts, ← RingHom.coe_range, Subalgebra.range_algebraMap] at this
    refine (lifts_iff_coeff_lifts _).2 fun n => ?_
    rw [← RingHom.coe_range]; rw [Subalgebra.range_algebraMap]
    obtain ⟨p, hp, he⟩ := SetLike.mem_coe.mp (this n); use p, hp
    rw [IsScalarTower.algebraMap_eq R K]; rw [coeff_map]; rw [← eval₂_map]; rw [eval₂_at_apply] at he
    rw [eval₂_eq_eval_map]; apply (injective_iff_map_eq_zero _).1 _ _ he
    apply RingHom.injective
  rw [aroots_def]; rw [IsScalarTower.algebraMap_eq R K _]; rw [← map_map]
  refine Multiset.mem_of_le (roots.le_of_dvd ((hf.map _).map _).ne_zero ?_) ha
  exact map_dvd (algebraMap K g.SplittingField) hd

variable [IsFractionRing R K]

/--
theorem `IsIntegrallyClosed.eq_map_mul_C_of_dvd` / 定理 `IsIntegrallyClosed.eq_map_mul_C_of_dvd`

English:
theorem IsIntegrallyClosed.eq_map_mul_C_of_dvd
  statement: [IsIntegrallyClosed R] {f : R[X]} (hf : f.Monic)
  proof: by
  have g_ne_0 : g != 0 := ne_zero_of_dvd_ne_zero (Monic.ne_zero <| hf.map (algebraMap R K)) hg
  suffices lem : exists g' : R[X], g'.map (algebraMap R K) = g * C g.leadingCoeff⁻¹ by
    obtain ⟨g', hg'⟩ := lem
    use g'
    rw [hg']; rw [mul_assoc]; rw [← C_mul]; rw [inv_mul_cancel₀ (leadingCoef

中文:
定理 是整闭.eq_map_mul_C_of_dvd
  结论: [是整闭 R] {f : R[X]} (hf : f.Monic)
  证明: by
  have g_ne_0 : g != 0 := ne_zero_of_dvd_ne_zero (Monic.ne_zero <| hf.map (algebraMap R K)) hg
  suffices lem : exists g' : R[X], g'.map (algebraMap R K) = g * C g.leadingCoeff⁻¹ by
    obtain ⟨g', hg'⟩ := lem
    use g'
    rw [hg']; rw [mul_assoc]; rw [← C_mul]; rw [inv_mul_cancel₀ (leadingCoef

Depends on / 依赖: Associated, Associated.dvd_iff_dvd_left, C_mul, Monic.ne_zero, algebraMap, associat, dvd_iff_dvd_left, f.map, g.leadingCoeff, g_mul_dvd, g_ne_0, hf.map, leadingCoeff, leadingCoeff_ne_zero, leadingCoeff_ne_zero.mpr, mul_assoc, mul_one, ne_zero, ne_zero_of_dvd_ne_zero
-/
theorem IsIntegrallyClosed.eq_map_mul_C_of_dvd [IsIntegrallyClosed R] {f : R[X]} (hf : f.Monic)
    {g : K[X]} (hg : g ∣ f.map (algebraMap R K)) :
    exists g' : R[X], g'.map (algebraMap R K) * (C <| leadingCoeff g) = g := by
  have g_ne_0 : g != 0 := ne_zero_of_dvd_ne_zero (Monic.ne_zero <| hf.map (algebraMap R K)) hg
  suffices lem : exists g' : R[X], g'.map (algebraMap R K) = g * C g.leadingCoeff⁻¹ by
    obtain ⟨g', hg'⟩ := lem
    use g'
    rw [hg']; rw [mul_assoc]; rw [← C_mul]; rw [inv_mul_cancel₀ (leadingCoeff_ne_zero.mpr g_ne_0)]; rw [C_1]; rw [mul_one]
  have g_mul_dvd : g * C g.leadingCoeff⁻¹ ∣ f.map (algebraMap R K) := by
    rwa [Associated.dvd_iff_dvd_left (show Associated (g * C g.leadingCoeff⁻¹) g from _)]
    rw [associated_mul_isUnit_left_iff]
    exact isUnit_C.mpr (inv_ne_zero <| leadingCoeff_ne_zero.mpr g_ne_0).isUnit
  let algeq :=
    (Subalgebra.equivOfEq _ _ <| integralClosure_eq_bot R _).trans
      (Algebra.botEquivOfInjective <| IsFractionRing.injective R <| K)
  have :
    (algebraMap R _).comp algeq.toAlgHom.toRingHom = (integralClosure R _).toSubring.subtype := by
    ext x; (conv_rhs => rw [← algeq.symm_apply_apply x]); rfl
  have H :=
    (mem_lifts _).1
      (integralClosure.mem_lifts_of_monic_of_dvd_map K hf (monic_mul_leadingCoeff_inv g_ne_0)
        g_mul_dvd)
  refine ⟨map algeq.toAlgHom.toRingHom ?_, ?_⟩
  · use! Classical.choose H
  · rw [map_map, this]
    exact Classical.choose_spec H

end IsIntegrallyClosed

namespace Polynomial

section

variable {S : Type*} [CommRing S] [IsDomain S]
variable {φ : R ->+* S} (hinj : Function.Injective φ) {f : R[X]} (hf : f.IsPrimitive)
include hinj hf

/--
theorem `IsPrimitive.isUnit_iff_isUnit_map_of_injective` / 定理 `IsPrimitive.isUnit_iff_isUnit_map_of_injective`

English:
theorem IsPrimitive.isUnit_iff_isUnit_map_of_injective
  statement: IsUnit f ↔ IsUnit (map φ f)
  proof: by
  refine ⟨(mapRingHom φ).isUnit_map, fun h => ?_⟩
  rcases isUnit_iff.1 h with ⟨_, ⟨u, rfl⟩, hu⟩
  have hdeg := degree_C u.ne_zero
  rw [hu]; rw [degree_map_eq_of_injective hinj] at hdeg
  rw [eq_C_of_degree_eq_zero hdeg] at hf ⊢
  exact isUnit_C.mpr (isPrimitive_iff_isUnit_of_C_dvd.mp hf (f.coef

中文:
定理 是Primitive.isUnit_iff_isUnit_map_of_injective
  结论: 是单位 f ↔ 是单位 (map φ f)
  证明: by
  refine ⟨(mapRingHom φ).isUnit_map, fun h => ?_⟩
  rcases isUnit_iff.1 h with ⟨_, ⟨u, rfl⟩, hu⟩
  have hdeg := degree_C u.ne_zero
  rw [hu]; rw [degree_map_eq_of_injective hinj] at hdeg
  rw [eq_C_of_degree_eq_zero hdeg] at hf ⊢
  exact isUnit_C.mpr (isPrimitive_iff_isUnit_of_C_dvd.mp hf (f.coef

Depends on / 依赖: degree_C, degree_map_eq_of_injective, dvd_rfl, eq_C_of_degree_eq_zero, f.coeff, isPrimitive_iff_isUnit_of_C_dvd, isPrimitive_iff_isUnit_of_C_dvd.mp, isUnit_C, isUnit_C.mpr, isUnit_iff, isUnit_map, mapRingHom, ne_zero, u.ne_zero
-/
theorem IsPrimitive.isUnit_iff_isUnit_map_of_injective : IsUnit f ↔ IsUnit (map φ f) := by
  refine ⟨(mapRingHom φ).isUnit_map, fun h => ?_⟩
  rcases isUnit_iff.1 h with ⟨_, ⟨u, rfl⟩, hu⟩
  have hdeg := degree_C u.ne_zero
  rw [hu]; rw [degree_map_eq_of_injective hinj] at hdeg
  rw [eq_C_of_degree_eq_zero hdeg] at hf ⊢
  exact isUnit_C.mpr (isPrimitive_iff_isUnit_of_C_dvd.mp hf (f.coeff 0) dvd_rfl)

/--
theorem `IsPrimitive.irreducible_of_irreducible_map_of_injective` / 定理 `IsPrimitive.irreducible_of_irreducible_map_of_injective`

English:
theorem IsPrimitive.irreducible_of_irreducible_map_of_injective
  given: (h_irr : Irreducible (map φ f))
  proof: by
  refine
    ⟨fun h => h_irr.not_isUnit (IsUnit.map (mapRingHom φ) h), fun a b h =>
      (h_irr.isUnit_or_isUnit <| by rw [h, Polynomial.map_mul]).imp ?_ ?_⟩
  all_goals apply ((isPrimitive_of_dvd hf _).isUnit_iff_isUnit_map_of_injective hinj).mpr
  exacts [Dvd.intro _ h.symm, Dvd.intro_left _ h

中文:
定理 是Primitive.irreducible_of_irreducible_map_of_injective
  条件: (h_irr : 不可约 (map φ f))
  证明: by
  refine
    ⟨fun h => h_irr.not_isUnit (IsUnit.map (mapRingHom φ) h), fun a b h =>
      (h_irr.isUnit_or_isUnit <| by rw [h, Polynomial.map_mul]).imp ?_ ?_⟩
  all_goals apply ((isPrimitive_of_dvd hf _).isUnit_iff_isUnit_map_of_injective hinj).mpr
  exacts [Dvd.intro _ h.symm, Dvd.intro_left _ h

Depends on / 依赖: Dvd.intro, Dvd.intro_left, IsUnit, IsUnit.map, Polynomial, Polynomial.map_mul, all_goals, exacts, h.symm, h_irr, h_irr.isUnit_or_isUnit, h_irr.not_isUnit, intro_left, isPrimitive_of_dvd, isUnit_iff_isUnit_map_of_injective, isUnit_or_isUnit, mapRingHom, map_mul, not_isUnit
-/
theorem IsPrimitive.irreducible_of_irreducible_map_of_injective (h_irr : Irreducible (map φ f)) :
    Irreducible f := by
  refine
    ⟨fun h => h_irr.not_isUnit (IsUnit.map (mapRingHom φ) h), fun a b h =>
      (h_irr.isUnit_or_isUnit <| by rw [h, Polynomial.map_mul]).imp ?_ ?_⟩
  all_goals apply ((isPrimitive_of_dvd hf _).isUnit_iff_isUnit_map_of_injective hinj).mpr
  exacts [Dvd.intro _ h.symm, Dvd.intro_left _ h.symm]

end

section FractionMap

variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/--
theorem `IsPrimitive.isUnit_iff_isUnit_map` / 定理 `IsPrimitive.isUnit_iff_isUnit_map`

English:
theorem IsPrimitive.isUnit_iff_isUnit_map
  given: {p : R[X]} (hp : p.IsPrimitive)
  proof: hp.isUnit_iff_isUnit_map_of_injective (IsFractionRing.injective _ _)

中文:
定理 是Primitive.isUnit_iff_isUnit_map
  条件: {p : R[X]} (hp : p.是Primitive)
  证明: hp.isUnit_iff_isUnit_map_of_injective (IsFractionRing.injective _ _)

Depends on / 依赖: IsFractionRing, IsFractionRing.injective, hp.isUnit_iff_isUnit_map_of_injective, injective, isUnit_iff_isUnit_map_of_injective
-/
theorem IsPrimitive.isUnit_iff_isUnit_map {p : R[X]} (hp : p.IsPrimitive) :
    IsUnit p ↔ IsUnit (p.map (algebraMap R K)) :=
  hp.isUnit_iff_isUnit_map_of_injective (IsFractionRing.injective _ _)

section IsIntegrallyClosed

open IsIntegrallyClosed

/--
theorem `Monic.irreducible_iff_irreducible_map_fraction_map` / 定理 `Monic.irreducible_iff_irreducible_map_fraction_map`

English:
theorem Monic.irreducible_iff_irreducible_map_fraction_map
  statement: [IsIntegrallyClosed R] {p : R[X]}
  proof: by
  /- The ← direction follows from `IsPrimitive.irreducible_of_irreducible_map_of_injective`.
       For the → direction, it is enough to show that if `(p.map <| algebraMap R K) = a * b` and
       `a` is not a unit then `b` is a unit -/
  refine
    ⟨fun hp =>
      irreducible_iff.mpr
        ⟨h

中文:
定理 Monic.irreducible_iff_irreducible_map_fraction_map
  结论: [是整闭 R] {p : R[X]}
  证明: by
  /- The ← direction follows from `IsPrimitive.irreducible_of_irreducible_map_of_injective`.
       For the → direction, it is enough to show that if `(p.map <| algebraMap R K) = a * b` and
       `a` is not a unit then `b` is a unit -/
  refine
    ⟨fun hp =>
      irreducible_iff.mpr
        ⟨h
-/
theorem Monic.irreducible_iff_irreducible_map_fraction_map [IsIntegrallyClosed R] {p : R[X]}
    (h : p.Monic) : Irreducible p ↔ Irreducible (p.map <| algebraMap R K) := by
  /- The ← direction follows from `IsPrimitive.irreducible_of_irreducible_map_of_injective`.
       For the → direction, it is enough to show that if `(p.map <| algebraMap R K) = a * b` and
       `a` is not a unit then `b` is a unit -/
  refine
    ⟨fun hp =>
      irreducible_iff.mpr
        ⟨hp.not_isUnit.imp h.isPrimitive.isUnit_iff_isUnit_map.mpr, fun a b H =>
          or_iff_not_imp_left.mpr fun hₐ => ?_⟩,
      fun hp =>
      h.isPrimitive.irreducible_of_irreducible_map_of_injective (IsFractionRing.injective R K) hp⟩
  obtain ⟨a', ha⟩ := eq_map_mul_C_of_dvd K h (dvd_of_mul_right_eq b H.symm)
  obtain ⟨b', hb⟩ := eq_map_mul_C_of_dvd K h (dvd_of_mul_left_eq a H.symm)
  have : a.leadingCoeff * b.leadingCoeff = 1 := by
    rw [← leadingCoeff_mul]; rw [← H]; rw [Monic.leadingCoeff (h.map <| algebraMap R K)]
  rw [← ha]; rw [← hb]; rw [mul_comm _ (C b.leadingCoeff)]; rw [mul_assoc]; rw [← mul_assoc (C a.leadingCoeff)]; rw [←
    C_mul]; rw [this]; rw [C_1]; rw [one_mul]; rw [← Polynomial.map_mul] at H
  rw [← hb]; rw [← Polynomial.coe_mapRingHom]
  refine
    IsUnit.mul (IsUnit.map _ (Or.resolve_left (hp.isUnit_or_isUnit ?_) (show ¬IsUnit a' from ?_)))
      (isUnit_iff_exists_inv'.mpr
        (Exists.intro (C a.leadingCoeff) <| by rw [← C_mul, this, C_1]))
  · exact Polynomial.map_injective _ (IsFractionRing.injective R K) H
  · by_contra h_contra
    refine hₐ ?_
    rw [← ha]; rw [← Polynomial.coe_mapRingHom]
    exact
      IsUnit.mul (IsUnit.map _ h_contra)
        (isUnit_iff_exists_inv.mpr
          (Exists.intro (C b.leadingCoeff) <| by rw [← C_mul, this, C_1]))

/--
theorem `isIntegrallyClosed_iff'` / 定理 `isIntegrallyClosed_iff'`

English:
theorem isIntegrallyClosed_iff'
  given: [IsDomain R]
  proof: by
  constructor
  · intro hR p hp; exact Monic.irreducible_iff_irreducible_map_fraction_map hp
  · intro H
    refine
      (isIntegrallyClosed_iff K).mpr fun {x} hx =>
RingHom.mem_range.mp minpoly.mem_range_of_degree_eq_one R x ?_
    rw [← Monic.degree_map (minpoly.monic hx) (algebraMap R K)]
   

中文:
定理 is整数egrallyClosed_iff'
  条件: [是整环 R]
  证明: by
  constructor
  · intro hR p hp; exact Monic.irreducible_iff_irreducible_map_fraction_map hp
  · intro H
    refine
      (isIntegrallyClosed_iff K).mpr fun {x} hx =>
RingHom.mem_range.mp minpoly.mem_range_of_degree_eq_one R x ?_
    rw [← Monic.degree_map (minpoly.monic hx) (algebraMap R K)]
   

Depends on / 依赖: IsRoot, Monic.degree_map, Monic.irreducible_iff_irreducible_map_fraction_map, RingHom, RingHom.mem_range.mp, algebraMap, degree_eq_one_of_irreducible_of_root, degree_map, eval_map_algebraMap, irreducible, irreducible_iff_irreducible_map_fraction_map, isIntegrallyClosed_iff, mem_range, mem_range_of_degree_eq_one, minpoly, minpoly.aeval, minpoly.irreducible, minpoly.mem_range_of_degree_eq_one, minpoly.monic
-/
theorem isIntegrallyClosed_iff' [IsDomain R] :
    IsIntegrallyClosed R ↔
      forall p : R[X], p.Monic -> (Irreducible p ↔ Irreducible (p.map <| algebraMap R K)) := by
  constructor
  · intro hR p hp; exact Monic.irreducible_iff_irreducible_map_fraction_map hp
  · intro H
    refine
      (isIntegrallyClosed_iff K).mpr fun {x} hx =>
RingHom.mem_range.mp minpoly.mem_range_of_degree_eq_one R x ?_
    rw [← Monic.degree_map (minpoly.monic hx) (algebraMap R K)]
    apply
      degree_eq_one_of_irreducible_of_root ((H _ <| minpoly.monic hx).mp (minpoly.irreducible hx))
    rw [IsRoot]; rw [eval_map_algebraMap]; rw [minpoly.aeval R x]

/--
theorem `Monic.dvd_of_fraction_map_dvd_fraction_map` / 定理 `Monic.dvd_of_fraction_map_dvd_fraction_map`

English:
theorem Monic.dvd_of_fraction_map_dvd_fraction_map
  statement: [IsIntegrallyClosed R] {p q : R[X]}
  proof: by
  obtain ⟨r, hr⟩ := h
  obtain ⟨d', hr'⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd K hp (dvd_of_mul_left_eq _ hr.symm)
  rw [Monic.leadingCoeff]; rw [C_1]; rw [mul_one] at hr'
  · rw [← hr', ← Polynomial.map_mul] at hr
    exact dvd_of_mul_right_eq _ (Polynomial.map_injective _ (IsFractionRing.in

中文:
定理 Monic.dvd_of_fraction_map_dvd_fraction_map
  结论: [是整闭 R] {p q : R[X]}
  证明: by
  obtain ⟨r, hr⟩ := h
  obtain ⟨d', hr'⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd K hp (dvd_of_mul_left_eq _ hr.symm)
  rw [Monic.leadingCoeff]; rw [C_1]; rw [mul_one] at hr'
  · rw [← hr', ← Polynomial.map_mul] at hr
    exact dvd_of_mul_right_eq _ (Polynomial.map_injective _ (IsFractionRing.in

Depends on / 依赖: IsFractionRing, IsFractionRing.injective, IsIntegrallyClosed, IsIntegrallyClosed.eq_map_mul_C_of_dvd, Monic.leadingCoeff, Monic.of_mul_monic_left, Polynomial, Polynomial.map_injective, Polynomial.map_mul, algebraMap, dvd_of_mul_left_eq, dvd_of_mul_right_eq, eq_map_mul_C_of_dvd, hp.map, hq.map, hr.symm, injective, leadingCoeff, map_injective, map_mul
-/
theorem Monic.dvd_of_fraction_map_dvd_fraction_map [IsIntegrallyClosed R] {p q : R[X]}
    (hp : p.Monic) (hq : q.Monic)
    (h : q.map (algebraMap R K) ∣ p.map (algebraMap R K)) : q ∣ p := by
  obtain ⟨r, hr⟩ := h
  obtain ⟨d', hr'⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd K hp (dvd_of_mul_left_eq _ hr.symm)
  rw [Monic.leadingCoeff]; rw [C_1]; rw [mul_one] at hr'
  · rw [← hr', ← Polynomial.map_mul] at hr
    exact dvd_of_mul_right_eq _ (Polynomial.map_injective _ (IsFractionRing.injective R K) hr.symm)
  · exact Monic.of_mul_monic_left (hq.map (algebraMap R K)) (by simpa [← hr] using hp.map _)

/--
theorem `Monic.dvd_iff_fraction_map_dvd_fraction_map` / 定理 `Monic.dvd_iff_fraction_map_dvd_fraction_map`

English:
theorem Monic.dvd_iff_fraction_map_dvd_fraction_map
  statement: [IsIntegrallyClosed R] {p q : R[X]}
  proof: ⟨fun h => hp.dvd_of_fraction_map_dvd_fraction_map hq h, fun ⟨a, b⟩ =>
    ⟨a.map (algebraMap R K), b.symm ▸ Polynomial.map_mul (algebraMap R K)⟩⟩

中文:
定理 Monic.dvd_iff_fraction_map_dvd_fraction_map
  结论: [是整闭 R] {p q : R[X]}
  证明: ⟨fun h => hp.dvd_of_fraction_map_dvd_fraction_map hq h, fun ⟨a, b⟩ =>
    ⟨a.map (algebraMap R K), b.symm ▸ Polynomial.map_mul (algebraMap R K)⟩⟩

Depends on / 依赖: Polynomial, Polynomial.map_mul, a.map, algebraMap, b.symm, dvd_of_fraction_map_dvd_fraction_map, hp.dvd_of_fraction_map_dvd_fraction_map, map_mul
-/
theorem Monic.dvd_iff_fraction_map_dvd_fraction_map [IsIntegrallyClosed R] {p q : R[X]}
    (hp : p.Monic) (hq : q.Monic) : q.map (algebraMap R K) ∣ p.map (algebraMap R K) ↔ q ∣ p :=
  ⟨fun h => hp.dvd_of_fraction_map_dvd_fraction_map hq h, fun ⟨a, b⟩ =>
    ⟨a.map (algebraMap R K), b.symm ▸ Polynomial.map_mul (algebraMap R K)⟩⟩

end IsIntegrallyClosed

open IsLocalization

section GCDMonoid

variable [IsDomain R]

/--
theorem `isUnit_or_eq_zero_of_isUnit_integerNormalization_primPart` / 定理 `isUnit_or_eq_zero_of_isUnit_integerNormalization_primPart`

English:
theorem isUnit_or_eq_zero_of_isUnit_integerNormalization_primPart
  statement: [NormalizedGCDMonoid R]
  proof: by
  rcases isUnit_iff.1 h with ⟨_, ⟨u, rfl⟩, hu⟩
  obtain ⟨c, c0, hc⟩ := integerNormalization_spec R⁰ p
  rw [Algebra.smul_def]; rw [algebraMap_apply] at hc
  apply isUnit_of_mul_isUnit_right
  rw [← hc]; rw [(integerNormalization R⁰ p).eq_C_content_mul_primPart]; rw [← hu]; rw [← map_mul]; rw [isU

中文:
定理 isUnit_or_eq_zero_of_isUnit_integerNormalization_primPart
  结论: [正规化最大公约数幺半群 R]
  证明: by
  rcases isUnit_iff.1 h with ⟨_, ⟨u, rfl⟩, hu⟩
  obtain ⟨c, c0, hc⟩ := integerNormalization_spec R⁰ p
  rw [Algebra.smul_def]; rw [algebraMap_apply] at hc
  apply isUnit_of_mul_isUnit_right
  rw [← hc]; rw [(integerNormalization R⁰ p).eq_C_content_mul_primPart]; rw [← hu]; rw [← map_mul]; rw [isU

Depends on / 依赖: Algebra, Algebra.smul_def, IsFractionRing, IsFractionRing.injective, algebraMap, algebraMap_apply, content, eq_C_content_mul_primPart, injective, injective_iff_map_eq_zero, integerNormalization, integerNormalization_spec, isUnit_iff, isUnit_iff_ne_zero, isUnit_of_mul_isUnit_right, map_mul, replace, smul_def
-/
theorem isUnit_or_eq_zero_of_isUnit_integerNormalization_primPart [NormalizedGCDMonoid R]
    {p : K[X]} (h0 : p != 0) (h : IsUnit (integerNormalization R⁰ p).primPart) : IsUnit p := by
  rcases isUnit_iff.1 h with ⟨_, ⟨u, rfl⟩, hu⟩
  obtain ⟨c, c0, hc⟩ := integerNormalization_spec R⁰ p
  rw [Algebra.smul_def]; rw [algebraMap_apply] at hc
  apply isUnit_of_mul_isUnit_right
  rw [← hc]; rw [(integerNormalization R⁰ p).eq_C_content_mul_primPart]; rw [← hu]; rw [← map_mul]; rw [isUnit_iff]
  refine
    ⟨algebraMap R K ((integerNormalization R⁰ p).content * ↑u), isUnit_iff_ne_zero.2 fun con => ?_,
      by simp⟩
  replace con := (injective_iff_map_eq_zero (algebraMap R K)).1 (IsFractionRing.injective _ _) _ con
  rw [mul_eq_zero]; rw [content_eq_zero_iff]; rw [IsFractionRing.integerNormalization_eq_zero_iff] at con
  rcases con with (con | con)
  · apply h0 con
  · apply Units.ne_zero _ con

variable [IsGCDMonoid R]

/--
lemma `IsPrimitive.mul_map_mem_lifts_iff` / 引理 `IsPrimitive.mul_map_mem_lifts_iff`

English:
lemma IsPrimitive.mul_map_mem_lifts_iff
  given: {f : R[X]} (hf : IsPrimitive f) {g : K[X]}
  proof: by
  let : NormalizedGCDMonoid R := Nonempty.some inferInstance
  refine ⟨fun ⟨k, (hk : k.map _ = _)⟩ => ?_, fun h => mul_mem h ⟨_, rfl⟩⟩
  let g' := integerNormalization R⁰ g
  obtain ⟨b, hb₁, (hb₂ : g'.map _ = _)⟩ := integerNormalization_spec R⁰ g
  have g'_mul_f : g' * f = b • k := by
    apply m

中文:
引理 是Primitive.mul_map_mem_lifts_iff
  条件: {f : R[X]} (hf : 是Primitive f) {g : K[X]}
  证明: by
  let : NormalizedGCDMonoid R := Nonempty.some inferInstance
  refine ⟨fun ⟨k, (hk : k.map _ = _)⟩ => ?_, fun h => mul_mem h ⟨_, rfl⟩⟩
  let g' := integerNormalization R⁰ g
  obtain ⟨b, hb₁, (hb₂ : g'.map _ = _)⟩ := integerNormalization_spec R⁰ g
  have g'_mul_f : g' * f = b • k := by
    apply m

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, Nonempty, Nonempty.some, NormalizedGCDMonoid, Polynomial, Polynomial.map_mul, Polynomial.map_smul, _mul_, _mul_f, algebraMap, algebraMap_injective, algebraMap_smul, apply_fun, content, integerNormalization, integerNormalization_spec, k.map, map_injective, map_mul
-/
lemma IsPrimitive.mul_map_mem_lifts_iff {f : R[X]} (hf : IsPrimitive f) {g : K[X]} :
    g * f.map (algebraMap R K) in lifts (algebraMap R K) ↔ g in lifts (algebraMap R K) := by
  let : NormalizedGCDMonoid R := Nonempty.some inferInstance
  refine ⟨fun ⟨k, (hk : k.map _ = _)⟩ => ?_, fun h => mul_mem h ⟨_, rfl⟩⟩
  let g' := integerNormalization R⁰ g
  obtain ⟨b, hb₁, (hb₂ : g'.map _ = _)⟩ := integerNormalization_spec R⁰ g
  have g'_mul_f : g' * f = b • k := by
    apply map_injective (algebraMap R K) (FaithfulSMul.algebraMap_injective R K)
    rw [Polynomial.map_smul]; rw [algebraMap_smul]; rw [hk]; rw [← smul_mul_assoc]; rw [← hb₂]; rw [Polynomial.map_mul]
  apply_fun content at g'_mul_f
  have h := Associated.of_eq g'_mul_f
  grw [← C_mul', associated_content_mul, associated_content_C_mul, hf.content_eq_one, mul_one] at h
obtain ⟨g'', hg⟩ : C b ∣ g' := dvd_content_iff_C_dvd.mp (dvd_mul_right ..).trans h.dvd'
  use g''
  simp [← smul_right_inj (nonZeroDivisors.ne_zero hb₁), ← hb₂, hg, C_mul']

/--
lemma `IsPrimitive.map_mul_mem_lifts_iff` / 引理 `IsPrimitive.map_mul_mem_lifts_iff`

English:
lemma IsPrimitive.map_mul_mem_lifts_iff
  given: {f : R[X]} (hf : IsPrimitive f) {g : K[X]}
  proof: by
  rw [mul_comm]; rw [hf.mul_map_mem_lifts_iff]

中文:
引理 是Primitive.map_mul_mem_lifts_iff
  条件: {f : R[X]} (hf : 是Primitive f) {g : K[X]}
  证明: by
  rw [mul_comm]; rw [hf.mul_map_mem_lifts_iff]

Depends on / 依赖: hf.mul_map_mem_lifts_iff, mul_comm, mul_map_mem_lifts_iff
-/
lemma IsPrimitive.map_mul_mem_lifts_iff {f : R[X]} (hf : IsPrimitive f) {g : K[X]} :
    f.map (algebraMap R K) * g in lifts (algebraMap R K) ↔ g in lifts (algebraMap R K) := by
  rw [mul_comm]; rw [hf.mul_map_mem_lifts_iff]

/--
theorem `IsPrimitive.irreducible_iff_irreducible_map_fraction_map` / 定理 `IsPrimitive.irreducible_iff_irreducible_map_fraction_map`

English:
theorem IsPrimitive.irreducible_iff_irreducible_map_fraction_map
  given: {p : R[X]} (hp : p.IsPrimitive)
  proof: by
  refine
    ⟨fun hi => ⟨fun h => hi.not_isUnit (hp.isUnit_iff_isUnit_map.2 h), fun a b hab => ?_⟩,
      hp.irreducible_of_irreducible_map_of_injective (IsFractionRing.injective _ _)⟩
  obtain ⟨c, c0, hc⟩ := integerNormalization_spec R⁰ a
  obtain ⟨d, d0, hd⟩ := integerNormalization_spec R⁰ b
  

中文:
定理 是Primitive.irreducible_iff_irreducible_map_fraction_map
  条件: {p : R[X]} (hp : p.是Primitive)
  证明: by
  refine
    ⟨fun hi => ⟨fun h => hi.not_isUnit (hp.isUnit_iff_isUnit_map.2 h), fun a b hab => ?_⟩,
      hp.irreducible_of_irreducible_map_of_injective (IsFractionRing.injective _ _)⟩
  obtain ⟨c, c0, hc⟩ := integerNormalization_spec R⁰ a
  obtain ⟨d, d0, hd⟩ := integerNormalization_spec R⁰ b
  

Depends on / 依赖: Algebra, Algebra.smul_def, C_eq_zero, IsFractionRing, IsFractionRing.injective, algebraMap_apply, hi.not_isUnit, hp.irreducible_of_irreducible_map_of_injective, hp.isUnit_iff_isUnit_map, injective, integerNormali, integerNormalization_spec, irreducible_of_irreducible_map_of_injective, isUnit_iff_isUnit_map, mem_nonZeroDivisors_iff_ne_zero, mul_ne_zero, not_isUnit, smul_def
-/
theorem IsPrimitive.irreducible_iff_irreducible_map_fraction_map {p : R[X]} (hp : p.IsPrimitive) :
    Irreducible p ↔ Irreducible (p.map (algebraMap R K)) := by
  refine
    ⟨fun hi => ⟨fun h => hi.not_isUnit (hp.isUnit_iff_isUnit_map.2 h), fun a b hab => ?_⟩,
      hp.irreducible_of_irreducible_map_of_injective (IsFractionRing.injective _ _)⟩
  obtain ⟨c, c0, hc⟩ := integerNormalization_spec R⁰ a
  obtain ⟨d, d0, hd⟩ := integerNormalization_spec R⁰ b
  rw [Algebra.smul_def]; rw [algebraMap_apply] at hc hd
  rw [mem_nonZeroDivisors_iff_ne_zero] at c0 d0
  have hcd0 : c * d != 0 := mul_ne_zero c0 d0
  rw [Ne]; rw [← C_eq_zero] at hcd0
  have h1 : C c * C d * p = integerNormalization R⁰ a * integerNormalization R⁰ b := by
    apply map_injective (algebraMap R K) (IsFractionRing.injective _ _) _
    rw [Polynomial.map_mul]; rw [Polynomial.map_mul]; rw [Polynomial.map_mul]; rw [hc]; rw [hd]; rw [map_C]; rw [map_C]; rw [hab]
    ring
  have := Classical.arbitrary (NormalizedGCDMonoid R)
  obtain ⟨u, hu⟩ :
    Associated (c * d)
      (content (integerNormalization R⁰ a) * content (integerNormalization R⁰ b)) := by
    grw [← associated_content_mul, ← h1, associated_content_mul, ← C_mul, content_C,
      hp.content_eq_one, mul_one]
    apply associated_normalize
  rw [← map_mul]; rw [eq_comm]; rw [(integerNormalization R⁰ a).eq_C_content_mul_primPart]; rw [(integerNormalization R⁰ b).eq_C_content_mul_primPart]; rw [mul_assoc]; rw [mul_comm _ (C _ * _)]; rw [←
    mul_assoc]; rw [← mul_assoc]; rw [← map_mul]; rw [← hu]; rw [map_mul]; rw [mul_assoc]; rw [mul_assoc]; rw [←
    mul_assoc (C (u : R))] at h1
  have h0 : a != 0 ∧ b != 0 := by
    rw [Ne]; rw [Ne]; rw [← not_or]; rw [← mul_eq_zero]; rw [← hab]
    intro con
    apply hp.ne_zero (map_injective (algebraMap R K) (IsFractionRing.injective _ _) _)
    simp [con]
  rcases hi.isUnit_or_isUnit (mul_left_cancel₀ hcd0 h1).symm with (h | h)
  · right
    apply
      isUnit_or_eq_zero_of_isUnit_integerNormalization_primPart h0.2
        (isUnit_of_mul_isUnit_right h)
  · left
    apply isUnit_or_eq_zero_of_isUnit_integerNormalization_primPart h0.1 h

/--
theorem `IsPrimitive.dvd_of_fraction_map_dvd_fraction_map` / 定理 `IsPrimitive.dvd_of_fraction_map_dvd_fraction_map`

English:
theorem IsPrimitive.dvd_of_fraction_map_dvd_fraction_map
  statement: {p q : R[X]} (hp : p.IsPrimitive)
  proof: by
  rcases h_dvd with ⟨r, hr⟩
  obtain ⟨r, rfl⟩ := (mul_map_mem_lifts_iff hp).mp ⟨q, mul_comm _ r ▸ hr⟩
  use r
  simpa [← Polynomial.map_mul, (map_injective _ (FaithfulSMul.algebraMap_injective R K)).eq_iff]
    using hr

中文:
定理 是Primitive.dvd_of_fraction_map_dvd_fraction_map
  结论: {p q : R[X]} (hp : p.是Primitive)
  证明: by
  rcases h_dvd with ⟨r, hr⟩
  obtain ⟨r, rfl⟩ := (mul_map_mem_lifts_iff hp).mp ⟨q, mul_comm _ r ▸ hr⟩
  use r
  simpa [← Polynomial.map_mul, (map_injective _ (FaithfulSMul.algebraMap_injective R K)).eq_iff]
    using hr

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, Polynomial, Polynomial.map_mul, algebraMap_injective, eq_iff, h_dvd, map_injective, map_mul, mul_comm, mul_map_mem_lifts_iff
-/
theorem IsPrimitive.dvd_of_fraction_map_dvd_fraction_map {p q : R[X]} (hp : p.IsPrimitive)
    (h_dvd : p.map (algebraMap R K) ∣ q.map (algebraMap R K)) : p ∣ q := by
  rcases h_dvd with ⟨r, hr⟩
  obtain ⟨r, rfl⟩ := (mul_map_mem_lifts_iff hp).mp ⟨q, mul_comm _ r ▸ hr⟩
  use r
  simpa [← Polynomial.map_mul, (map_injective _ (FaithfulSMul.algebraMap_injective R K)).eq_iff]
    using hr

variable (K)

/--
theorem `IsPrimitive.dvd_iff_fraction_map_dvd_fraction_map` / 定理 `IsPrimitive.dvd_iff_fraction_map_dvd_fraction_map`

English:
theorem IsPrimitive.dvd_iff_fraction_map_dvd_fraction_map
  given: {p q : R[X]} (hp : p.IsPrimitive)
  proof: ⟨fun ⟨a, b⟩ => ⟨a.map (algebraMap R K), b.symm ▸ Polynomial.map_mul (algebraMap R K)⟩, fun h =>
    hp.dvd_of_fraction_map_dvd_fraction_map h⟩

中文:
定理 是Primitive.dvd_iff_fraction_map_dvd_fraction_map
  条件: {p q : R[X]} (hp : p.是Primitive)
  证明: ⟨fun ⟨a, b⟩ => ⟨a.map (algebraMap R K), b.symm ▸ Polynomial.map_mul (algebraMap R K)⟩, fun h =>
    hp.dvd_of_fraction_map_dvd_fraction_map h⟩

Depends on / 依赖: Polynomial, Polynomial.map_mul, a.map, algebraMap, b.symm, dvd_of_fraction_map_dvd_fraction_map, hp.dvd_of_fraction_map_dvd_fraction_map, map_mul
-/
theorem IsPrimitive.dvd_iff_fraction_map_dvd_fraction_map {p q : R[X]} (hp : p.IsPrimitive) :
    p ∣ q ↔ p.map (algebraMap R K) ∣ q.map (algebraMap R K) :=
  ⟨fun ⟨a, b⟩ => ⟨a.map (algebraMap R K), b.symm ▸ Polynomial.map_mul (algebraMap R K)⟩, fun h =>
    hp.dvd_of_fraction_map_dvd_fraction_map h⟩

end GCDMonoid

end FractionMap

/--
theorem `IsPrimitive.Int.irreducible_iff_irreducible_map_cast` / 定理 `IsPrimitive.Int.irreducible_iff_irreducible_map_cast`

English:
theorem IsPrimitive.Int.irreducible_iff_irreducible_map_cast
  given: {p : Int[X]} (hp : p.IsPrimitive)
  proof: hp.irreducible_iff_irreducible_map_fraction_map

中文:
定理 是Primitive.整数.irreducible_iff_irreducible_map_cast
  条件: {p : 整数[X]} (hp : p.是Primitive)
  证明: hp.irreducible_iff_irreducible_map_fraction_map

Depends on / 依赖: SMulMemClass, SMulMemClass.smul_mem, hp.irreducible_iff_irreducible_map_fraction_map, irreducible_iff_irreducible_map_fraction_map, smul_mem
-/
theorem IsPrimitive.Int.irreducible_iff_irreducible_map_cast {p : Int[X]} (hp : p.IsPrimitive) :
    Irreducible p ↔ Irreducible (p.map (Int.castRingHom Rat)) :=
  hp.irreducible_iff_irreducible_map_fraction_map

/--
theorem `IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast` / 定理 `IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast`

English:
theorem IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast
  given: (p q : Int[X]) (hp : p.IsPrimitive)
  proof: hp.dvd_iff_fraction_map_dvd_fraction_map Rat

中文:
定理 是Primitive.整数.dvd_iff_map_cast_dvd_map_cast
  条件: (p q : 整数[X]) (hp : p.是Primitive)
  证明: hp.dvd_iff_fraction_map_dvd_fraction_map Rat

Depends on / 依赖: dvd_iff_fraction_map_dvd_fraction_map, hp.dvd_iff_fraction_map_dvd_fraction_map
-/
theorem IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast (p q : Int[X]) (hp : p.IsPrimitive) :
    p ∣ q ↔ p.map (Int.castRingHom Rat) ∣ q.map (Int.castRingHom Rat) :=
  hp.dvd_iff_fraction_map_dvd_fraction_map Rat

end Polynomial
