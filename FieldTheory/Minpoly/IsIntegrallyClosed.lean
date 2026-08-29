/-
Copyright (c) 2019 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Paul Lezeau, Junyan Xu
-/
module

public import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# Minimal polynomials over a GCD monoid

This file specializes the theory of minpoly to the case of an algebra over a GCD monoid.

## Main results

* `minpoly.isIntegrallyClosed_eq_field_fractions`: For integrally closed domains, the minimal
  polynomial over the ring is the same as the minimal polynomial over the fraction field.

* `minpoly.isIntegrallyClosed_dvd`: For integrally closed domains, the minimal polynomial divides
  any primitive polynomial that has the integral element as root.

* `IsIntegrallyClosed.Minpoly.unique`: The minimal polynomial of an element `x` is uniquely
  characterized by its defining property: if there is another monic polynomial of minimal degree
  that has `x` as a root, then this polynomial is equal to the minimal polynomial of `x`.

-/

@[expose] public section

open Polynomial Set Function minpoly Module

namespace minpoly

variable {R S : Type*} [CommRing R] [CommRing S] [IsDomain R] [Algebra R S]

section

variable (K L : Type*) [Field K] [Algebra R K] [IsFractionRing R K] [CommRing L] [Nontrivial L]
  [Algebra R L] [Algebra S L] [Algebra K L] [IsScalarTower R K L] [IsScalarTower R S L]

variable [IsIntegrallyClosed R]

/--
theorem `isIntegrallyClosed_eq_field_fractions` / 定理 `isIntegrallyClosed_eq_field_fractions`

English:
theorem isIntegrallyClosed_eq_field_fractions
  given: [IsDomain S] {s : S} (hs : IsIntegral R s)
  proof: by
  refine (eq_of_irreducible_of_monic ?_ ?_ ?_).symm
  · exact ((monic hs).irreducible_iff_irreducible_map_fraction_map).1 (irreducible hs)
  · rw [aeval_map_algebraMap, aeval_algebraMap_apply, aeval, map_zero]
  · exact (monic hs).map _

中文:
定理 is整数egrallyClosed_eq_field_fractions
  条件: [是整环 S] {s : S} (hs : 是整 R s)
  证明: by
  refine (eq_of_irreducible_of_monic ?_ ?_ ?_).symm
  · exact ((monic hs).irreducible_iff_irreducible_map_fraction_map).1 (irreducible hs)
  · rw [aeval_map_algebraMap, aeval_algebraMap_apply, aeval, map_zero]
  · exact (monic hs).map _

Depends on / 依赖: aeval_algebraMap_apply, aeval_map_algebraMap, eq_of_irreducible_of_monic, irreducible, irreducible_iff_irreducible_map_fraction_map, map_zero
-/
theorem isIntegrallyClosed_eq_field_fractions [IsDomain S] {s : S} (hs : IsIntegral R s) :
    minpoly K (algebraMap S L s) = (minpoly R s).map (algebraMap R K) := by
  refine (eq_of_irreducible_of_monic ?_ ?_ ?_).symm
  · exact ((monic hs).irreducible_iff_irreducible_map_fraction_map).1 (irreducible hs)
  · rw [aeval_map_algebraMap, aeval_algebraMap_apply, aeval, map_zero]
  · exact (monic hs).map _

/--
theorem `isIntegrallyClosed_eq_field_fractions'` / 定理 `isIntegrallyClosed_eq_field_fractions'`

English:
theorem isIntegrallyClosed_eq_field_fractions'
  statement: [IsDomain S] [Algebra K S] [IsScalarTower R K S]
  proof: by
  let L := FractionRing S
  rw [← isIntegrallyClosed_eq_field_fractions K L hs]; rw [algebraMap_eq (IsFractionRing.injective S L)]

中文:
定理 is整数egrallyClosed_eq_field_fractions'
  结论: [是整环 S] [代数 K S] [标量塔 R K S]
  证明: by
  let L := FractionRing S
  rw [← isIntegrallyClosed_eq_field_fractions K L hs]; rw [algebraMap_eq (IsFractionRing.injective S L)]

Depends on / 依赖: FractionRing, IsFractionRing, IsFractionRing.injective, algebraMap_eq, injective, isIntegrallyClosed_eq_field_fractions
-/
theorem isIntegrallyClosed_eq_field_fractions' [IsDomain S] [Algebra K S] [IsScalarTower R K S]
    {s : S} (hs : IsIntegral R s) : minpoly K s = (minpoly R s).map (algebraMap R K) := by
  let L := FractionRing S
  rw [← isIntegrallyClosed_eq_field_fractions K L hs]; rw [algebraMap_eq (IsFractionRing.injective S L)]

end

variable [IsIntegrallyClosed R] [IsDomain S] [IsTorsionFree R S]

/--
theorem `isIntegrallyClosed_dvd` / 定理 `isIntegrallyClosed_dvd`

English:
theorem isIntegrallyClosed_dvd
  statement: {s : S} (hs : IsIntegral R s) {p : R[X]}
  proof: by
  let K := FractionRing R
  let L := FractionRing S
  let _ : Algebra K L := FractionRing.liftAlgebra R L
  have : minpoly K (algebraMap S L s) ∣ map (algebraMap R K) (p %ₘ minpoly R s) := by
    rw [map_modByMonic _ (minpoly.monic hs)]; rw [modByMonic_eq_sub_mul_div]
    refine dvd_sub (minpoly.

中文:
定理 is整数egrallyClosed_dvd
  结论: {s : S} (hs : 是整 R s) {p : R[X]}
  证明: by
  let K := FractionRing R
  let L := FractionRing S
  let _ : Algebra K L := FractionRing.liftAlgebra R L
  have : minpoly K (algebraMap S L s) ∣ map (algebraMap R K) (p %ₘ minpoly R s) := by
    rw [map_modByMonic _ (minpoly.monic hs)]; rw [modByMonic_eq_sub_mul_div]
    refine dvd_sub (minpoly.

Depends on / 依赖: Algebra, FractionRing, FractionRing.liftAlgebra, IsScalarTower, IsScalarTower.algebraMap_eq, algebraMap, algebraMap_eq, dvd_mul_of_dvd_left, dvd_sub, isIntegrallyClosed_eq_field_fractions, liftAlgebra, map_aeval_eq_aeval_map, map_modByMonic, map_zero, minpoly, minpoly.dvd, minpoly.monic, modByMonic_eq_sub_mul_div
-/
theorem isIntegrallyClosed_dvd {s : S} (hs : IsIntegral R s) {p : R[X]}
    (hp : Polynomial.aeval s p = 0) : minpoly R s ∣ p := by
  let K := FractionRing R
  let L := FractionRing S
  let _ : Algebra K L := FractionRing.liftAlgebra R L
  have : minpoly K (algebraMap S L s) ∣ map (algebraMap R K) (p %ₘ minpoly R s) := by
    rw [map_modByMonic _ (minpoly.monic hs)]; rw [modByMonic_eq_sub_mul_div]
    refine dvd_sub (minpoly.dvd K (algebraMap S L s) ?_) ?_
    · rw [← map_aeval_eq_aeval_map, hp, map_zero]
      rw [← IsScalarTower.algebraMap_eq]; rw [← IsScalarTower.algebraMap_eq]
    apply dvd_mul_of_dvd_left
    rw [isIntegrallyClosed_eq_field_fractions K L hs]
  rw [isIntegrallyClosed_eq_field_fractions _ _ hs]; rw [map_dvd_map (algebraMap R K) (IsFractionRing.injective R K) (minpoly.monic hs)] at this
  rw [← modByMonic_eq_zero_iff_dvd (minpoly.monic hs)]
  exact Polynomial.eq_zero_of_dvd_of_degree_lt this (degree_modByMonic_lt p <| minpoly.monic hs)

/--
theorem `isIntegrallyClosed_dvd_iff` / 定理 `isIntegrallyClosed_dvd_iff`

English:
theorem isIntegrallyClosed_dvd_iff
  given: {s : S} (hs : IsIntegral R s) (p : R[X])
  proof: ⟨fun hp => isIntegrallyClosed_dvd hs hp, fun hp => by
    simpa only [RingHom.mem_ker, RingHom.coe_comp, coe_evalRingHom, coe_mapRingHom,
      Function.comp_apply, eval_map_algebraMap] using
      aeval_eq_zero_of_dvd_aeval_eq_zero hp (minpoly.aeval R s)⟩

中文:
定理 is整数egrallyClosed_dvd_iff
  条件: {s : S} (hs : 是整 R s) (p : R[X])
  证明: ⟨fun hp => isIntegrallyClosed_dvd hs hp, fun hp => by
    simpa only [RingHom.mem_ker, RingHom.coe_comp, coe_evalRingHom, coe_mapRingHom,
      Function.comp_apply, eval_map_algebraMap] using
      aeval_eq_zero_of_dvd_aeval_eq_zero hp (minpoly.aeval R s)⟩

Depends on / 依赖: Function, Function.comp_apply, RingHom, RingHom.coe_comp, RingHom.mem_ker, aeval_eq_zero_of_dvd_aeval_eq_zero, coe_comp, coe_evalRingHom, coe_mapRingHom, comp_apply, eval_map_algebraMap, isIntegrallyClosed_dvd, mem_ker, minpoly, minpoly.aeval
-/
theorem isIntegrallyClosed_dvd_iff {s : S} (hs : IsIntegral R s) (p : R[X]) :
    Polynomial.aeval s p = 0 ↔ minpoly R s ∣ p :=
  ⟨fun hp => isIntegrallyClosed_dvd hs hp, fun hp => by
    simpa only [RingHom.mem_ker, RingHom.coe_comp, coe_evalRingHom, coe_mapRingHom,
      Function.comp_apply, eval_map_algebraMap] using
      aeval_eq_zero_of_dvd_aeval_eq_zero hp (minpoly.aeval R s)⟩

/--
theorem `ker_eval` / 定理 `ker_eval`

English:
theorem ker_eval
  given: {s : S} (hs : IsIntegral R s)
  proof: by
  ext p
  simp_rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    isIntegrallyClosed_dvd_iff hs, ← Ideal.mem_span_singleton]

中文:
定理 ker_eval
  条件: {s : S} (hs : 是整 R s)
  证明: by
  ext p
  simp_rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    isIntegrallyClosed_dvd_iff hs, ← Ideal.mem_span_singleton]

Depends on / 依赖: AlgHom, AlgHom.coe_toRingHom, AlgHom.toRingHom_eq_coe, Ideal.mem_span_singleton, RingHom, RingHom.mem_ker, coe_toRingHom, isIntegrallyClosed_dvd_iff, mem_ker, mem_span_singleton, simp_rw, toRingHom_eq_coe
-/
theorem ker_eval {s : S} (hs : IsIntegral R s) :
    RingHom.ker ((Polynomial.aeval s).toRingHom : R[X] ->+* S) =
    Ideal.span ({minpoly R s} : Set R[X]) := by
  ext p
  simp_rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    isIntegrallyClosed_dvd_iff hs, ← Ideal.mem_span_singleton]

/--
theorem `IsIntegrallyClosed.degree_le_of_ne_zero` / 定理 `IsIntegrallyClosed.degree_le_of_ne_zero`

English:
theorem IsIntegrallyClosed.degree_le_of_ne_zero
  statement: {s : S} {p : R[X]}
  proof: by
  by_cases! hs : ¬IsIntegral R s
  · simp [minpoly, hs]
  rw [degree_eq_natDegree (minpoly.ne_zero hs)]; rw [degree_eq_natDegree hp0]
  norm_cast
  exact natDegree_le_of_dvd ((isIntegrallyClosed_dvd_iff hs _).mp hp) hp0

中文:
定理 是整闭.degree_le_of_ne_zero
  结论: {s : S} {p : R[X]}
  证明: by
  by_cases! hs : ¬IsIntegral R s
  · simp [minpoly, hs]
  rw [degree_eq_natDegree (minpoly.ne_zero hs)]; rw [degree_eq_natDegree hp0]
  norm_cast
  exact natDegree_le_of_dvd ((isIntegrallyClosed_dvd_iff hs _).mp hp) hp0

Depends on / 依赖: IsIntegral, degree_eq_natDegree, isIntegrallyClosed_dvd_iff, minpoly, minpoly.ne_zero, natDegree_le_of_dvd, ne_zero
-/
theorem IsIntegrallyClosed.degree_le_of_ne_zero {s : S} {p : R[X]}
    (hp0 : p != 0) (hp : Polynomial.aeval s p = 0) : degree (minpoly R s) <= degree p := by
  by_cases! hs : ¬IsIntegral R s
  · simp [minpoly, hs]
  rw [degree_eq_natDegree (minpoly.ne_zero hs)]; rw [degree_eq_natDegree hp0]
  norm_cast
  exact natDegree_le_of_dvd ((isIntegrallyClosed_dvd_iff hs _).mp hp) hp0

/--
theorem `IsIntegrallyClosed.isIntegral_iff_isUnit_leadingCoeff` / 定理 `IsIntegrallyClosed.isIntegral_iff_isUnit_leadingCoeff`

English:
theorem IsIntegrallyClosed.isIntegral_iff_isUnit_leadingCoeff
  statement: {x : S} {p : R[X]}
  proof: by
    obtain ⟨p, rfl⟩ := isIntegrallyClosed_dvd int_x hp
    rw [leadingCoeff_mul]; rw [monic int_x]; rw [one_mul]
    exact ((of_irreducible_mul hirr).resolve_left (not_isUnit R x)).map leadingCoeffHom
  mpr isUnit := by
    simpa [smul_smul] using (isIntegral_leadingCoeff_smul _ _ hp).smul ((isUn

中文:
定理 是整闭.is整数egral_iff_isUnit_leadingCoeff
  结论: {x : S} {p : R[X]}
  证明: by
    obtain ⟨p, rfl⟩ := isIntegrallyClosed_dvd int_x hp
    rw [leadingCoeff_mul]; rw [monic int_x]; rw [one_mul]
    exact ((of_irreducible_mul hirr).resolve_left (not_isUnit R x)).map leadingCoeffHom
  mpr isUnit := by
    simpa [smul_smul] using (isIntegral_leadingCoeff_smul _ _ hp).smul ((isUn

Depends on / 依赖: int_x, isIntegral_leadingCoeff_smul, isIntegrallyClosed_dvd, isUnit, isUnit.unit, leadingCoeffHom, leadingCoeff_mul, not_isUnit, of_irreducible_mul, one_mul, resolve_left, smul_smul
-/
theorem IsIntegrallyClosed.isIntegral_iff_isUnit_leadingCoeff {x : S} {p : R[X]}
    (hirr : Irreducible p) (hp : p.aeval x = 0) :
    IsIntegral R x ↔ IsUnit p.leadingCoeff where
  mp int_x := by
    obtain ⟨p, rfl⟩ := isIntegrallyClosed_dvd int_x hp
    rw [leadingCoeff_mul]; rw [monic int_x]; rw [one_mul]
    exact ((of_irreducible_mul hirr).resolve_left (not_isUnit R x)).map leadingCoeffHom
  mpr isUnit := by
    simpa [smul_smul] using (isIntegral_leadingCoeff_smul _ _ hp).smul ((isUnit.unit⁻¹ : Rˣ) : R)

/--
theorem `_root_.IsIntegrallyClosed.minpoly.unique` / 定理 `_root_.IsIntegrallyClosed.minpoly.unique`

English:
theorem _root_.IsIntegrallyClosed.minpoly.unique
  statement: {s : S} {P : R[X]} (hmo : P.Monic)
  proof: by
  have hs : IsIntegral R s := ⟨P, hmo, hP⟩
  symm; apply eq_of_sub_eq_zero
  by_contra hnz
.not_gt ?_ refine IsIntegrallyClosed.degree_le_of_ne_zero (s := s) hnz (by simp [hP])
  refine degree_sub_lt_left ?_ (ne_zero hs) ?_
  · exact le_antisymm (min R s hmo hP) (Pmin (minpoly R s) (monic hs) (ae

中文:
定理 _root_.是整闭.minpoly.unique
  结论: {s : S} {P : R[X]} (hmo : P.Monic)
  证明: by
  have hs : IsIntegral R s := ⟨P, hmo, hP⟩
  symm; apply eq_of_sub_eq_zero
  by_contra hnz
.not_gt ?_ refine IsIntegrallyClosed.degree_le_of_ne_zero (s := s) hnz (by simp [hP])
  refine degree_sub_lt_left ?_ (ne_zero hs) ?_
  · exact le_antisymm (min R s hmo hP) (Pmin (minpoly R s) (monic hs) (ae

Depends on / 依赖: IsIntegral, IsIntegrallyClosed, IsIntegrallyClosed.degree_le_of_ne_zero, degree_le_of_ne_zero, degree_sub_lt_left, eq_of_sub_eq_zero, hmo.leadingCoeff, le_antisymm, leadingCoeff, minpoly, ne_zero, not_gt
-/
theorem _root_.IsIntegrallyClosed.minpoly.unique {s : S} {P : R[X]} (hmo : P.Monic)
    (hP : Polynomial.aeval s P = 0)
    (Pmin : forall Q : R[X], Q.Monic -> Polynomial.aeval s Q = 0 -> degree P <= degree Q) :
    P = minpoly R s := by
  have hs : IsIntegral R s := ⟨P, hmo, hP⟩
  symm; apply eq_of_sub_eq_zero
  by_contra hnz
.not_gt ?_ refine IsIntegrallyClosed.degree_le_of_ne_zero (s := s) hnz (by simp [hP])
  refine degree_sub_lt_left ?_ (ne_zero hs) ?_
  · exact le_antisymm (min R s hmo hP) (Pmin (minpoly R s) (monic hs) (aeval R s))
  · rw [(monic hs).leadingCoeff, hmo.leadingCoeff]

/--
theorem `IsIntegrallyClosed.unique_of_degree_le_degree_minpoly` / 定理 `IsIntegrallyClosed.unique_of_degree_le_degree_minpoly`

English:
theorem IsIntegrallyClosed.unique_of_degree_le_degree_minpoly
  statement: {s : S} {p : R[X]} (hmo : p.Monic)
  proof: IsIntegrallyClosed.minpoly.unique hmo hp fun _ qm hq => pmin.trans min _ _ qm hq

中文:
定理 是整闭.unique_of_degree_le_degree_minpoly
  结论: {s : S} {p : R[X]} (hmo : p.Monic)
  证明: IsIntegrallyClosed.minpoly.unique hmo hp fun _ qm hq => pmin.trans min _ _ qm hq

Depends on / 依赖: IsIntegrallyClosed, IsIntegrallyClosed.minpoly.unique, minpoly, pmin.trans, unique
-/
theorem IsIntegrallyClosed.unique_of_degree_le_degree_minpoly {s : S} {p : R[X]} (hmo : p.Monic)
    (hp : p.aeval s = 0) (pmin : p.degree <= (minpoly R s).degree) : p = minpoly R s :=
IsIntegrallyClosed.minpoly.unique hmo hp fun _ qm hq => pmin.trans min _ _ qm hq

/--
theorem `IsIntegrallyClosed.isIntegral_iff_leadingCoeff_dvd` / 定理 `IsIntegrallyClosed.isIntegral_iff_leadingCoeff_dvd`

English:
theorem IsIntegrallyClosed.isIntegral_iff_leadingCoeff_dvd
  statement: {s : S} {p : R[X]} (hp : p.aeval s = 0)
  proof: by
  refine ⟨fun hInt => ?_, fun ⟨q, hMul⟩ => minpoly.ne_zero_iff.mp ?_⟩
  · use minpoly R s
    have ⟨q, hMul⟩ := isIntegrallyClosed_dvd hInt hp
    suffices q.degree <= 0 by simp [degree_le_zero_iff.mp this ▸ hMul, minpoly.monic hInt, mul_comm]
apply WithBot.le_of_add_le_add_left Polynomial.degree

中文:
定理 是整闭.is整数egral_iff_leadingCoeff_dvd
  结论: {s : S} {p : R[X]} (hp : p.aeval s = 0)
  证明: by
  refine ⟨fun hInt => ?_, fun ⟨q, hMul⟩ => minpoly.ne_zero_iff.mp ?_⟩
  · use minpoly R s
    have ⟨q, hMul⟩ := isIntegrallyClosed_dvd hInt hp
    suffices q.degree <= 0 by simp [degree_le_zero_iff.mp this ▸ hMul, minpoly.monic hInt, mul_comm]
apply WithBot.le_of_add_le_add_left Polynomial.degree

Depends on / 依赖: IsIntegrallyClosed, IsIntegrallyClosed.minpoly.u, Polynomial, Polynomial.degree_ne_bot.mpr, WithBot, WithBot.le_of_add_le_add_left, add_zero, convert, degree, degree_le_zero_iff, degree_le_zero_iff.mp, degree_mul, degree_ne_bot, isIntegrallyClosed_dvd, le_of_add_le_add_left, minpoly, minpoly.aeval, minpoly.monic, minpoly.ne_zero, minpoly.ne_zero_iff.mp
-/
theorem IsIntegrallyClosed.isIntegral_iff_leadingCoeff_dvd {s : S} {p : R[X]} (hp : p.aeval s = 0)
    (h₀ : p != 0) (pmin : forall q : R[X], q.Monic -> q.aeval s = 0 -> p.degree <= q.degree) :
    IsIntegral R s ↔ C p.leadingCoeff ∣ p := by
  refine ⟨fun hInt => ?_, fun ⟨q, hMul⟩ => minpoly.ne_zero_iff.mp ?_⟩
  · use minpoly R s
    have ⟨q, hMul⟩ := isIntegrallyClosed_dvd hInt hp
    suffices q.degree <= 0 by simp [degree_le_zero_iff.mp this ▸ hMul, minpoly.monic hInt, mul_comm]
apply WithBot.le_of_add_le_add_left Polynomial.degree_ne_bot.mpr minpoly.ne_zero hInt
    convert! pmin _ (minpoly.monic hInt) (minpoly.aeval ..)
    · rw [hMul, degree_mul]
    · rw [add_zero]
· convert! right_ne_zero_of_mul hMul ▸ h₀
.symm refine IsIntegrallyClosed.minpoly.unique ?_ ?_ ?_
.symm · have := hMul ▸ leadingCoeff_mul ..
      simp only [leadingCoeff_C, ne_eq, leadingCoeff_eq_zero, h₀, not_false_eq_true, mul_eq_left₀]
        at this
      exact this
    · have := congrArg (Polynomial.aeval s) hMul
      simp only [hp, h₀, map_mul, aeval_C, zero_eq_mul, FaithfulSMul.algebraMap_eq_zero_iff,
        leadingCoeff_eq_zero, false_or] at this
      exact this
    · exact (hMul ▸ degree_C_mul <| by simp [h₀]) ▸ pmin

/--
theorem `prime_of_isIntegrallyClosed` / 定理 `prime_of_isIntegrallyClosed`

English:
theorem prime_of_isIntegrallyClosed
  given: {x : S} (hx : IsIntegral R x)
  statement: Prime (minpoly R x)
  proof: by
  refine
    ⟨(minpoly.monic hx).ne_zero,
      ⟨fun h_contra => (ne_of_lt (minpoly.degree_pos hx)) (degree_eq_zero_of_isUnit h_contra).symm,
        fun a b h => or_iff_not_imp_left.mpr fun h' => ?_⟩⟩
  rw [← minpoly.isIntegrallyClosed_dvd_iff hx] at h' h ⊢
  rw [aeval_mul] at h
  exact eq_zero_

中文:
定理 prime_of_is整数egrallyClosed
  条件: {x : S} (hx : 是整 R x)
  结论: 素 (minpoly R x)
  证明: by
  refine
    ⟨(minpoly.monic hx).ne_zero,
      ⟨fun h_contra => (ne_of_lt (minpoly.degree_pos hx)) (degree_eq_zero_of_isUnit h_contra).symm,
        fun a b h => or_iff_not_imp_left.mpr fun h' => ?_⟩⟩
  rw [← minpoly.isIntegrallyClosed_dvd_iff hx] at h' h ⊢
  rw [aeval_mul] at h
  exact eq_zero_

Depends on / 依赖: aeval_mul, degree_eq_zero_of_isUnit, degree_pos, eq_zero_of_ne_zero_of_mul_left_eq_zero, h_contra, isIntegrallyClosed_dvd_iff, minpoly, minpoly.degree_pos, minpoly.isIntegrallyClosed_dvd_iff, minpoly.monic, ne_of_lt, ne_zero, or_iff_not_imp_left, or_iff_not_imp_left.mpr
-/
theorem prime_of_isIntegrallyClosed {x : S} (hx : IsIntegral R x) : Prime (minpoly R x) := by
  refine
    ⟨(minpoly.monic hx).ne_zero,
      ⟨fun h_contra => (ne_of_lt (minpoly.degree_pos hx)) (degree_eq_zero_of_isUnit h_contra).symm,
        fun a b h => or_iff_not_imp_left.mpr fun h' => ?_⟩⟩
  rw [← minpoly.isIntegrallyClosed_dvd_iff hx] at h' h ⊢
  rw [aeval_mul] at h
  exact eq_zero_of_ne_zero_of_mul_left_eq_zero h' h

/--
lemma `_root_.IsIntegrallyClosed.minpoly_smul` / 引理 `_root_.IsIntegrallyClosed.minpoly_smul`

English:
lemma _root_.IsIntegrallyClosed.minpoly_smul
  given: {r : R} (hr : r != 0) {s : S} (hs : IsIntegral R s)
  proof: by
  let K := FractionRing R
  let L := FractionRing S
  let : Algebra K L := FractionRing.liftAlgebra _ _
  apply map_injective _ (FaithfulSMul.algebraMap_injective R K)
  rw [← minpoly.isIntegrallyClosed_eq_field_fractions K L (hs.smul r)]; rw [map_scaleRoots _ _ _ (by simpa [minpoly.ne_zero_iff])

中文:
引理 _root_.是整闭.minpoly_smul
  条件: {r : R} (hr : r != 0) {s : S} (hs : 是整 R s)
  证明: by
  let K := FractionRing R
  let L := FractionRing S
  let : Algebra K L := FractionRing.liftAlgebra _ _
  apply map_injective _ (FaithfulSMul.algebraMap_injective R K)
  rw [← minpoly.isIntegrallyClosed_eq_field_fractions K L (hs.smul r)]; rw [map_scaleRoots _ _ _ (by simpa [minpoly.ne_zero_iff])

Depends on / 依赖: Algebra, Algebra.smul_def, FaithfulSMul, FaithfulSMul.algebraMap_injective, FractionRing, FractionRing.liftAlgebra, IsScalarTower, IsScalarTower.algebraMap_apply, algebraMap_apply, algebraMap_injective, eq_of_monic_of_associated, hs.smul, isIntegrallyClosed_eq_field_fractions, liftAlgebra, map_injective, map_mul, map_scaleRoots, minpoly, minpoly.isIntegrallyClosed_eq_field_fractions, minpoly.mo
-/
lemma _root_.IsIntegrallyClosed.minpoly_smul {r : R} (hr : r != 0) {s : S} (hs : IsIntegral R s) :
    minpoly R (r • s) = (minpoly R s).scaleRoots r := by
  let K := FractionRing R
  let L := FractionRing S
  let : Algebra K L := FractionRing.liftAlgebra _ _
  apply map_injective _ (FaithfulSMul.algebraMap_injective R K)
  rw [← minpoly.isIntegrallyClosed_eq_field_fractions K L (hs.smul r)]; rw [map_scaleRoots _ _ _ (by simpa [minpoly.ne_zero_iff]),
    ← minpoly.isIntegrallyClosed_eq_field_fractions K L hs]
  simp_rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply R K L]
  refine eq_of_monic_of_associated (minpoly.monic ?_) ?_
    (associated_of_dvd_dvd (minpoly.dvd _ _ ?_) ?_)
  · refine isIntegral_algebraMap.mul (hs.map (IsScalarTower.toAlgHom R S L)).tower_top
  · simpa [monic_scaleRoots_iff] using minpoly.monic
      (hs.map (IsScalarTower.toAlgHom R S L)).tower_top
  · exact scaleRoots_aeval_eq_zero (minpoly.aeval _ _)
  · rw [← Polynomial.scaleRoots_dvd_iff _ _ (r := (algebraMap R K r)⁻¹) (IsUnit.mk0 _ (by simpa)),
      ← scaleRoots_mul, mul_inv_cancel₀ (by simpa), scaleRoots_one]
    refine minpoly.dvd _ _ ?_
    nth_rw 1 [← inv_mul_cancel_left₀ (b := algebraMap S L s)
      (a := algebraMap K L (algebraMap R K r)) (by simpa), ← map_inv₀]
    exact scaleRoots_aeval_eq_zero (minpoly.aeval _ _)

noncomputable section AdjoinRoot

open Algebra Polynomial AdjoinRoot

variable {x : S}

/--
theorem `ToAdjoin.injective` / 定理 `ToAdjoin.injective`

English:
theorem ToAdjoin.injective
  given: (hx : IsIntegral R x)
  statement: Function.Injective (Minpoly.toAdjoin R x)
  proof: by
  refine (injective_iff_map_eq_zero _).2 fun P₁ hP₁ => ?_
  obtain ⟨P, rfl⟩ := mk_surjective P₁
  simpa [← Subalgebra.coe_eq_zero, isIntegrallyClosed_dvd_iff hx, ← aeval_def] using hP₁

中文:
定理 ToAdjoin.injective
  条件: (hx : 是整 R x)
  结论: 函数.单射 (Minpoly.toAdjoin R x)
  证明: by
  refine (injective_iff_map_eq_zero _).2 fun P₁ hP₁ => ?_
  obtain ⟨P, rfl⟩ := mk_surjective P₁
  simpa [← Subalgebra.coe_eq_zero, isIntegrallyClosed_dvd_iff hx, ← aeval_def] using hP₁

Depends on / 依赖: Subalgebra, Subalgebra.coe_eq_zero, aeval_def, coe_eq_zero, injective_iff_map_eq_zero, isIntegrallyClosed_dvd_iff, mk_surjective
-/
theorem ToAdjoin.injective (hx : IsIntegral R x) : Function.Injective (Minpoly.toAdjoin R x) := by
  refine (injective_iff_map_eq_zero _).2 fun P₁ hP₁ => ?_
  obtain ⟨P, rfl⟩ := mk_surjective P₁
  simpa [← Subalgebra.coe_eq_zero, isIntegrallyClosed_dvd_iff hx, ← aeval_def] using hP₁

/--
Definition of `equivAdjoin` / `equivAdjoin` 的定义

English:
definition equivAdjoin
  signature: (hx : IsIntegral R x)
  body: AlgEquiv.ofBijective (Minpoly.toAdjoin R x)
    ⟨minpoly.ToAdjoin.injective hx, Minpoly.toAdjoin.surjective R x⟩

@[simp]

中文:
定义 equivAdjoin
  签名: (hx : 是整 R x)
  定义体: AlgEquiv.ofBijective (Minpoly.toAdjoin R x)
    ⟨minpoly.ToAdjoin.injective hx, Minpoly.toAdjoin.surjective R x⟩

@[simp]

Depends on / 依赖: AlgEquiv, AlgEquiv.ofBijective, Minpoly, Minpoly.toAdjoin, Minpoly.toAdjoin.surjective, ToAdjoin, injective, minpoly, minpoly.ToAdjoin.injective, ofBijective, surjective, toAdjoin
-/
def equivAdjoin (hx : IsIntegral R x) : AdjoinRoot (minpoly R x) ≃ₐ[R] adjoin R ({x} : Set S) :=
  AlgEquiv.ofBijective (Minpoly.toAdjoin R x)
    ⟨minpoly.ToAdjoin.injective hx, Minpoly.toAdjoin.surjective R x⟩

@[simp]
/--
theorem `equivAdjoin_toAlgHom` / 定理 `equivAdjoin_toAlgHom`

English:
theorem equivAdjoin_toAlgHom
  given: (hx : IsIntegral R x)
  statement: equivAdjoin hx = Minpoly.toAdjoin R x
  proof: rfl

@[simp]

中文:
定理 equivAdjoin_toAlgHom
  条件: (hx : 是整 R x)
  结论: equivAdjoin hx = Minpoly.toAdjoin R x
  证明: rfl

@[simp]
-/
theorem equivAdjoin_toAlgHom (hx : IsIntegral R x) : equivAdjoin hx = Minpoly.toAdjoin R x := rfl

@[simp]
/--
theorem `coe_equivAdjoin` / 定理 `coe_equivAdjoin`

English:
theorem coe_equivAdjoin
  given: (hx : IsIntegral R x)
  statement: ⇑(equivAdjoin hx) = Minpoly.toAdjoin R x
  proof: rfl

中文:
定理 coe_equivAdjoin
  条件: (hx : 是整 R x)
  结论: ⇑(equivAdjoin hx) = Minpoly.toAdjoin R x
  证明: rfl
-/
theorem coe_equivAdjoin (hx : IsIntegral R x) : ⇑(equivAdjoin hx) = Minpoly.toAdjoin R x := rfl

/--
Definition of `_root_.Algebra.adjoin.powerBasis'` / `_root_.Algebra.adjoin.powerBasis'` 的定义

English:
definition _root_.Algebra.adjoin.powerBasis'
  signature: (hx : IsIntegral R x)
  body: PowerBasis.map (AdjoinRoot.powerBasis' (minpoly.monic hx)) (minpoly.equivAdjoin hx)

@[simp]

中文:
定义 _root_.代数.adjoin.powerBasis'
  签名: (hx : 是整 R x)
  定义体: PowerBasis.map (AdjoinRoot.powerBasis' (minpoly.monic hx)) (minpoly.equivAdjoin hx)

@[simp]

Depends on / 依赖: AdjoinRoot, AdjoinRoot.powerBasis, PowerBasis, PowerBasis.map, equivAdjoin, minpoly, minpoly.equivAdjoin, minpoly.monic, powerBasis
-/
def _root_.Algebra.adjoin.powerBasis' (hx : IsIntegral R x) :
    PowerBasis R (Algebra.adjoin R ({x} : Set S)) :=
  PowerBasis.map (AdjoinRoot.powerBasis' (minpoly.monic hx)) (minpoly.equivAdjoin hx)

@[simp]
/--
theorem `_root_.Algebra.adjoin.powerBasis'_dim` / 定理 `_root_.Algebra.adjoin.powerBasis'_dim`

English:
theorem _root_.Algebra.adjoin.powerBasis'_dim
  given: (hx : IsIntegral R x)
  proof: rfl

中文:
定理 _root_.代数.adjoin.powerBasis'_dim
  条件: (hx : 是整 R x)
  证明: rfl
-/
theorem _root_.Algebra.adjoin.powerBasis'_dim (hx : IsIntegral R x) :
    (Algebra.adjoin.powerBasis' hx).dim = (minpoly R x).natDegree := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `_root_.Algebra.adjoin.powerBasis'_gen` / 定理 `_root_.Algebra.adjoin.powerBasis'_gen`

English:
theorem _root_.Algebra.adjoin.powerBasis'_gen
  given: (hx : IsIntegral R x)
  proof: by
  rw [Algebra.adjoin.powerBasis']; rw [PowerBasis.map_gen]; rw [AdjoinRoot.powerBasis'_gen]; rw [equivAdjoin]; rw [AlgEquiv.ofBijective_apply]; rw [Minpoly.toAdjoin]; rw [liftAlgHom_root]

中文:
定理 _root_.代数.adjoin.powerBasis'_gen
  条件: (hx : 是整 R x)
  证明: by
  rw [Algebra.adjoin.powerBasis']; rw [PowerBasis.map_gen]; rw [AdjoinRoot.powerBasis'_gen]; rw [equivAdjoin]; rw [AlgEquiv.ofBijective_apply]; rw [Minpoly.toAdjoin]; rw [liftAlgHom_root]
-/
theorem _root_.Algebra.adjoin.powerBasis'_gen (hx : IsIntegral R x) :
(adjoin.powerBasis' hx).gen = ⟨x, SetLike.mem_coe.1 subset_adjoin mem_singleton x⟩ := by
  rw [Algebra.adjoin.powerBasis']; rw [PowerBasis.map_gen]; rw [AdjoinRoot.powerBasis'_gen]; rw [equivAdjoin]; rw [AlgEquiv.ofBijective_apply]; rw [Minpoly.toAdjoin]; rw [liftAlgHom_root]

/--
Definition of `_root_.PowerBasis.ofAdjoinEqTop'` / `_root_.PowerBasis.ofAdjoinEqTop'` 的定义

English:
definition _root_.PowerBasis.ofAdjoinEqTop'
  signature: {x : S} (hx : IsIntegral R x)
  body: (adjoin.powerBasis' hx).map ((Subalgebra.equivOfEq _ _ hx').trans Subalgebra.topEquiv)

中文:
定义 _root_.PowerBasis.ofAdjoinEqTop'
  签名: {x : S} (hx : 是整 R x)
  定义体: (adjoin.powerBasis' hx).map ((Subalgebra.equivOfEq _ _ hx').trans Subalgebra.topEquiv)

Depends on / 依赖: Subalgebra, Subalgebra.equivOfEq, Subalgebra.topEquiv, adjoin, adjoin.powerBasis, equivOfEq, powerBasis, topEquiv
-/
noncomputable def _root_.PowerBasis.ofAdjoinEqTop' {x : S} (hx : IsIntegral R x)
    (hx' : adjoin R {x} = ⊤) :
    PowerBasis R S :=
  (adjoin.powerBasis' hx).map ((Subalgebra.equivOfEq _ _ hx').trans Subalgebra.topEquiv)

open Algebra in
example {x : S} (B : PowerBasis R S)
    (hint : IsIntegral R x) (hx : B.gen in R[x]) :
    PowerBasis R S := by
  apply PowerBasis.ofAdjoinEqTop' hint
  exact PowerBasis.adjoin_eq_top_of_gen_mem_adjoin hx

@[simp]
/--
theorem `_root_.PowerBasis.ofAdjoinEqTop'_dim` / 定理 `_root_.PowerBasis.ofAdjoinEqTop'_dim`

English:
theorem _root_.PowerBasis.ofAdjoinEqTop'_dim
  statement: {x : S} (hx : IsIntegral R x)
  proof: rfl

@[simp]

中文:
定理 _root_.PowerBasis.ofAdjoinEqTop'_dim
  结论: {x : S} (hx : 是整 R x)
  证明: rfl

@[simp]
-/
theorem _root_.PowerBasis.ofAdjoinEqTop'_dim {x : S} (hx : IsIntegral R x)
    (hx' : adjoin R {x} = ⊤) :
    (PowerBasis.ofAdjoinEqTop' hx hx').dim = (minpoly R x).natDegree := rfl

@[simp]
/--
theorem `_root_.PowerBasis.ofAdjoinEqTop'_gen` / 定理 `_root_.PowerBasis.ofAdjoinEqTop'_gen`

English:
theorem _root_.PowerBasis.ofAdjoinEqTop'_gen
  statement: {x : S} (hx : IsIntegral R x)
  proof: by
  simp [PowerBasis.ofAdjoinEqTop']

中文:
定理 _root_.PowerBasis.ofAdjoinEqTop'_gen
  结论: {x : S} (hx : 是整 R x)
  证明: by
  simp [PowerBasis.ofAdjoinEqTop']
-/
theorem _root_.PowerBasis.ofAdjoinEqTop'_gen {x : S} (hx : IsIntegral R x)
    (hx' : adjoin R {x} = ⊤) : (PowerBasis.ofAdjoinEqTop' hx hx').gen = x := by
  simp [PowerBasis.ofAdjoinEqTop']

end AdjoinRoot

section Subring

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

variable (A : Subring K) [IsIntegrallyClosed A] [IsFractionRing A K]

-- Implementation note: `inferInstance` does not work for these.
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra A (integralClosure A L)
  body: Subalgebra.algebra (integralClosure A L)

中文:
实例 :
  签名: 代数 A (integralClosure A L)
  定义体: Subalgebra.algebra (integralClosure A L)

Depends on / 依赖: Subalgebra, Subalgebra.algebra, algebra, integralClosure
-/
instance : Algebra A (integralClosure A L) := Subalgebra.algebra (integralClosure A L)
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul A (integralClosure A L)
  body: Algebra.toSMul

中文:
实例 :
  签名: 标量乘法 A (integralClosure A L)
  定义体: Algebra.toSMul

Depends on / 依赖: Algebra, Algebra.toSMul, toSMul
-/
instance : SMul A (integralClosure A L) := Algebra.toSMul
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsScalarTower A ((integralClosure A L)) L
  body: IsScalarTower.subalgebra' A L L (integralClosure A L)

中文:
实例 :
  签名: 标量塔 A ((integralClosure A L)) L
  定义体: IsScalarTower.subalgebra' A L L (integralClosure A L)

Depends on / 依赖: IsScalarTower, IsScalarTower.subalgebra, integralClosure, subalgebra
-/
instance : IsScalarTower A ((integralClosure A L)) L :=
  IsScalarTower.subalgebra' A L L (integralClosure A L)

/--
theorem `ofSubring` / 定理 `ofSubring`

English:
theorem ofSubring
  given: (x : integralClosure A L)
  proof: eq_comm.mpr (isIntegrallyClosed_eq_field_fractions K L (IsIntegralClosure.isIntegral A L x))

中文:
定理 ofSubring
  条件: (x : integralClosure A L)
  证明: eq_comm.mpr (isIntegrallyClosed_eq_field_fractions K L (IsIntegralClosure.isIntegral A L x))

Depends on / 依赖: IsIntegralClosure, IsIntegralClosure.isIntegral, eq_comm, eq_comm.mpr, isIntegral, isIntegrallyClosed_eq_field_fractions
-/
theorem ofSubring (x : integralClosure A L) :
    Polynomial.map (algebraMap A K) (minpoly A x) = minpoly K (x : L) :=
  eq_comm.mpr (isIntegrallyClosed_eq_field_fractions K L (IsIntegralClosure.isIntegral A L x))

end Subring

end minpoly
