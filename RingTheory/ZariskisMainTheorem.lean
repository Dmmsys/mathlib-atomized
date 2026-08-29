/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Algebraic.StronglyTranscendental
public import Mathlib.RingTheory.Conductor
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.RingTheory.IntegralClosure.GoingDown
public import Mathlib.RingTheory.Polynomial.IsIntegral
public import Mathlib.RingTheory.QuasiFinite.Polynomial
public import Mathlib.Algebra.Algebra.Shrink

/-!
# Algebraic Zariski's Main Theorem

The statement of Zariski's main theorem is the following:
Given a finite type `R`-algebra `S`, and `p` a prime of `S` such that `S` is quasi-finite at `R`,
then there exists a `f ∉ p` such that `S[1/f]` is isomorphic to `R'[1/f]` where `R'` is the integral
closure of `R` in `S`.

We follow https://stacks.math.columbia.edu/tag/00PI and proceed in the following steps

1. `Algebra.ZariskisMainProperty.of_adjoin_eq_top`:
  The case where `S = R[X]/I`.
  The key is `Polynomial.not_ker_le_map_C_of_surjective_of_quasiFiniteAt`
  which shows that there exists some `g ∈ I` such that some coefficient `gᵢ ∉ p`.
  Then one basically takes `f = gᵢ` and `g` becomes monic in `R[1/gᵢ][X]` up to some minor technical
  issues, and then `S[1/gᵢ]` is basically integral over `R[1/gᵢ]`.
2. `Algebra.ZariskisMainProperty.of_algHom_polynomial`:
  The case where `S` is finite over `R⟨x⟩` for some `x : S`.
  The following key results are first established:
  - `isStronglyTranscendental_mk_radical_conductor`:
    Let `𝔣` be the conductor of `x` (i.e. the largest `S`-ideal in `R⟨x⟩`).
    `x` as an element of `S/√𝔣` is strongly transcendental over `R`.
  - `Algebra.not_quasiFiniteAt_of_stronglyTranscendental`:
    If `S` is reduced, then `x : S` is not strongly transcendental over `R`.
    One first reduces to when `R ⊆ S` are domains, and then to when `R` is integrally closed.
    A going down theorem is now available, which could be applied to
    `Polynomial.map_under_lt_comap_of_quasiFiniteAt`:`(p ∩ R)[X] < p ∩ R<x>` to get a contradiction.

  The second result applied to `S/√𝔣` together with the first result implies that
  `p` does not contain `𝔣`.
  The claim then follows from `Localization.localRingHom_bijective_of_not_conductor_le`.
3. `Algebra.ZariskisMainProperty.of_algHom_mvPolynomial`:
  The case where `S` is finite over `R⟨x₁,...,xₙ⟩`. This is proved using induction on `n`.

## Main definition and results
- `Algebra.ZariskisMainProperty`:
  We say that an `R` algebra `S` satisfies the Zariski's main property at a prime `p` of `S`
  if there exists `r ∉ p` in the integral closure `S'` of `R` in `S`, such that `S'[1/r] = S[1/r]`.
- `Algebra.ZariskisMainProperty.of_finiteType`:
  If `S` is finite type over `R` and quasi-finite at `p`, then `ZariskisMainProperty` holds.
- `Algebra.QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective`:
  If `S` is finite type over `R` and quasi-finite at `p`,
  then there exists a subalgebra `S'` of `R` that is finitely generated as an `R`-module,
  and some `r ∈ S'` such that `r ∉ p` and `S'[1/r] = S[1/r]`.
-/

@[expose] public section

variable {R S T : Type*} [CommRing R] [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]

open scoped TensorProduct nonZeroDivisors

open Polynomial

namespace Algebra

variable (R) in
/--
Definition of `ZariskisMainProperty` / `ZariskisMainProperty` 的定义

English:
definition ZariskisMainProperty
  signature: (p : Ideal S)
  body: exists r : integralClosure R S, r.1 ∉ p ∧ Function.Bijective
    (Localization.awayMap (integralClosure R S).val.toRingHom r)

中文:
定义 ZariskisMainProperty
  签名: (p : 理想 S)
  定义体: exists r : integralClosure R S, r.1 ∉ p ∧ Function.Bijective
    (Localization.awayMap (integralClosure R S).val.toRingHom r)

Depends on / 依赖: Bijective, Function, Function.Bijective, Localization, Localization.awayMap, awayMap, integralClosure, toRingHom, val.toRingHom
-/
def ZariskisMainProperty (p : Ideal S) : Prop :=
  exists r : integralClosure R S, r.1 ∉ p ∧ Function.Bijective
    (Localization.awayMap (integralClosure R S).val.toRingHom r)

/--
lemma `zariskisMainProperty_iff` / 引理 `zariskisMainProperty_iff`

English:
lemma zariskisMainProperty_iff
  given: {p : Ideal S}
  proof: by
  simp only [ZariskisMainProperty, Subtype.exists, ← exists_prop, @exists_comm (_ ∉ p)]
  refine exists₃_congr fun r hr hrp => ?_
  rw [Function.Bijective]; rw [and_iff_right
    (by exact IsLocalization.map_injective_of_injective _ _ _ Subtype.val_injective)]; rw [Localization.awayMap_surjective_iff]
  simp [mem_integralClosure_iff]

中文:
引理 zariskisMainProperty_iff
  条件: {p : 理想 S}
  证明: by
  simp only [ZariskisMainProperty, Subtype.exists, ← exists_prop, @exists_comm (_ ∉ p)]
  refine exists₃_congr fun r hr hrp => ?_
  rw [Function.Bijective]; rw [and_iff_right
    (by exact IsLocalization.map_injective_of_injective _ _ _ Subtype.val_injective)]; rw [Localization.awayMap_surjective_iff]
  simp [mem_integralClosure_iff]

Depends on / 依赖: Bijective, Function, Function.Bijective, IsLocalization, IsLocalization.map_injective_of_injective, Localization, Localization.awayMap_surjective_iff, Subtype, Subtype.exists, Subtype.val_injective, ZariskisMainProperty, and_iff_right, awayMap_surjective_iff, exists_comm, exists_prop, map_injective_of_injective, mem_integralClosure_iff, val_injective
-/
lemma zariskisMainProperty_iff {p : Ideal S} :
    ZariskisMainProperty R p ↔ exists r ∉ p, IsIntegral R r ∧ forall x, exists m, IsIntegral R (r ^ m * x) := by
  simp only [ZariskisMainProperty, Subtype.exists, ← exists_prop, @exists_comm (_ ∉ p)]
  refine exists₃_congr fun r hr hrp => ?_
  rw [Function.Bijective]; rw [and_iff_right
    (by exact IsLocalization.map_injective_of_injective _ _ _ Subtype.val_injective)]; rw [Localization.awayMap_surjective_iff]
  simp [mem_integralClosure_iff]

/--
lemma `zariskisMainProperty_iff'` / 引理 `zariskisMainProperty_iff'`

English:
lemma zariskisMainProperty_iff'
  given: {p : Ideal S}
  proof: by
  refine zariskisMainProperty_iff.trans (exists_congr fun r => and_congr_right fun hrp =>
    and_iff_right_of_imp fun H => ?_)
  obtain ⟨n, hn⟩ := H r
  rw [← pow_succ] at hn
  exact (IsIntegral.pow_iff (by simp)).mp hn

中文:
引理 zariskisMainProperty_iff'
  条件: {p : 理想 S}
  证明: by
  refine zariskisMainProperty_iff.trans (exists_congr fun r => and_congr_right fun hrp =>
    and_iff_right_of_imp fun H => ?_)
  obtain ⟨n, hn⟩ := H r
  rw [← pow_succ] at hn
  exact (IsIntegral.pow_iff (by simp)).mp hn

Depends on / 依赖: IsIntegral, IsIntegral.pow_iff, and_congr_right, and_iff_right_of_imp, exists_congr, pow_iff, pow_succ, zariskisMainProperty_iff, zariskisMainProperty_iff.trans
-/
lemma zariskisMainProperty_iff' {p : Ideal S} :
    ZariskisMainProperty R p ↔ exists r ∉ p, forall x, exists m, IsIntegral R (r ^ m * x) := by
  refine zariskisMainProperty_iff.trans (exists_congr fun r => and_congr_right fun hrp =>
    and_iff_right_of_imp fun H => ?_)
  obtain ⟨n, hn⟩ := H r
  rw [← pow_succ] at hn
  exact (IsIntegral.pow_iff (by simp)).mp hn

/--
lemma `zariskisMainProperty_iff_exists_saturation_eq_top` / 引理 `zariskisMainProperty_iff_exists_saturation_eq_top`

English:
lemma zariskisMainProperty_iff_exists_saturation_eq_top
  given: {p : Ideal S}
  proof: by
  simp [zariskisMainProperty_iff, ← top_le_iff, SetLike.le_def,
    Submonoid.mem_powers_iff, mem_integralClosure_iff]

中文:
引理 zariskisMainProperty_iff_存在_saturation_eq_top
  条件: {p : 理想 S}
  证明: by
  simp [zariskisMainProperty_iff, ← top_le_iff, SetLike.le_def,
    Submonoid.mem_powers_iff, mem_integralClosure_iff]

Depends on / 依赖: SetLike, SetLike.le_def, Submonoid, Submonoid.mem_powers_iff, le_def, mem_integralClosure_iff, mem_powers_iff, top_le_iff, zariskisMainProperty_iff
-/
lemma zariskisMainProperty_iff_exists_saturation_eq_top {p : Ideal S} :
    ZariskisMainProperty R p ↔ exists r ∉ p, exists h : IsIntegral R r,
      (integralClosure R S).saturation (.powers r) (by simpa [Submonoid.powers_le]) = ⊤ := by
  simp [zariskisMainProperty_iff, ← top_le_iff, SetLike.le_def,
    Submonoid.mem_powers_iff, mem_integralClosure_iff]

/--
lemma `ZariskisMainProperty.restrictScalars` / 引理 `ZariskisMainProperty.restrictScalars`

English:
lemma ZariskisMainProperty.restrictScalars
  statement: [Algebra S T] [IsScalarTower R S T]
  proof: by
  rw [zariskisMainProperty_iff'] at H ⊢
  obtain ⟨r, hrp, H⟩ := H
  exact ⟨r, hrp, fun x => ⟨_, isIntegral_trans _ (H x).choose_spec⟩⟩

中文:
引理 ZariskisMainProperty.restrictScalars
  结论: [代数 S T] [标量塔 R S T]
  证明: by
  rw [zariskisMainProperty_iff'] at H ⊢
  obtain ⟨r, hrp, H⟩ := H
  exact ⟨r, hrp, fun x => ⟨_, isIntegral_trans _ (H x).choose_spec⟩⟩

Depends on / 依赖: choose_spec, isIntegral_trans, zariskisMainProperty_iff
-/
lemma ZariskisMainProperty.restrictScalars [Algebra S T] [IsScalarTower R S T]
    [Algebra.IsIntegral R S] {p : Ideal T} (H : ZariskisMainProperty S p) :
    ZariskisMainProperty R p := by
  rw [zariskisMainProperty_iff'] at H ⊢
  obtain ⟨r, hrp, H⟩ := H
  exact ⟨r, hrp, fun x => ⟨_, isIntegral_trans _ (H x).choose_spec⟩⟩

/--
lemma `ZariskisMainProperty.trans` / 引理 `ZariskisMainProperty.trans`

English:
lemma ZariskisMainProperty.trans
  statement: [Algebra S T] [IsScalarTower R S T] (p : Ideal T) [p.IsPrime]
  proof: by
  rw [zariskisMainProperty_iff] at h₁
  rw [zariskisMainProperty_iff']
  obtain ⟨s, hsp, hs, Hs⟩ := h₁
  obtain ⟨t, htp, Ht⟩ := h₂
  obtain ⟨m, hm⟩ := Hs t
  refine ⟨algebraMap _ _ (s ^ (m + 1) * t), ?_, fun x => ?_⟩
  · simpa using ‹p.IsPrime›.mul_notMem
      (mt ((inferInstance : (p.under S).IsPrime).mem_of_pow_mem (m + 1)) hsp) htp
  obtain ⟨_, ⟨n, rfl⟩, a, ha⟩ := Ht.ge (Set.mem_univ x)
  obtain ⟨k, hk⟩ := Hs a
  refine ⟨k + n, ?_⟩
  convert_to IsIntegral R (algebraMap S T ((s ^ ((m + 1) * n) * (s ^ m * t) ^ k * (s ^ k * a))))
  · simp only [AlgHom.toRingHom_eq_coe, Algebra.toRingHom_ofId] at ha
    simp only [map_pow, map_mul, ha, pow_add, mul_pow]
    ring
  · exact .algebraMap (.mul ((hs.pow _).mul (hm.pow _)) hk)

中文:
引理 ZariskisMainProperty.trans
  结论: [代数 S T] [标量塔 R S T] (p : 理想 T) [p.是素]
  证明: by
  rw [zariskisMainProperty_iff] at h₁
  rw [zariskisMainProperty_iff']
  obtain ⟨s, hsp, hs, Hs⟩ := h₁
  obtain ⟨t, htp, Ht⟩ := h₂
  obtain ⟨m, hm⟩ := Hs t
  refine ⟨algebraMap _ _ (s ^ (m + 1) * t), ?_, fun x => ?_⟩
  · simpa using ‹p.IsPrime›.mul_notMem
      (mt ((inferInstance : (p.under S).IsPrime).mem_of_pow_mem (m + 1)) hsp) htp
  obtain ⟨_, ⟨n, rfl⟩, a, ha⟩ := Ht.ge (Set.mem_univ x)
  obtain ⟨k, hk⟩ := Hs a
  refine ⟨k + n, ?_⟩
  convert_to IsIntegral R (algebraMap S T ((s ^ ((m + 1) * n) * (s ^ m * t) ^ k * (s ^ k * a))))
  · simp only [AlgHom.toRingHom_eq_coe, Algebra.toRingHom_ofId] at ha
    simp only [map_pow, map_mul, ha, pow_add, mul_pow]
    ring
  · exact .algebraMap (.mul ((hs.pow _).mul (hm.pow _)) hk)

Depends on / 依赖: Ht.ge, IsIntegral, IsPrime, Set.mem_univ, algebraMap, convert_to, mem_of_pow_mem, mem_univ, mul_notMem, p.IsPrime, p.under, zariskisMainProperty_iff
-/
lemma ZariskisMainProperty.trans [Algebra S T] [IsScalarTower R S T] (p : Ideal T) [p.IsPrime]
    (h₁ : ZariskisMainProperty R (p.under S))
    (h₂ : exists r ∉ p.under S, (⊥ : Subalgebra S T).saturation (.powers (algebraMap _ _ r))
      (by simp [Submonoid.powers_le]) = ⊤) :
    ZariskisMainProperty R p := by
  rw [zariskisMainProperty_iff] at h₁
  rw [zariskisMainProperty_iff']
  obtain ⟨s, hsp, hs, Hs⟩ := h₁
  obtain ⟨t, htp, Ht⟩ := h₂
  obtain ⟨m, hm⟩ := Hs t
  refine ⟨algebraMap _ _ (s ^ (m + 1) * t), ?_, fun x => ?_⟩
  · simpa using ‹p.IsPrime›.mul_notMem
      (mt ((inferInstance : (p.under S).IsPrime).mem_of_pow_mem (m + 1)) hsp) htp
  obtain ⟨_, ⟨n, rfl⟩, a, ha⟩ := Ht.ge (Set.mem_univ x)
  obtain ⟨k, hk⟩ := Hs a
  refine ⟨k + n, ?_⟩
  convert_to IsIntegral R (algebraMap S T ((s ^ ((m + 1) * n) * (s ^ m * t) ^ k * (s ^ k * a))))
  · simp only [AlgHom.toRingHom_eq_coe, Algebra.toRingHom_ofId] at ha
    simp only [map_pow, map_mul, ha, pow_add, mul_pow]
    ring
  · exact .algebraMap (.mul ((hs.pow _).mul (hm.pow _)) hk)

/--
lemma `ZariskisMainProperty.of_isIntegral` / 引理 `ZariskisMainProperty.of_isIntegral`

English:
lemma ZariskisMainProperty.of_isIntegral
  given: (p : Ideal S) [p.IsPrime] [Algebra.IsIntegral R S]
  proof: zariskisMainProperty_iff'.mpr ⟨1, p.primeCompl.one_mem,
    fun _ => ⟨0, Algebra.IsIntegral.isIntegral _⟩⟩

中文:
引理 ZariskisMainProperty.of_is整数egral
  条件: (p : 理想 S) [p.是素] [代数.是整 R S]
  证明: zariskisMainProperty_iff'.mpr ⟨1, p.primeCompl.one_mem,
    fun _ => ⟨0, Algebra.IsIntegral.isIntegral _⟩⟩

Depends on / 依赖: Algebra, Algebra.IsIntegral.isIntegral, IsIntegral, isIntegral, one_mem, p.primeCompl.one_mem, primeCompl, zariskisMainProperty_iff
-/
lemma ZariskisMainProperty.of_isIntegral (p : Ideal S) [p.IsPrime] [Algebra.IsIntegral R S] :
    ZariskisMainProperty R p :=
  zariskisMainProperty_iff'.mpr ⟨1, p.primeCompl.one_mem,
    fun _ => ⟨0, Algebra.IsIntegral.isIntegral _⟩⟩

end Algebra

section IsStronglyTranscendental

variable (φ : R[X] ->ₐ[R] S) (t : S) (p r : R[X])

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `isIntegral_of_isIntegralElem_of_monic_of_natDegree_lt` / 引理 `isIntegral_of_isIntegralElem_of_monic_of_natDegree_lt`

English:
lemma isIntegral_of_isIntegralElem_of_monic_of_natDegree_lt
  proof: by
  let St := Localization.Away t
  let t' : St := IsLocalization.Away.invSelf t
  have ht't : t' * algebraMap S St t = 1 := by rw [mul_comm, IsLocalization.Away.mul_invSelf]
  let R₁ := Algebra.adjoin R {t'}
  let R₂ := Algebra.adjoin R₁ {algebraMap S St (φ X)}
  let : Algebra R₁ R₂ := R₂.algebra
  let : Algebra R₂ St := R₂.toAlgebra
  let : Algebra R₁ St := R₁.toAlgebra
  have : IsScalarTower R₁ R₂ St := Subalgebra.isScalarTower_mid _
  have : Algebra.IsIntegral R₁ R₂ := by
    cases subsingleton_or_nontrivial R₁
    · have := (algebraMap R₁ R₂).codomain_trivial; exact ⟨(Subsingleton.elim · 0 ▸ isIntegral_zero)⟩
    rw [← le_integralClosure_iff_isIntegral]; rw [Algebra.adjoin_le_iff]; rw [Set.singleton_subset_iff]; rw [SetLike.mem_coe]; rw [mem_integralClosure_iff]
    refine ⟨p.map (algebraMap R R₁) - C ⟨t', Algebra.self_mem_adjoin_singleton R t'⟩ *
        r.map (algebraMap R R₁), (hpm.map _).sub_of_left (degree_lt_degree ?_), ?_⟩
    · grw [natDegree_C_mul_le, natDegree_map_le, hpm.natDegree_map]; assumption
    · simp [← aeval_def, aeval_algebraMap_apply, aeval_algHom_apply,
        ← hp, ← mul_assoc, ht't, mul_right_comm]
  have : IsIntegral R₁ (algebraMap S St t) := by
    refine isIntegral_trans (A := R₂) (algebraMap S St t) ?_
    obtain ⟨q, hq, hq'⟩ := ht
    refine ⟨q.map (aeval ⟨_, Algebra.self_mem_adjoin_singleton _ _⟩).toRingHom, hq.map _, ?_⟩
    rw [AlgHom.toRingHom_eq_coe]; rw [eval₂_map]; rw [← map_zero (algebraMap S St)]; rw [← hq']; rw [hom_eval₂]
    congr 1
    ext <;> simp [-Polynomial.algebraMap_apply, ← algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  simpa using IsLocalization.Away.isIntegral_of_isIntegral_map t
    (isIntegral_of_isIntegral_adjoin_of_mul_eq_one _ _ ht't this)

@[stacks 00PT]

中文:
引理 is整数egral_of_is整数egralElem_of_monic_of_natDegree_lt
  证明: by
  let St := Localization.Away t
  let t' : St := IsLocalization.Away.invSelf t
  have ht't : t' * algebraMap S St t = 1 := by rw [mul_comm, IsLocalization.Away.mul_invSelf]
  let R₁ := Algebra.adjoin R {t'}
  let R₂ := Algebra.adjoin R₁ {algebraMap S St (φ X)}
  let : Algebra R₁ R₂ := R₂.algebra
  let : Algebra R₂ St := R₂.toAlgebra
  let : Algebra R₁ St := R₁.toAlgebra
  have : IsScalarTower R₁ R₂ St := Subalgebra.isScalarTower_mid _
  have : Algebra.IsIntegral R₁ R₂ := by
    cases subsingleton_or_nontrivial R₁
    · have := (algebraMap R₁ R₂).codomain_trivial; exact ⟨(Subsingleton.elim · 0 ▸ isIntegral_zero)⟩
    rw [← le_integralClosure_iff_isIntegral]; rw [Algebra.adjoin_le_iff]; rw [Set.singleton_subset_iff]; rw [SetLike.mem_coe]; rw [mem_integralClosure_iff]
    refine ⟨p.map (algebraMap R R₁) - C ⟨t', Algebra.self_mem_adjoin_singleton R t'⟩ *
        r.map (algebraMap R R₁), (hpm.map _).sub_of_left (degree_lt_degree ?_), ?_⟩
    · grw [natDegree_C_mul_le, natDegree_map_le, hpm.natDegree_map]; assumption
    · simp [← aeval_def, aeval_algebraMap_apply, aeval_algHom_apply,
        ← hp, ← mul_assoc, ht't, mul_right_comm]
  have : IsIntegral R₁ (algebraMap S St t) := by
    refine isIntegral_trans (A := R₂) (algebraMap S St t) ?_
    obtain ⟨q, hq, hq'⟩ := ht
    refine ⟨q.map (aeval ⟨_, Algebra.self_mem_adjoin_singleton _ _⟩).toRingHom, hq.map _, ?_⟩
    rw [AlgHom.toRingHom_eq_coe]; rw [eval₂_map]; rw [← map_zero (algebraMap S St)]; rw [← hq']; rw [hom_eval₂]
    congr 1
    ext <;> simp [-Polynomial.algebraMap_apply, ← algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  simpa using IsLocalization.Away.isIntegral_of_isIntegral_map t
    (isIntegral_of_isIntegral_adjoin_of_mul_eq_one _ _ ht't this)

@[stacks 00PT]

Depends on / 依赖: Algebra, Algebra.IsIntegral, Algebra.adjoin, IsIntegral, IsLocalization, IsLocalization.Away.invSelf, IsLocalization.Away.mul_invSelf, IsScalarTower, Localization, Localization.Away, Subalgebra, Subalgebra.isScalarTower_mid, adjoin, algebra, algebraMap, invSelf, isScalarTower_mid, mul_comm, mul_invSelf, subsingleton_or_nontrivial
-/
lemma isIntegral_of_isIntegralElem_of_monic_of_natDegree_lt
    (ht : φ.IsIntegralElem t) (hpm : p.Monic)
    (hpr : r.natDegree < p.natDegree) (hp : φ p * t = φ r) : IsIntegral R t := by
  let St := Localization.Away t
  let t' : St := IsLocalization.Away.invSelf t
  have ht't : t' * algebraMap S St t = 1 := by rw [mul_comm, IsLocalization.Away.mul_invSelf]
  let R₁ := Algebra.adjoin R {t'}
  let R₂ := Algebra.adjoin R₁ {algebraMap S St (φ X)}
  let : Algebra R₁ R₂ := R₂.algebra
  let : Algebra R₂ St := R₂.toAlgebra
  let : Algebra R₁ St := R₁.toAlgebra
  have : IsScalarTower R₁ R₂ St := Subalgebra.isScalarTower_mid _
  have : Algebra.IsIntegral R₁ R₂ := by
    cases subsingleton_or_nontrivial R₁
    · have := (algebraMap R₁ R₂).codomain_trivial; exact ⟨(Subsingleton.elim · 0 ▸ isIntegral_zero)⟩
    rw [← le_integralClosure_iff_isIntegral]; rw [Algebra.adjoin_le_iff]; rw [Set.singleton_subset_iff]; rw [SetLike.mem_coe]; rw [mem_integralClosure_iff]
    refine ⟨p.map (algebraMap R R₁) - C ⟨t', Algebra.self_mem_adjoin_singleton R t'⟩ *
        r.map (algebraMap R R₁), (hpm.map _).sub_of_left (degree_lt_degree ?_), ?_⟩
    · grw [natDegree_C_mul_le, natDegree_map_le, hpm.natDegree_map]; assumption
    · simp [← aeval_def, aeval_algebraMap_apply, aeval_algHom_apply,
        ← hp, ← mul_assoc, ht't, mul_right_comm]
  have : IsIntegral R₁ (algebraMap S St t) := by
    refine isIntegral_trans (A := R₂) (algebraMap S St t) ?_
    obtain ⟨q, hq, hq'⟩ := ht
    refine ⟨q.map (aeval ⟨_, Algebra.self_mem_adjoin_singleton _ _⟩).toRingHom, hq.map _, ?_⟩
    rw [AlgHom.toRingHom_eq_coe]; rw [eval₂_map]; rw [← map_zero (algebraMap S St)]; rw [← hq']; rw [hom_eval₂]
    congr 1
    ext <;> simp [-Polynomial.algebraMap_apply, ← algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  simpa using IsLocalization.Away.isIntegral_of_isIntegral_map t
    (isIntegral_of_isIntegral_adjoin_of_mul_eq_one _ _ ht't this)

@[stacks 00PT]
/--
lemma `exists_isIntegral_sub_of_isIntegralElem_of_mul_mem_range` / 引理 `exists_isIntegral_sub_of_isIntegralElem_of_mul_mem_range`

English:
lemma exists_isIntegral_sub_of_isIntegralElem_of_mul_mem_range
  proof: by
  obtain ⟨r, hr : φ r = _⟩ := hp
  obtain rfl | hp1 := eq_or_ne p 1
  · exact ⟨r, by simp_all [isIntegral_zero]⟩
  exact ⟨_, isIntegral_of_isIntegralElem_of_monic_of_natDegree_lt φ (t - φ (r /ₘ p)) p (r %ₘ p)
    (ht.sub _ φ.isIntegralElem_map) hpm (natDegree_modByMonic_lt _ hpm hp1)
    (by simp [mul_sub, ← hr, sub_eq_iff_eq_add, ← map_mul, ← map_add, r.modByMonic_add_div])⟩

中文:
引理 存在_is整数egral_sub_of_is整数egralElem_of_mul_mem_range
  证明: by
  obtain ⟨r, hr : φ r = _⟩ := hp
  obtain rfl | hp1 := eq_or_ne p 1
  · exact ⟨r, by simp_all [isIntegral_zero]⟩
  exact ⟨_, isIntegral_of_isIntegralElem_of_monic_of_natDegree_lt φ (t - φ (r /ₘ p)) p (r %ₘ p)
    (ht.sub _ φ.isIntegralElem_map) hpm (natDegree_modByMonic_lt _ hpm hp1)
    (by simp [mul_sub, ← hr, sub_eq_iff_eq_add, ← map_mul, ← map_add, r.modByMonic_add_div])⟩

Depends on / 依赖: eq_or_ne, ht.sub, isIntegralElem_map, isIntegral_of_isIntegralElem_of_monic_of_natDegree_lt, isIntegral_zero, map_add, map_mul, modByMonic_add_div, mul_sub, natDegree_modByMonic_lt, r.modByMonic_add_div, sub_eq_iff_eq_add
-/
lemma exists_isIntegral_sub_of_isIntegralElem_of_mul_mem_range
    (ht : φ.IsIntegralElem t) (hpm : p.Monic) (hp : φ p * t in φ.range) :
    exists q, IsIntegral R (t - φ q) := by
  obtain ⟨r, hr : φ r = _⟩ := hp
  obtain rfl | hp1 := eq_or_ne p 1
  · exact ⟨r, by simp_all [isIntegral_zero]⟩
  exact ⟨_, isIntegral_of_isIntegralElem_of_monic_of_natDegree_lt φ (t - φ (r /ₘ p)) p (r %ₘ p)
    (ht.sub _ φ.isIntegralElem_map) hpm (natDegree_modByMonic_lt _ hpm hp1)
    (by simp [mul_sub, ← hr, sub_eq_iff_eq_add, ← map_mul, ← map_add, r.modByMonic_add_div])⟩

open IsScalarTower in
attribute [local simp] IsLocalization.map_eq aeval_algebraMap_apply aeval_algHom_apply in
@[stacks 00PV]
/--
lemma `exists_isIntegral_leadingCoeff_pow_smul_sub_of_isIntegralElem_of_mul_mem_range` / 引理 `exists_isIntegral_leadingCoeff_pow_smul_sub_of_isIntegralElem_of_mul_mem_range`

English:
lemma exists_isIntegral_leadingCoeff_pow_smul_sub_of_isIntegralElem_of_mul_mem_range
  proof: by
  set a := p.leadingCoeff
  let R' := Localization.Away a
  let S' := Localization.Away (algebraMap R S a)
  let : Algebra R' S' := (Localization.awayMap (algebraMap R S) a).toAlgebra
  have : IsScalarTower R R' S' := .of_algebraMap_eq (by
    simp +zetaDelta [RingHom.algebraMap_toAlgebra, IsLocalization.Away.map, ← algebraMap_apply R S])
  have ha : IsUnit (algebraMap R R' a) := IsLocalization.Away.algebraMap_isUnit a
  have H : (aeval ((algebraMap S S') (φ X))).toRingHom.comp (mapRingHom (algebraMap R R')) =
    (algebraMap S S').comp φ := by ext <;>
      simp [-Polynomial.algebraMap_apply, ← Polynomial.algebraMap_eq, ← algebraMap_apply]
  obtain ⟨q, hq⟩ := exists_isIntegral_sub_of_isIntegralElem_of_mul_mem_range (R := R')
    (aeval (algebraMap S S' (φ X))) (algebraMap S S' t) (C ha.unit⁻¹.1 * p.map (algebraMap _ _)) (by
      obtain ⟨q, hqm, hq⟩ := ht
      refine ⟨q.map (mapRingHom (algebraMap _ _)), hqm.map _, ?_⟩
      rw [eval₂_map]; rw [H]; rw [← hom_eval₂]; rw [← AlgHom.toRingHom_eq_coe]; rw [hq]; rw [map_zero]) (by
      nontriviality R'
      simp [Monic, leadingCoeff_C_mul_of_isUnit,
        leadingCoeff_map_of_leadingCoeff_ne_zero _ ha.ne_zero, a]) (by
      obtain ⟨r, hr : φ r = _⟩ := hp
      use C ha.unit⁻¹.1 * mapRingHom (algebraMap R R') r
      simp [aeval_algebraMap_apply, aeval_algHom_apply, hr, mul_assoc])
  obtain ⟨_, ⟨n, rfl⟩, e⟩ := IsLocalization.integerNormalization_spec (.powers a) q
  generalize IsLocalization.integerNormalization (.powers a) q = q' at e
  have : IsIntegral R' ((algebraMap S S') (a ^ n • t - φ q')) := by
    have : algebraMap S S' (φ q') = (algebraMap R S' a) ^ n * aeval (algebraMap S S' (φ X)) q := by
      simpa [Algebra.smul_def, aeval_algebraMap_apply, aeval_algHom_apply, ← algebraMap_apply] using
        congr(aeval (algebraMap S S' (φ X)) $e)
    simpa [Algebra.smul_def, ← mul_sub, ← algebraMap_apply, this] using
      (isIntegral_algebraMap (A := S') (x := algebraMap R R' a ^ n)).mul hq
  obtain ⟨⟨_, m, rfl⟩, hm⟩ := this.exists_multiple_integral_of_isLocalization (.powers a) _
  simp only [Algebra.smul_def, Submonoid.smul_def, algebraMap_apply R S S', ← map_mul] at hm
  obtain ⟨_, ⟨k, rfl⟩, hk⟩ := IsLocalization.exists_isIntegral_smul_of_isIntegral_map (.powers a) hm
  refine ⟨C a ^ (k + m) * q', k + m + n, ?_⟩
  convert! hk using 1
  simp only [Algebra.smul_def, map_pow, ← Polynomial.algebraMap_eq, map_mul, AlgHom.commutes]
  ring

@[stacks 00PX]

中文:
引理 存在_is整数egral_leadingCoeff_pow_smul_sub_of_is整数egralElem_of_mul_mem_range
  证明: by
  set a := p.leadingCoeff
  let R' := Localization.Away a
  let S' := Localization.Away (algebraMap R S a)
  let : Algebra R' S' := (Localization.awayMap (algebraMap R S) a).toAlgebra
  have : IsScalarTower R R' S' := .of_algebraMap_eq (by
    simp +zetaDelta [RingHom.algebraMap_toAlgebra, IsLocalization.Away.map, ← algebraMap_apply R S])
  have ha : IsUnit (algebraMap R R' a) := IsLocalization.Away.algebraMap_isUnit a
  have H : (aeval ((algebraMap S S') (φ X))).toRingHom.comp (mapRingHom (algebraMap R R')) =
    (algebraMap S S').comp φ := by ext <;>
      simp [-Polynomial.algebraMap_apply, ← Polynomial.algebraMap_eq, ← algebraMap_apply]
  obtain ⟨q, hq⟩ := exists_isIntegral_sub_of_isIntegralElem_of_mul_mem_range (R := R')
    (aeval (algebraMap S S' (φ X))) (algebraMap S S' t) (C ha.unit⁻¹.1 * p.map (algebraMap _ _)) (by
      obtain ⟨q, hqm, hq⟩ := ht
      refine ⟨q.map (mapRingHom (algebraMap _ _)), hqm.map _, ?_⟩
      rw [eval₂_map]; rw [H]; rw [← hom_eval₂]; rw [← AlgHom.toRingHom_eq_coe]; rw [hq]; rw [map_zero]) (by
      nontriviality R'
      simp [Monic, leadingCoeff_C_mul_of_isUnit,
        leadingCoeff_map_of_leadingCoeff_ne_zero _ ha.ne_zero, a]) (by
      obtain ⟨r, hr : φ r = _⟩ := hp
      use C ha.unit⁻¹.1 * mapRingHom (algebraMap R R') r
      simp [aeval_algebraMap_apply, aeval_algHom_apply, hr, mul_assoc])
  obtain ⟨_, ⟨n, rfl⟩, e⟩ := IsLocalization.integerNormalization_spec (.powers a) q
  generalize IsLocalization.integerNormalization (.powers a) q = q' at e
  have : IsIntegral R' ((algebraMap S S') (a ^ n • t - φ q')) := by
    have : algebraMap S S' (φ q') = (algebraMap R S' a) ^ n * aeval (algebraMap S S' (φ X)) q := by
      simpa [Algebra.smul_def, aeval_algebraMap_apply, aeval_algHom_apply, ← algebraMap_apply] using
        congr(aeval (algebraMap S S' (φ X)) $e)
    simpa [Algebra.smul_def, ← mul_sub, ← algebraMap_apply, this] using
      (isIntegral_algebraMap (A := S') (x := algebraMap R R' a ^ n)).mul hq
  obtain ⟨⟨_, m, rfl⟩, hm⟩ := this.exists_multiple_integral_of_isLocalization (.powers a) _
  simp only [Algebra.smul_def, Submonoid.smul_def, algebraMap_apply R S S', ← map_mul] at hm
  obtain ⟨_, ⟨k, rfl⟩, hk⟩ := IsLocalization.exists_isIntegral_smul_of_isIntegral_map (.powers a) hm
  refine ⟨C a ^ (k + m) * q', k + m + n, ?_⟩
  convert! hk using 1
  simp only [Algebra.smul_def, map_pow, ← Polynomial.algebraMap_eq, map_mul, AlgHom.commutes]
  ring

@[stacks 00PX]

Depends on / 依赖: Algebra, IsLocalization, IsLocalization.Away.algebraMap_isUnit, IsLocalization.Away.map, IsScalarTower, IsUnit, Localization, Localization.Away, Localization.awayMap, RingHom, RingHom.algebraMap_toAlgebra, algebraMap, algebraMap_apply, algebraMap_isUnit, algebraMap_toAlgebra, awayMap, leadingCoeff, mapRingHom, of_algebraMap_eq, p.leadingCoeff
-/
lemma exists_isIntegral_leadingCoeff_pow_smul_sub_of_isIntegralElem_of_mul_mem_range
    (ht : φ.IsIntegralElem t) (hp : φ p * t in φ.range) :
    exists q n, IsIntegral R (p.leadingCoeff ^ n • t - φ q) := by
  set a := p.leadingCoeff
  let R' := Localization.Away a
  let S' := Localization.Away (algebraMap R S a)
  let : Algebra R' S' := (Localization.awayMap (algebraMap R S) a).toAlgebra
  have : IsScalarTower R R' S' := .of_algebraMap_eq (by
    simp +zetaDelta [RingHom.algebraMap_toAlgebra, IsLocalization.Away.map, ← algebraMap_apply R S])
  have ha : IsUnit (algebraMap R R' a) := IsLocalization.Away.algebraMap_isUnit a
  have H : (aeval ((algebraMap S S') (φ X))).toRingHom.comp (mapRingHom (algebraMap R R')) =
    (algebraMap S S').comp φ := by ext <;>
      simp [-Polynomial.algebraMap_apply, ← Polynomial.algebraMap_eq, ← algebraMap_apply]
  obtain ⟨q, hq⟩ := exists_isIntegral_sub_of_isIntegralElem_of_mul_mem_range (R := R')
    (aeval (algebraMap S S' (φ X))) (algebraMap S S' t) (C ha.unit⁻¹.1 * p.map (algebraMap _ _)) (by
      obtain ⟨q, hqm, hq⟩ := ht
      refine ⟨q.map (mapRingHom (algebraMap _ _)), hqm.map _, ?_⟩
      rw [eval₂_map]; rw [H]; rw [← hom_eval₂]; rw [← AlgHom.toRingHom_eq_coe]; rw [hq]; rw [map_zero]) (by
      nontriviality R'
      simp [Monic, leadingCoeff_C_mul_of_isUnit,
        leadingCoeff_map_of_leadingCoeff_ne_zero _ ha.ne_zero, a]) (by
      obtain ⟨r, hr : φ r = _⟩ := hp
      use C ha.unit⁻¹.1 * mapRingHom (algebraMap R R') r
      simp [aeval_algebraMap_apply, aeval_algHom_apply, hr, mul_assoc])
  obtain ⟨_, ⟨n, rfl⟩, e⟩ := IsLocalization.integerNormalization_spec (.powers a) q
  generalize IsLocalization.integerNormalization (.powers a) q = q' at e
  have : IsIntegral R' ((algebraMap S S') (a ^ n • t - φ q')) := by
    have : algebraMap S S' (φ q') = (algebraMap R S' a) ^ n * aeval (algebraMap S S' (φ X)) q := by
      simpa [Algebra.smul_def, aeval_algebraMap_apply, aeval_algHom_apply, ← algebraMap_apply] using
        congr(aeval (algebraMap S S' (φ X)) $e)
    simpa [Algebra.smul_def, ← mul_sub, ← algebraMap_apply, this] using
      (isIntegral_algebraMap (A := S') (x := algebraMap R R' a ^ n)).mul hq
  obtain ⟨⟨_, m, rfl⟩, hm⟩ := this.exists_multiple_integral_of_isLocalization (.powers a) _
  simp only [Algebra.smul_def, Submonoid.smul_def, algebraMap_apply R S S', ← map_mul] at hm
  obtain ⟨_, ⟨k, rfl⟩, hk⟩ := IsLocalization.exists_isIntegral_smul_of_isIntegral_map (.powers a) hm
  refine ⟨C a ^ (k + m) * q', k + m + n, ?_⟩
  convert! hk using 1
  simp only [Algebra.smul_def, map_pow, ← Polynomial.algebraMap_eq, map_mul, AlgHom.commutes]
  ring

@[stacks 00PX]
/--
lemma `exists_leadingCoeff_pow_smul_mem_conductor` / 引理 `exists_leadingCoeff_pow_smul_mem_conductor`

English:
lemma exists_leadingCoeff_pow_smul_mem_conductor
  proof: by
  algebraize [φ.toRingHom]
  have : IsScalarTower R R[X] S := .of_algebraMap_eq' φ.comp_algebraMap.symm
  have (x : _) : exists n, p.leadingCoeff ^ n • (t * x) in φ.range := by
    have : φ p * t * x in φ.range := by simpa [← AlgHom.map_adjoin_singleton] using hp x
    obtain ⟨q, n, hn⟩ :=
      exists_isIntegral_leadingCoeff_pow_smul_sub_of_isIntegralElem_of_mul_mem_range φ _ p
        (hφ.to_isIntegral (t * x)) (by convert! this using 1; ring)
    obtain ⟨r, hr : algebraMap _ _ r = _⟩ := hRS.le hn
    exact ⟨n, (C r + q), by simp [← Polynomial.algebraMap_eq, -Polynomial.algebraMap_apply, hr]⟩
  choose n hn using this
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R[X]) (M := S)
  refine ⟨s.sup n, fun x => ?_⟩
  rw [← AlgHom.map_adjoin_singleton]; rw [adjoin_X]; rw [Algebra.map_top]; rw [Algebra.smul_mul_assoc]
  induction hs.ge (Set.mem_univ x) using Submodule.span_induction with
  | mem x h =>
    rw [← Nat.sub_add_cancel (s.le_sup h)]; rw [pow_add]; rw [mul_smul]
    exact Subalgebra.smul_mem _ (hn _) _
  | zero => simp
  | add x y _ _ hx hy => simpa only [mul_add, smul_add] using add_mem hx hy
  | smul a x hx IH =>
    rw [mul_smul_comm]; rw [smul_comm]; rw [Algebra.smul_def]
    exact mul_mem (AlgHom.mem_range_self _ _) IH

@[stacks 00PY]

中文:
引理 存在_leadingCoeff_pow_smul_mem_conductor
  证明: by
  algebraize [φ.toRingHom]
  have : IsScalarTower R R[X] S := .of_algebraMap_eq' φ.comp_algebraMap.symm
  have (x : _) : exists n, p.leadingCoeff ^ n • (t * x) in φ.range := by
    have : φ p * t * x in φ.range := by simpa [← AlgHom.map_adjoin_singleton] using hp x
    obtain ⟨q, n, hn⟩ :=
      exists_isIntegral_leadingCoeff_pow_smul_sub_of_isIntegralElem_of_mul_mem_range φ _ p
        (hφ.to_isIntegral (t * x)) (by convert! this using 1; ring)
    obtain ⟨r, hr : algebraMap _ _ r = _⟩ := hRS.le hn
    exact ⟨n, (C r + q), by simp [← Polynomial.algebraMap_eq, -Polynomial.algebraMap_apply, hr]⟩
  choose n hn using this
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R[X]) (M := S)
  refine ⟨s.sup n, fun x => ?_⟩
  rw [← AlgHom.map_adjoin_singleton]; rw [adjoin_X]; rw [Algebra.map_top]; rw [Algebra.smul_mul_assoc]
  induction hs.ge (Set.mem_univ x) using Submodule.span_induction with
  | mem x h =>
    rw [← Nat.sub_add_cancel (s.le_sup h)]; rw [pow_add]; rw [mul_smul]
    exact Subalgebra.smul_mem _ (hn _) _
  | zero => simp
  | add x y _ _ hx hy => simpa only [mul_add, smul_add] using add_mem hx hy
  | smul a x hx IH =>
    rw [mul_smul_comm]; rw [smul_comm]; rw [Algebra.smul_def]
    exact mul_mem (AlgHom.mem_range_self _ _) IH

@[stacks 00PY]

Depends on / 依赖: AlgHom, AlgHom.map_adjoin_singleton, IsScalarTower, algebraMap, algebraize, comp_algebraMap, comp_algebraMap.symm, convert, exists_isIntegral_leadingCoeff_pow_smul_sub_of_isIntegralElem_of_mul_mem_range, hRS.le, leadingCoeff, map_adjoin_singleton, of_algebraMap_eq, p.leadingCoeff, toRingHom, to_isIntegral
-/
lemma exists_leadingCoeff_pow_smul_mem_conductor
    (hRS : integralClosure R S = ⊥) -- `IsIntegrallyClosedIn` but without injective assumption
    (hφ : φ.toRingHom.Finite) (hp : φ p * t in conductor R (φ X)) :
    exists n, p.leadingCoeff ^ n • t in conductor R (φ X) := by
  algebraize [φ.toRingHom]
  have : IsScalarTower R R[X] S := .of_algebraMap_eq' φ.comp_algebraMap.symm
  have (x : _) : exists n, p.leadingCoeff ^ n • (t * x) in φ.range := by
    have : φ p * t * x in φ.range := by simpa [← AlgHom.map_adjoin_singleton] using hp x
    obtain ⟨q, n, hn⟩ :=
      exists_isIntegral_leadingCoeff_pow_smul_sub_of_isIntegralElem_of_mul_mem_range φ _ p
        (hφ.to_isIntegral (t * x)) (by convert! this using 1; ring)
    obtain ⟨r, hr : algebraMap _ _ r = _⟩ := hRS.le hn
    exact ⟨n, (C r + q), by simp [← Polynomial.algebraMap_eq, -Polynomial.algebraMap_apply, hr]⟩
  choose n hn using this
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R[X]) (M := S)
  refine ⟨s.sup n, fun x => ?_⟩
  rw [← AlgHom.map_adjoin_singleton]; rw [adjoin_X]; rw [Algebra.map_top]; rw [Algebra.smul_mul_assoc]
  induction hs.ge (Set.mem_univ x) using Submodule.span_induction with
  | mem x h =>
    rw [← Nat.sub_add_cancel (s.le_sup h)]; rw [pow_add]; rw [mul_smul]
    exact Subalgebra.smul_mem _ (hn _) _
  | zero => simp
  | add x y _ _ hx hy => simpa only [mul_add, smul_add] using add_mem hx hy
  | smul a x hx IH =>
    rw [mul_smul_comm]; rw [smul_comm]; rw [Algebra.smul_def]
    exact mul_mem (AlgHom.mem_range_self _ _) IH

@[stacks 00PY]
/--
lemma `exists_leadingCoeff_pow_smul_mem_radical_conductor` / 引理 `exists_leadingCoeff_pow_smul_mem_radical_conductor`

English:
lemma exists_leadingCoeff_pow_smul_mem_radical_conductor
  proof: by
  wlog hi : i = p.natDegree generalizing p i
  · clear hi
    simp only [forall_eq, coeff_natDegree] at this
    induction hpn : p.natDegree using Nat.strong_induction_on generalizing p with
    | h n IH =>
    cases n with
    | zero =>
      obtain hi' | hi' := lt_or_ge p.natDegree i
      · simp [coeff_eq_zero_of_natDegree_lt hi']
      · simpa [← coeff_natDegree, hpn, show i = 0 by lia] using this _ hp
    | succ n =>
      obtain hi' | hi' := eq_or_ne i p.natDegree
      · simpa [hi'] using this _ hp
      have : φ p.eraseLead * t in (conductor R (φ X)).radical := by
        simp only [← self_sub_C_mul_X_pow, map_sub, ← algebraMap_eq, map_mul, AlgHom.commutes,
          map_pow, sub_mul, mul_right_comm _ _ t, ← Algebra.smul_def _ t]
        exact sub_mem hp (Ideal.mul_mem_right _ _ (this _ hp))
      simpa [eraseLead_coeff, hi'] using
        IH _ ((eraseLead_natDegree_le _).trans_lt (by lia)) _ this rfl
  obtain ⟨n, hn⟩ := hp
  obtain ⟨k, hk⟩ := exists_leadingCoeff_pow_smul_mem_conductor φ (t ^ n) (p ^ n) hRS hφ
    (by simpa [mul_pow] using hn)
  by_cases hpn : p.leadingCoeff ^ n = 0
  · use n; simp [_root_.smul_pow, hpn, hi]
  rw [leadingCoeff_pow' hpn]; rw [← pow_mul] at hk
  refine ⟨n * k + n, ?_⟩
  rw [_root_.smul_pow]; rw [pow_add]; rw [add_comm]; rw [pow_add]; rw [mul_smul_mul_comm]; rw [hi]
  exact Ideal.mul_mem_right _ _ hk

@[stacks 00PY]

中文:
引理 存在_leadingCoeff_pow_smul_mem_radical_conductor
  证明: by
  wlog hi : i = p.natDegree generalizing p i
  · clear hi
    simp only [forall_eq, coeff_natDegree] at this
    induction hpn : p.natDegree using Nat.strong_induction_on generalizing p with
    | h n IH =>
    cases n with
    | zero =>
      obtain hi' | hi' := lt_or_ge p.natDegree i
      · simp [coeff_eq_zero_of_natDegree_lt hi']
      · simpa [← coeff_natDegree, hpn, show i = 0 by lia] using this _ hp
    | succ n =>
      obtain hi' | hi' := eq_or_ne i p.natDegree
      · simpa [hi'] using this _ hp
      have : φ p.eraseLead * t in (conductor R (φ X)).radical := by
        simp only [← self_sub_C_mul_X_pow, map_sub, ← algebraMap_eq, map_mul, AlgHom.commutes,
          map_pow, sub_mul, mul_right_comm _ _ t, ← Algebra.smul_def _ t]
        exact sub_mem hp (Ideal.mul_mem_right _ _ (this _ hp))
      simpa [eraseLead_coeff, hi'] using
        IH _ ((eraseLead_natDegree_le _).trans_lt (by lia)) _ this rfl
  obtain ⟨n, hn⟩ := hp
  obtain ⟨k, hk⟩ := exists_leadingCoeff_pow_smul_mem_conductor φ (t ^ n) (p ^ n) hRS hφ
    (by simpa [mul_pow] using hn)
  by_cases hpn : p.leadingCoeff ^ n = 0
  · use n; simp [_root_.smul_pow, hpn, hi]
  rw [leadingCoeff_pow' hpn]; rw [← pow_mul] at hk
  refine ⟨n * k + n, ?_⟩
  rw [_root_.smul_pow]; rw [pow_add]; rw [add_comm]; rw [pow_add]; rw [mul_smul_mul_comm]; rw [hi]
  exact Ideal.mul_mem_right _ _ hk

@[stacks 00PY]

Depends on / 依赖: Nat.strong_induction_on, coeff_eq_zero_of_natDegree_lt, coeff_natDegree, conductor, eq_or_ne, eraseLead, forall_eq, generalizing, lt_or_ge, natDegree, p.eraseLead, p.natDegree, strong_induction_on
-/
lemma exists_leadingCoeff_pow_smul_mem_radical_conductor
    (hRS : integralClosure R S = ⊥) -- `IsIntegrallyClosedIn` but without injective assumption
    (hφ : φ.toRingHom.Finite) (hp : φ p * t in (conductor R (φ X)).radical) (i : Nat) :
    p.coeff i • t in (conductor R (φ X)).radical := by
  wlog hi : i = p.natDegree generalizing p i
  · clear hi
    simp only [forall_eq, coeff_natDegree] at this
    induction hpn : p.natDegree using Nat.strong_induction_on generalizing p with
    | h n IH =>
    cases n with
    | zero =>
      obtain hi' | hi' := lt_or_ge p.natDegree i
      · simp [coeff_eq_zero_of_natDegree_lt hi']
      · simpa [← coeff_natDegree, hpn, show i = 0 by lia] using this _ hp
    | succ n =>
      obtain hi' | hi' := eq_or_ne i p.natDegree
      · simpa [hi'] using this _ hp
      have : φ p.eraseLead * t in (conductor R (φ X)).radical := by
        simp only [← self_sub_C_mul_X_pow, map_sub, ← algebraMap_eq, map_mul, AlgHom.commutes,
          map_pow, sub_mul, mul_right_comm _ _ t, ← Algebra.smul_def _ t]
        exact sub_mem hp (Ideal.mul_mem_right _ _ (this _ hp))
      simpa [eraseLead_coeff, hi'] using
        IH _ ((eraseLead_natDegree_le _).trans_lt (by lia)) _ this rfl
  obtain ⟨n, hn⟩ := hp
  obtain ⟨k, hk⟩ := exists_leadingCoeff_pow_smul_mem_conductor φ (t ^ n) (p ^ n) hRS hφ
    (by simpa [mul_pow] using hn)
  by_cases hpn : p.leadingCoeff ^ n = 0
  · use n; simp [_root_.smul_pow, hpn, hi]
  rw [leadingCoeff_pow' hpn]; rw [← pow_mul] at hk
  refine ⟨n * k + n, ?_⟩
  rw [_root_.smul_pow]; rw [pow_add]; rw [add_comm]; rw [pow_add]; rw [mul_smul_mul_comm]; rw [hi]
  exact Ideal.mul_mem_right _ _ hk

@[stacks 00PY]
/--
lemma `isStronglyTranscendental_mk_radical_conductor` / 引理 `isStronglyTranscendental_mk_radical_conductor`

English:
lemma isStronglyTranscendental_mk_radical_conductor
  proof: by
  refine Ideal.Quotient.mk_surjective.forall.mpr fun u p e => ?_
  rw [← Ideal.Quotient.algebraMap_eq]; rw [aeval_algebraMap_apply]; rw [Ideal.Quotient.algebraMap_eq]; rw [← map_mul]; rw [Ideal.Quotient.eq_zero_iff_mem] at e
  ext i
  simpa [← Ideal.Quotient.mk_algebraMap, ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
    Algebra.smul_def] using exists_leadingCoeff_pow_smul_mem_radical_conductor _ u p hRS hx
      (by simpa using e) i

中文:
引理 isStronglyTranscendental_mk_radical_conductor
  证明: by
  refine Ideal.Quotient.mk_surjective.forall.mpr fun u p e => ?_
  rw [← Ideal.Quotient.algebraMap_eq]; rw [aeval_algebraMap_apply]; rw [Ideal.Quotient.algebraMap_eq]; rw [← map_mul]; rw [Ideal.Quotient.eq_zero_iff_mem] at e
  ext i
  simpa [← Ideal.Quotient.mk_algebraMap, ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
    Algebra.smul_def] using exists_leadingCoeff_pow_smul_mem_radical_conductor _ u p hRS hx
      (by simpa using e) i

Depends on / 依赖: Finite
-/
lemma isStronglyTranscendental_mk_radical_conductor
    (hRS : integralClosure R S = ⊥) -- `IsIntegrallyClosedIn` but without injective assumption
    (x : S) (hx : (aeval (R := R) x).Finite) :
    IsStronglyTranscendental R (Ideal.Quotient.mk (conductor R x).radical x) := by
  refine Ideal.Quotient.mk_surjective.forall.mpr fun u p e => ?_
  rw [← Ideal.Quotient.algebraMap_eq]; rw [aeval_algebraMap_apply]; rw [Ideal.Quotient.algebraMap_eq]; rw [← map_mul]; rw [Ideal.Quotient.eq_zero_iff_mem] at e
  ext i
  simpa [← Ideal.Quotient.mk_algebraMap, ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
    Algebra.smul_def] using exists_leadingCoeff_pow_smul_mem_radical_conductor _ u p hRS hx
      (by simpa using e) i

end IsStronglyTranscendental

namespace Algebra

attribute [local instance] Polynomial.isLocalization Polynomial.algebra

section not_quasiFiniteAt

/--
lemma `not_isStronglyTranscendental_of_weaklyQuasiFiniteAt_of_isIntegrallyClosed` / 引理 `not_isStronglyTranscendental_of_weaklyQuasiFiniteAt_of_isIntegrallyClosed`

English:
lemma not_isStronglyTranscendental_of_weaklyQuasiFiniteAt_of_isIntegrallyClosed
  proof: by
  intro hx
  have : IsDomain R := (FaithfulSMul.algebraMap_injective R S).isDomain
  have hf' : Function.Injective (aeval (R := R) x) := (injective_iff_map_eq_zero _).mpr
    fun p hp => not_not.mp fun hp' => hx.transcendental ⟨p, hp', hp⟩
  generalize hf : aeval (R := R) x = f at *
  obtain rfl : f X = x := by simp [← hf]
  let := f.toRingHom.toAlgebra
  have := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  have : Module.Finite R[X] S := RingHom.finite_algebraMap.mpr hx'
  have : FaithfulSMul R[X] S := by
    rw [faithfulSMul_iff_algebraMap_injective]; rw [injective_iff_map_eq_zero]
    intro p hp
    by_contra hp'
    exact hx.transcendental ⟨p, hp', by rwa [aeval_algHom_apply, aeval_X_left_apply]⟩
  have : (P.under R).map C < P.under R[X] := map_under_lt_comap_of_weaklyQuasiFiniteAt _ _
  obtain ⟨Q, hQ, _, ⟨e⟩⟩ := Ideal.exists_ideal_lt_liesOver_of_lt (S := S) P this
  refine hQ.ne (Algebra.WeaklyQuasiFiniteAt.eq_of_le_of_under_eq (R := R) hQ.le ?_)
  rw [← Ideal.under_under (B := R[X]), ← e]
  ext
  simp [Ideal.mem_map_C_iff, coeff_C, apply_ite]

中文:
引理 not_isStronglyTranscendental_of_weaklyQuasiFiniteAt_of_is整数egrallyClosed
  证明: by
  intro hx
  have : IsDomain R := (FaithfulSMul.algebraMap_injective R S).isDomain
  have hf' : Function.Injective (aeval (R := R) x) := (injective_iff_map_eq_zero _).mpr
    fun p hp => not_not.mp fun hp' => hx.transcendental ⟨p, hp', hp⟩
  generalize hf : aeval (R := R) x = f at *
  obtain rfl : f X = x := by simp [← hf]
  let := f.toRingHom.toAlgebra
  have := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  have : Module.Finite R[X] S := RingHom.finite_algebraMap.mpr hx'
  have : FaithfulSMul R[X] S := by
    rw [faithfulSMul_iff_algebraMap_injective]; rw [injective_iff_map_eq_zero]
    intro p hp
    by_contra hp'
    exact hx.transcendental ⟨p, hp', by rwa [aeval_algHom_apply, aeval_X_left_apply]⟩
  have : (P.under R).map C < P.under R[X] := map_under_lt_comap_of_weaklyQuasiFiniteAt _ _
  obtain ⟨Q, hQ, _, ⟨e⟩⟩ := Ideal.exists_ideal_lt_liesOver_of_lt (S := S) P this
  refine hQ.ne (Algebra.WeaklyQuasiFiniteAt.eq_of_le_of_under_eq (R := R) hQ.le ?_)
  rw [← Ideal.under_under (B := R[X]), ← e]
  ext
  simp [Ideal.mem_map_C_iff, coeff_C, apply_ite]
-/
private lemma not_isStronglyTranscendental_of_weaklyQuasiFiniteAt_of_isIntegrallyClosed
    [FaithfulSMul R S] [IsIntegrallyClosed R] [IsDomain S]
    {x : S} (hx' : (aeval (R := R) x).Finite)
    (P : Ideal S) [P.IsPrime] [Algebra.WeaklyQuasiFiniteAt R P] :
      ¬ IsStronglyTranscendental R x := by
  intro hx
  have : IsDomain R := (FaithfulSMul.algebraMap_injective R S).isDomain
  have hf' : Function.Injective (aeval (R := R) x) := (injective_iff_map_eq_zero _).mpr
    fun p hp => not_not.mp fun hp' => hx.transcendental ⟨p, hp', hp⟩
  generalize hf : aeval (R := R) x = f at *
  obtain rfl : f X = x := by simp [← hf]
  let := f.toRingHom.toAlgebra
  have := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  have : Module.Finite R[X] S := RingHom.finite_algebraMap.mpr hx'
  have : FaithfulSMul R[X] S := by
    rw [faithfulSMul_iff_algebraMap_injective]; rw [injective_iff_map_eq_zero]
    intro p hp
    by_contra hp'
    exact hx.transcendental ⟨p, hp', by rwa [aeval_algHom_apply, aeval_X_left_apply]⟩
  have : (P.under R).map C < P.under R[X] := map_under_lt_comap_of_weaklyQuasiFiniteAt _ _
  obtain ⟨Q, hQ, _, ⟨e⟩⟩ := Ideal.exists_ideal_lt_liesOver_of_lt (S := S) P this
  refine hQ.ne (Algebra.WeaklyQuasiFiniteAt.eq_of_le_of_under_eq (R := R) hQ.le ?_)
  rw [← Ideal.under_under (B := R[X]), ← e]
  ext
  simp [Ideal.mem_map_C_iff, coeff_C, apply_ite]

/-- This asks for an explicit `K = Frac(R)`, `L = Frac(S)`,
`R'` the integral closure of `R` in `K`, and `S' ⊆ L` the subalgebra spanned by `R'` and `S`,
to aid typeclass synthesis.

Use `not_isStronglyTranscendental_of_quasiFiniteAt` below instead. -/
@[stacks 00Q1]
/--
lemma `not_isStronglyTranscendental_of_weaklyQuasiFiniteAt_of_isDomain_aux` / 引理 `not_isStronglyTranscendental_of_weaklyQuasiFiniteAt_of_isDomain_aux`

English:
lemma not_isStronglyTranscendental_of_weaklyQuasiFiniteAt_of_isDomain_aux
  proof: by
  intro hx
  have := (FaithfulSMul.algebraMap_injective S' L).isDomain
  have := (FaithfulSMul.algebraMap_injective R K).isDomain
  have : Algebra.IsIntegral R R' := IsIntegralClosure.isIntegral_algebra _ K
  have : FaithfulSMul R' K := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (IsIntegralClosure.algebraMap_injective R' R K)
  have : FaithfulSMul R R' := .tower_bot _ _ K
  have : FaithfulSMul R' L := .trans _ K _
  have : FaithfulSMul R' S' := .tower_bot _ _ L
  have : IsIntegrallyClosedIn R' K := .of_isIntegralClosure R
  have : IsIntegrallyClosed R' := .of_isIntegrallyClosed_of_isIntegrallyClosedIn _ K
  let g := Algebra.TensorProduct.lift (Algebra.ofId R' S') f fun _ _ => .all _ _
  have hf₃ : Function.Injective f :=
    .of_comp (f := algebraMap S' L) (hf₂ ▸ FaithfulSMul.algebraMap_injective S L:)
  have hf₄ : f.IsIntegral := by
    have : f = (g.restrictScalars R).comp ((Algebra.TensorProduct.comm _ _ _).toAlgHom.comp
        (IsScalarTower.toAlgHom _ _ _)) := by ext; simp [g]
    simp only [this, AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom, ← RingHom.comp_assoc]
    refine .trans _ _ (algebraMap_isIntegral_iff.mpr inferInstance) ?_
    exact RingHom.isIntegral_of_surjective _
      (hf₁.comp (Algebra.TensorProduct.comm _ _ _).surjective)
  have H₁ : IsStronglyTranscendental R' (f x) := by
    refine .of_map (f := IsScalarTower.toAlgHom R' S' L) (FaithfulSMul.algebraMap_injective S' L) ?_
    dsimp
    rw [show algebraMap S' L (f x) = algebraMap _ _ x from congr($hf₂ x)]
    exact ((hx.of_isLocalization S⁰).of_isLocalization_left R⁰).restrictScalars (S := K)
  have H₂ : (aeval (R := R') (f x)).toRingHom.Finite := by
    convert!
      ((RingHom.Finite.of_surjective g.toRingHom hf₁).comp
            (RingHom.Finite.tensorProductMap (f := AlgHom.id R R') (RingEquiv.refl _).finite
              hx')).comp
        (polyEquivTensor R R').toRingEquiv.finite using 1
    ext <;> simp [g]
  obtain ⟨⟨Q, _⟩, hQ⟩ := hf₄.comap_surjective hf₃ ⟨P, ‹_›⟩
  suffices WeaklyQuasiFiniteAt R' Q from
    not_isStronglyTranscendental_of_weaklyQuasiFiniteAt_of_isIntegrallyClosed H₂ Q H₁
have : Algebra.WeaklyQuasiFiniteAt R' (Q.comap g.toRingHom) := .baseChange P _ by
    rw [Ideal.comap_comap]
    convert! congr(($hQ.symm).1)
    ext; simp [g]
  exact .of_surjectiveOnStalks (Q.comap g.toRingHom) _ g
    (RingHom.surjectiveOnStalks_of_surjective hf₁) rfl

中文:
引理 not_isStronglyTranscendental_of_weaklyQuasiFiniteAt_of_isDomain_aux
  证明: by
  intro hx
  have := (FaithfulSMul.algebraMap_injective S' L).isDomain
  have := (FaithfulSMul.algebraMap_injective R K).isDomain
  have : Algebra.IsIntegral R R' := IsIntegralClosure.isIntegral_algebra _ K
  have : FaithfulSMul R' K := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (IsIntegralClosure.algebraMap_injective R' R K)
  have : FaithfulSMul R R' := .tower_bot _ _ K
  have : FaithfulSMul R' L := .trans _ K _
  have : FaithfulSMul R' S' := .tower_bot _ _ L
  have : IsIntegrallyClosedIn R' K := .of_isIntegralClosure R
  have : IsIntegrallyClosed R' := .of_isIntegrallyClosed_of_isIntegrallyClosedIn _ K
  let g := Algebra.TensorProduct.lift (Algebra.ofId R' S') f fun _ _ => .all _ _
  have hf₃ : Function.Injective f :=
    .of_comp (f := algebraMap S' L) (hf₂ ▸ FaithfulSMul.algebraMap_injective S L:)
  have hf₄ : f.IsIntegral := by
    have : f = (g.restrictScalars R).comp ((Algebra.TensorProduct.comm _ _ _).toAlgHom.comp
        (IsScalarTower.toAlgHom _ _ _)) := by ext; simp [g]
    simp only [this, AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom, ← RingHom.comp_assoc]
    refine .trans _ _ (algebraMap_isIntegral_iff.mpr inferInstance) ?_
    exact RingHom.isIntegral_of_surjective _
      (hf₁.comp (Algebra.TensorProduct.comm _ _ _).surjective)
  have H₁ : IsStronglyTranscendental R' (f x) := by
    refine .of_map (f := IsScalarTower.toAlgHom R' S' L) (FaithfulSMul.algebraMap_injective S' L) ?_
    dsimp
    rw [show algebraMap S' L (f x) = algebraMap _ _ x from congr($hf₂ x)]
    exact ((hx.of_isLocalization S⁰).of_isLocalization_left R⁰).restrictScalars (S := K)
  have H₂ : (aeval (R := R') (f x)).toRingHom.Finite := by
    convert!
      ((RingHom.Finite.of_surjective g.toRingHom hf₁).comp
            (RingHom.Finite.tensorProductMap (f := AlgHom.id R R') (RingEquiv.refl _).finite
              hx')).comp
        (polyEquivTensor R R').toRingEquiv.finite using 1
    ext <;> simp [g]
  obtain ⟨⟨Q, _⟩, hQ⟩ := hf₄.comap_surjective hf₃ ⟨P, ‹_›⟩
  suffices WeaklyQuasiFiniteAt R' Q from
    not_isStronglyTranscendental_of_weaklyQuasiFiniteAt_of_isIntegrallyClosed H₂ Q H₁
have : Algebra.WeaklyQuasiFiniteAt R' (Q.comap g.toRingHom) := .baseChange P _ by
    rw [Ideal.comap_comap]
    convert! congr(($hQ.symm).1)
    ext; simp [g]
  exact .of_surjectiveOnStalks (Q.comap g.toRingHom) _ g
    (RingHom.surjectiveOnStalks_of_surjective hf₁) rfl
-/
private lemma not_isStronglyTranscendental_of_weaklyQuasiFiniteAt_of_isDomain_aux
    (K L : Type*) [Field K] [Field L] [Algebra R K] [Algebra R L] [Algebra S L] [Algebra K L]
    [IsScalarTower R K L] [IsScalarTower R S L] [IsFractionRing R K] [IsFractionRing S L]
    {R' S' : Type*} [CommRing R'] [CommRing S'] [Algebra R R'] [Algebra R' S'] [Algebra R S']
    [Algebra S' L] [Algebra R' L] [IsScalarTower R' S' L] [Algebra R' K] [IsScalarTower R' K L]
    [IsScalarTower R R' S'] [FaithfulSMul S' L] [IsIntegralClosure R' R K]
    [IsScalarTower R R' K]
    (f : S ->ₐ[R] S') (hf₁ : Function.Surjective
      (Algebra.TensorProduct.lift (Algebra.ofId R' S') f fun _ _ => .all _ _))
    (hf₂ : (algebraMap S' L).comp f.toRingHom = algebraMap _ _)
    {x : S} (hx' : (aeval (R := R) x).Finite)
    (P : Ideal S) [P.IsPrime] [Algebra.WeaklyQuasiFiniteAt R P] :
    ¬ IsStronglyTranscendental R x := by
  intro hx
  have := (FaithfulSMul.algebraMap_injective S' L).isDomain
  have := (FaithfulSMul.algebraMap_injective R K).isDomain
  have : Algebra.IsIntegral R R' := IsIntegralClosure.isIntegral_algebra _ K
  have : FaithfulSMul R' K := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (IsIntegralClosure.algebraMap_injective R' R K)
  have : FaithfulSMul R R' := .tower_bot _ _ K
  have : FaithfulSMul R' L := .trans _ K _
  have : FaithfulSMul R' S' := .tower_bot _ _ L
  have : IsIntegrallyClosedIn R' K := .of_isIntegralClosure R
  have : IsIntegrallyClosed R' := .of_isIntegrallyClosed_of_isIntegrallyClosedIn _ K
  let g := Algebra.TensorProduct.lift (Algebra.ofId R' S') f fun _ _ => .all _ _
  have hf₃ : Function.Injective f :=
    .of_comp (f := algebraMap S' L) (hf₂ ▸ FaithfulSMul.algebraMap_injective S L:)
  have hf₄ : f.IsIntegral := by
    have : f = (g.restrictScalars R).comp ((Algebra.TensorProduct.comm _ _ _).toAlgHom.comp
        (IsScalarTower.toAlgHom _ _ _)) := by ext; simp [g]
    simp only [this, AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom, ← RingHom.comp_assoc]
    refine .trans _ _ (algebraMap_isIntegral_iff.mpr inferInstance) ?_
    exact RingHom.isIntegral_of_surjective _
      (hf₁.comp (Algebra.TensorProduct.comm _ _ _).surjective)
  have H₁ : IsStronglyTranscendental R' (f x) := by
    refine .of_map (f := IsScalarTower.toAlgHom R' S' L) (FaithfulSMul.algebraMap_injective S' L) ?_
    dsimp
    rw [show algebraMap S' L (f x) = algebraMap _ _ x from congr($hf₂ x)]
    exact ((hx.of_isLocalization S⁰).of_isLocalization_left R⁰).restrictScalars (S := K)
  have H₂ : (aeval (R := R') (f x)).toRingHom.Finite := by
    convert!
      ((RingHom.Finite.of_surjective g.toRingHom hf₁).comp
            (RingHom.Finite.tensorProductMap (f := AlgHom.id R R') (RingEquiv.refl _).finite
              hx')).comp
        (polyEquivTensor R R').toRingEquiv.finite using 1
    ext <;> simp [g]
  obtain ⟨⟨Q, _⟩, hQ⟩ := hf₄.comap_surjective hf₃ ⟨P, ‹_›⟩
  suffices WeaklyQuasiFiniteAt R' Q from
    not_isStronglyTranscendental_of_weaklyQuasiFiniteAt_of_isIntegrallyClosed H₂ Q H₁
have : Algebra.WeaklyQuasiFiniteAt R' (Q.comap g.toRingHom) := .baseChange P _ by
    rw [Ideal.comap_comap]
    convert! congr(($hQ.symm).1)
    ext; simp [g]
  exact .of_surjectiveOnStalks (Q.comap g.toRingHom) _ g
    (RingHom.surjectiveOnStalks_of_surjective hf₁) rfl

set_option backward.isDefEq.respectTransparency false in
nonrec lemma not_isStronglyTranscendental_of_weaklyQuasiFiniteAt [IsReduced S]
    {x : S} (hx' : (aeval (R := R) x).toRingHom.Finite)
    (P : Ideal S) [P.IsPrime] [Algebra.WeaklyQuasiFiniteAt R P] :
    ¬ IsStronglyTranscendental R x := by
  wlog hS : IsDomain S ∧ FaithfulSMul R S
  · intro hx
    obtain ⟨p, hp, hpP⟩ := Ideal.exists_minimalPrimes_le (J := P) bot_le
    have inst := hp.1.1
    have inst : (P.map (Ideal.Quotient.mk p)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by simpa)
    have inst : WeaklyQuasiFiniteAt (R ⧸ Ideal.under R p) (Ideal.map (Ideal.Quotient.mk p) P) := by
      suffices Algebra.WeaklyQuasiFiniteAt R (P.map (Ideal.Quotient.mk p)) from
        .of_restrictScalars R _ _
      refine .of_surjectiveOnStalks P _ (Ideal.Quotient.mkₐ _ _)
        (RingHom.surjectiveOnStalks_of_surjective Ideal.Quotient.mk_surjective) ?_
      refine .trans ?_ (Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective _).symm
      simpa [← RingHom.ker_eq_comap_bot]
    refine this (R := R ⧸ p.under R) ?_ (P.map (Ideal.Quotient.mk p)) ⟨inferInstance, inferInstance⟩
      ((isStronglyTranscendental_mk_of_mem_minimalPrimes hx p hp).of_surjective_left
        Ideal.Quotient.mk_surjective)
    refine RingHom.Finite.of_comp_finite (f := mapRingHom (Ideal.Quotient.mk _)) ?_
    convert! (RingHom.Finite.of_surjective _ (Ideal.Quotient.mk_surjective (I := p))).comp hx'
    ext <;> simp
  cases hS
  have : IsDomain R := (FaithfulSMul.algebraMap_injective R S).isDomain
  let K := FractionRing R
  let L := FractionRing S
  let : Algebra K L := FractionRing.liftAlgebra _ _
  let R' := integralClosure R K
  let S' : Subalgebra R' L := Algebra.adjoin R' (algebraMap S L).range
  let f : S ->ₐ[R] S' := (IsScalarTower.toAlgHom R S L).codRestrict (S'.restrictScalars R) fun x => by
    simpa using show algebraMap S L x in S' from Algebra.subset_adjoin ⟨x, rfl⟩
  let g := Algebra.TensorProduct.lift (Algebra.ofId R' S') f fun _ _ => .all _ _
  have hf : Function.Surjective g := by
    rw [← AlgHom.range_eq_top]; rw [← (Subalgebra.map_injective (f := S'.val) Subtype.val_injective).eq_iff]; rw [Algebra.map_top]
    refine le_antisymm (Set.image_subset_range S'.val g.range) ?_
    simp only [RingHom.coe_range, Subalgebra.range_val, Algebra.adjoin_le_iff, Subalgebra.coe_map,
      Subalgebra.coe_val, AlgHom.coe_range, Set.range_subset_iff, Set.mem_image, Set.mem_range,
      exists_exists_eq_and, S']
    exact fun y => ⟨1 otimesₜ y, by simp [g, S']; rfl⟩
  exact not_isStronglyTranscendental_of_weaklyQuasiFiniteAt_of_isDomain_aux K L f hf rfl hx' P

@[stacks 00Q2]
nonrec lemma not_isStronglyTranscendental_of_quasiFiniteAt [IsReduced S]
    {x : S} (hx' : (aeval (R := R) x).toRingHom.Finite)
    (P : Ideal S) [P.IsPrime] [Algebra.QuasiFiniteAt R P] :
    ¬ IsStronglyTranscendental R x :=
  not_isStronglyTranscendental_of_weaklyQuasiFiniteAt hx' P

end not_quasiFiniteAt

section FixedUniverse

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

-- Subsumed by `ZariskisMainProperty.of_finiteType`.
/--
lemma `ZariskisMainProperty.of_adjoin_eq_top` / 引理 `ZariskisMainProperty.of_adjoin_eq_top`

English:
lemma ZariskisMainProperty.of_adjoin_eq_top
  proof: by
  wlog H : integralClosure R S = ⊥
  · let inst : Algebra (integralClosure R S) (Localization.AtPrime p) :=
      OreLocalization.instAlgebra
    have inst : Algebra.WeaklyQuasiFiniteAt (integralClosure R S) p :=
      .of_restrictScalars R (integralClosure R S) _
    refine .restrictScalars (this p x ?_ (integralClosure_idem (R := R)))
    suffices ⊤ <= (Algebra.adjoin (integralClosure R S) {x}).restrictScalars R from
      top_le_iff.mp fun x _ => (Subalgebra.mem_restrictScalars _).mp (this trivial)
    refine hx.ge.trans ?_
    rw [Algebra.restrictScalars_adjoin]
    exact Algebra.adjoin_mono (by simp)
  have H₀ : Function.Surjective (aeval (R := R) x) := by
    rwa [← AlgHom.range_eq_top, ← Algebra.adjoin_singleton_eq_range_aeval]
  have ⟨f, (hf : aeval x f = 0), hfp⟩ := SetLike.not_le_iff_exists.mp
    (Polynomial.not_ker_le_map_C_of_surjective_of_weaklyQuasiFiniteAt _ H₀ p)
  obtain ⟨n, hfn⟩ : exists x, algebraMap R S (f.coeff x) ∉ p := by simpa [Ideal.mem_map_C_iff] using! hfp
  clear hfp
  induction hm : f.natDegree using Nat.strong_induction_on generalizing f n with | h m IH =>
  obtain (_ | m) := m
  · obtain ⟨r, rfl⟩ := natDegree_eq_zero.mp hm
    cases n <;> aesop
  by_cases Hfp : algebraMap _ _ f.leadingCoeff in p
  · obtain ⟨a, ha⟩ := H.le (isIntegral_leadingCoeff_smul f x hf)
    refine IH _ ?_ (f.eraseLead + C a * X ^ m) (hm := rfl) ?_ n ?_
    · suffices f.eraseLead.natDegree <= m by compute_degree!
      exact (eraseLead_natDegree_le ..).trans (by lia)
    · simp [← self_sub_monomial_natDegree_leadingCoeff, hf, hm, pow_succ', ← Algebra.smul_def,
        ← Algebra.smul_mul_assoc, ← ha]
    · suffices algebraMap R S (f.coeff n) + algebraMap R S (if n = m then a else 0) ∉ p by
        simpa [eraseLead_coeff, show n != f.natDegree by rintro rfl; exact hfn (by simpa)]
      rwa [Ideal.add_mem_iff_left]
      split_ifs
      · convert p.mul_mem_right x Hfp
        simpa [Algebra.smul_def] using! ha
      · simp
  · refine zariskisMainProperty_iff_exists_saturation_eq_top.mpr ⟨_, Hfp, isIntegral_algebraMap, ?_⟩
    rw [← top_le_iff]; rw [← hx]
    refine Algebra.adjoin_singleton_le ⟨_, ⟨1, rfl⟩, ?_⟩
    simpa [Algebra.smul_def] using! isIntegral_leadingCoeff_smul f x hf

中文:
引理 ZariskisMainProperty.of_adjoin_eq_top
  证明: by
  wlog H : integralClosure R S = ⊥
  · let inst : Algebra (integralClosure R S) (Localization.AtPrime p) :=
      OreLocalization.instAlgebra
    have inst : Algebra.WeaklyQuasiFiniteAt (integralClosure R S) p :=
      .of_restrictScalars R (integralClosure R S) _
    refine .restrictScalars (this p x ?_ (integralClosure_idem (R := R)))
    suffices ⊤ <= (Algebra.adjoin (integralClosure R S) {x}).restrictScalars R from
      top_le_iff.mp fun x _ => (Subalgebra.mem_restrictScalars _).mp (this trivial)
    refine hx.ge.trans ?_
    rw [Algebra.restrictScalars_adjoin]
    exact Algebra.adjoin_mono (by simp)
  have H₀ : Function.Surjective (aeval (R := R) x) := by
    rwa [← AlgHom.range_eq_top, ← Algebra.adjoin_singleton_eq_range_aeval]
  have ⟨f, (hf : aeval x f = 0), hfp⟩ := SetLike.not_le_iff_exists.mp
    (Polynomial.not_ker_le_map_C_of_surjective_of_weaklyQuasiFiniteAt _ H₀ p)
  obtain ⟨n, hfn⟩ : exists x, algebraMap R S (f.coeff x) ∉ p := by simpa [Ideal.mem_map_C_iff] using! hfp
  clear hfp
  induction hm : f.natDegree using Nat.strong_induction_on generalizing f n with | h m IH =>
  obtain (_ | m) := m
  · obtain ⟨r, rfl⟩ := natDegree_eq_zero.mp hm
    cases n <;> aesop
  by_cases Hfp : algebraMap _ _ f.leadingCoeff in p
  · obtain ⟨a, ha⟩ := H.le (isIntegral_leadingCoeff_smul f x hf)
    refine IH _ ?_ (f.eraseLead + C a * X ^ m) (hm := rfl) ?_ n ?_
    · suffices f.eraseLead.natDegree <= m by compute_degree!
      exact (eraseLead_natDegree_le ..).trans (by lia)
    · simp [← self_sub_monomial_natDegree_leadingCoeff, hf, hm, pow_succ', ← Algebra.smul_def,
        ← Algebra.smul_mul_assoc, ← ha]
    · suffices algebraMap R S (f.coeff n) + algebraMap R S (if n = m then a else 0) ∉ p by
        simpa [eraseLead_coeff, show n != f.natDegree by rintro rfl; exact hfn (by simpa)]
      rwa [Ideal.add_mem_iff_left]
      split_ifs
      · convert p.mul_mem_right x Hfp
        simpa [Algebra.smul_def] using! ha
      · simp
  · refine zariskisMainProperty_iff_exists_saturation_eq_top.mpr ⟨_, Hfp, isIntegral_algebraMap, ?_⟩
    rw [← top_le_iff]; rw [← hx]
    refine Algebra.adjoin_singleton_le ⟨_, ⟨1, rfl⟩, ?_⟩
    simpa [Algebra.smul_def] using! isIntegral_leadingCoeff_smul f x hf
-/
private lemma ZariskisMainProperty.of_adjoin_eq_top
    (p : Ideal S) [p.IsPrime] [Algebra.WeaklyQuasiFiniteAt R p]
    (x : S) (hx : Algebra.adjoin R {x} = ⊤) : ZariskisMainProperty R p := by
  wlog H : integralClosure R S = ⊥
  · let inst : Algebra (integralClosure R S) (Localization.AtPrime p) :=
      OreLocalization.instAlgebra
    have inst : Algebra.WeaklyQuasiFiniteAt (integralClosure R S) p :=
      .of_restrictScalars R (integralClosure R S) _
    refine .restrictScalars (this p x ?_ (integralClosure_idem (R := R)))
    suffices ⊤ <= (Algebra.adjoin (integralClosure R S) {x}).restrictScalars R from
      top_le_iff.mp fun x _ => (Subalgebra.mem_restrictScalars _).mp (this trivial)
    refine hx.ge.trans ?_
    rw [Algebra.restrictScalars_adjoin]
    exact Algebra.adjoin_mono (by simp)
  have H₀ : Function.Surjective (aeval (R := R) x) := by
    rwa [← AlgHom.range_eq_top, ← Algebra.adjoin_singleton_eq_range_aeval]
  have ⟨f, (hf : aeval x f = 0), hfp⟩ := SetLike.not_le_iff_exists.mp
    (Polynomial.not_ker_le_map_C_of_surjective_of_weaklyQuasiFiniteAt _ H₀ p)
  obtain ⟨n, hfn⟩ : exists x, algebraMap R S (f.coeff x) ∉ p := by simpa [Ideal.mem_map_C_iff] using! hfp
  clear hfp
  induction hm : f.natDegree using Nat.strong_induction_on generalizing f n with | h m IH =>
  obtain (_ | m) := m
  · obtain ⟨r, rfl⟩ := natDegree_eq_zero.mp hm
    cases n <;> aesop
  by_cases Hfp : algebraMap _ _ f.leadingCoeff in p
  · obtain ⟨a, ha⟩ := H.le (isIntegral_leadingCoeff_smul f x hf)
    refine IH _ ?_ (f.eraseLead + C a * X ^ m) (hm := rfl) ?_ n ?_
    · suffices f.eraseLead.natDegree <= m by compute_degree!
      exact (eraseLead_natDegree_le ..).trans (by lia)
    · simp [← self_sub_monomial_natDegree_leadingCoeff, hf, hm, pow_succ', ← Algebra.smul_def,
        ← Algebra.smul_mul_assoc, ← ha]
    · suffices algebraMap R S (f.coeff n) + algebraMap R S (if n = m then a else 0) ∉ p by
        simpa [eraseLead_coeff, show n != f.natDegree by rintro rfl; exact hfn (by simpa)]
      rwa [Ideal.add_mem_iff_left]
      split_ifs
      · convert p.mul_mem_right x Hfp
        simpa [Algebra.smul_def] using! ha
      · simp
  · refine zariskisMainProperty_iff_exists_saturation_eq_top.mpr ⟨_, Hfp, isIntegral_algebraMap, ?_⟩
    rw [← top_le_iff]; rw [← hx]
    refine Algebra.adjoin_singleton_le ⟨_, ⟨1, rfl⟩, ?_⟩
    simpa [Algebra.smul_def] using! isIntegral_leadingCoeff_smul f x hf

-- Subsumed by `ZariskisMainProperty.of_finiteType`.
/--
lemma `ZariskisMainProperty.of_algHom_polynomial` / 引理 `ZariskisMainProperty.of_algHom_polynomial`

English:
lemma ZariskisMainProperty.of_algHom_polynomial
  proof: by
  wlog H : integralClosure R S = ⊥
  · let inst : Algebra (integralClosure R S) (Localization.AtPrime p) :=
      OreLocalization.instAlgebra
    have inst : Algebra.WeaklyQuasiFiniteAt (integralClosure R S) p :=
      .of_restrictScalars R (integralClosure R S) _
    refine .restrictScalars (this p (aeval (f X)) ?_ (integralClosure_idem (R := R)))
    refine RingHom.Finite.of_comp_finite (f := mapRingHom (algebraMap R _)) ?_
    convert! (show f.toRingHom.Finite from hf)
    ext <;> simp [show forall x, f (C x) = algebraMap _ _ x from f.commutes]
  replace hf : ¬ conductor R (f X) <= p := by
    intro hp
    rw [← ‹p.IsPrime›.isRadical.radical_le_iff] at hp
    set J := (conductor R (f X)).radical
    have inst : (p.map (Ideal.Quotient.mk J)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by simpa using hp)
    have inst : IsReduced (S ⧸ J) :=
        (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical _)
    have inst : WeaklyQuasiFiniteAt R (p.map (Ideal.Quotient.mk J)) := by
      refine .of_surjectiveOnStalks p _ (Ideal.Quotient.mkₐ R _)
        (RingHom.surjectiveOnStalks_of_surjective Ideal.Quotient.mk_surjective)
        ((Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective p).trans ?_).symm
      simpa [← RingHom.ker_eq_comap_bot]
    refine not_isStronglyTranscendental_of_weaklyQuasiFiniteAt ?_ (p.map (Ideal.Quotient.mk J))
      (isStronglyTranscendental_mk_radical_conductor H (f X) (by convert! hf; ext; simp))
    convert! (RingHom.Finite.of_surjective _ (Ideal.Quotient.mk_surjective (I := J))).comp hf
      using 1
    ext <;> simp [show forall x, f (C x) = algebraMap _ _ x from f.commutes, J]
  obtain ⟨x, hx, hxp⟩ := SetLike.not_le_iff_exists.mp hf
  replace hx (a : _) : x * a in f.range := by simpa [← AlgHom.map_adjoin_singleton f] using hx a
  refine ZariskisMainProperty.trans (S := f.range) _ ?_ ?_
  · have : Algebra.WeaklyQuasiFiniteAt R (p.under f.range) := by
      let := Localization.AtPrime.algebraOfLiesOver (p.under f.range) p
      let e : Localization.AtPrime (p.under f.range) ≃ₐ[R] Localization.AtPrime p :=
        .ofBijective (IsScalarTower.toAlgHom _ _ _)
          (Localization.localRingHom_bijective_of_not_conductor_le hf
            (by simp [← AlgHom.map_adjoin_singleton f]) _)
      exact .of_algHom_localization _ _ e.symm.toAlgHom e.symm.surjective
    refine .of_adjoin_eq_top _ ⟨f X, X, rfl⟩ ?_
    simp [← (Subalgebra.map_injective (f := Subalgebra.val _) Subtype.val_injective).eq_iff,
      ← AlgHom.map_adjoin_singleton f, Subalgebra.range_val]
  · refine ⟨⟨x, by simpa using hx 1⟩, hxp, top_le_iff.mp fun s _ => ⟨_, ⟨1, rfl⟩, ?_⟩⟩
    simpa [Algebra.mem_bot] using hx s

中文:
引理 ZariskisMainProperty.of_algHom_polynomial
  证明: by
  wlog H : integralClosure R S = ⊥
  · let inst : Algebra (integralClosure R S) (Localization.AtPrime p) :=
      OreLocalization.instAlgebra
    have inst : Algebra.WeaklyQuasiFiniteAt (integralClosure R S) p :=
      .of_restrictScalars R (integralClosure R S) _
    refine .restrictScalars (this p (aeval (f X)) ?_ (integralClosure_idem (R := R)))
    refine RingHom.Finite.of_comp_finite (f := mapRingHom (algebraMap R _)) ?_
    convert! (show f.toRingHom.Finite from hf)
    ext <;> simp [show forall x, f (C x) = algebraMap _ _ x from f.commutes]
  replace hf : ¬ conductor R (f X) <= p := by
    intro hp
    rw [← ‹p.IsPrime›.isRadical.radical_le_iff] at hp
    set J := (conductor R (f X)).radical
    have inst : (p.map (Ideal.Quotient.mk J)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by simpa using hp)
    have inst : IsReduced (S ⧸ J) :=
        (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical _)
    have inst : WeaklyQuasiFiniteAt R (p.map (Ideal.Quotient.mk J)) := by
      refine .of_surjectiveOnStalks p _ (Ideal.Quotient.mkₐ R _)
        (RingHom.surjectiveOnStalks_of_surjective Ideal.Quotient.mk_surjective)
        ((Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective p).trans ?_).symm
      simpa [← RingHom.ker_eq_comap_bot]
    refine not_isStronglyTranscendental_of_weaklyQuasiFiniteAt ?_ (p.map (Ideal.Quotient.mk J))
      (isStronglyTranscendental_mk_radical_conductor H (f X) (by convert! hf; ext; simp))
    convert! (RingHom.Finite.of_surjective _ (Ideal.Quotient.mk_surjective (I := J))).comp hf
      using 1
    ext <;> simp [show forall x, f (C x) = algebraMap _ _ x from f.commutes, J]
  obtain ⟨x, hx, hxp⟩ := SetLike.not_le_iff_exists.mp hf
  replace hx (a : _) : x * a in f.range := by simpa [← AlgHom.map_adjoin_singleton f] using hx a
  refine ZariskisMainProperty.trans (S := f.range) _ ?_ ?_
  · have : Algebra.WeaklyQuasiFiniteAt R (p.under f.range) := by
      let := Localization.AtPrime.algebraOfLiesOver (p.under f.range) p
      let e : Localization.AtPrime (p.under f.range) ≃ₐ[R] Localization.AtPrime p :=
        .ofBijective (IsScalarTower.toAlgHom _ _ _)
          (Localization.localRingHom_bijective_of_not_conductor_le hf
            (by simp [← AlgHom.map_adjoin_singleton f]) _)
      exact .of_algHom_localization _ _ e.symm.toAlgHom e.symm.surjective
    refine .of_adjoin_eq_top _ ⟨f X, X, rfl⟩ ?_
    simp [← (Subalgebra.map_injective (f := Subalgebra.val _) Subtype.val_injective).eq_iff,
      ← AlgHom.map_adjoin_singleton f, Subalgebra.range_val]
  · refine ⟨⟨x, by simpa using hx 1⟩, hxp, top_le_iff.mp fun s _ => ⟨_, ⟨1, rfl⟩, ?_⟩⟩
    simpa [Algebra.mem_bot] using hx s
-/
private lemma ZariskisMainProperty.of_algHom_polynomial
    (p : Ideal S) [p.IsPrime] [Algebra.WeaklyQuasiFiniteAt R p]
    (f : R[X] ->ₐ[R] S) (hf : f.Finite) : ZariskisMainProperty R p := by
  wlog H : integralClosure R S = ⊥
  · let inst : Algebra (integralClosure R S) (Localization.AtPrime p) :=
      OreLocalization.instAlgebra
    have inst : Algebra.WeaklyQuasiFiniteAt (integralClosure R S) p :=
      .of_restrictScalars R (integralClosure R S) _
    refine .restrictScalars (this p (aeval (f X)) ?_ (integralClosure_idem (R := R)))
    refine RingHom.Finite.of_comp_finite (f := mapRingHom (algebraMap R _)) ?_
    convert! (show f.toRingHom.Finite from hf)
    ext <;> simp [show forall x, f (C x) = algebraMap _ _ x from f.commutes]
  replace hf : ¬ conductor R (f X) <= p := by
    intro hp
    rw [← ‹p.IsPrime›.isRadical.radical_le_iff] at hp
    set J := (conductor R (f X)).radical
    have inst : (p.map (Ideal.Quotient.mk J)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by simpa using hp)
    have inst : IsReduced (S ⧸ J) :=
        (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical _)
    have inst : WeaklyQuasiFiniteAt R (p.map (Ideal.Quotient.mk J)) := by
      refine .of_surjectiveOnStalks p _ (Ideal.Quotient.mkₐ R _)
        (RingHom.surjectiveOnStalks_of_surjective Ideal.Quotient.mk_surjective)
        ((Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective p).trans ?_).symm
      simpa [← RingHom.ker_eq_comap_bot]
    refine not_isStronglyTranscendental_of_weaklyQuasiFiniteAt ?_ (p.map (Ideal.Quotient.mk J))
      (isStronglyTranscendental_mk_radical_conductor H (f X) (by convert! hf; ext; simp))
    convert! (RingHom.Finite.of_surjective _ (Ideal.Quotient.mk_surjective (I := J))).comp hf
      using 1
    ext <;> simp [show forall x, f (C x) = algebraMap _ _ x from f.commutes, J]
  obtain ⟨x, hx, hxp⟩ := SetLike.not_le_iff_exists.mp hf
  replace hx (a : _) : x * a in f.range := by simpa [← AlgHom.map_adjoin_singleton f] using hx a
  refine ZariskisMainProperty.trans (S := f.range) _ ?_ ?_
  · have : Algebra.WeaklyQuasiFiniteAt R (p.under f.range) := by
      let := Localization.AtPrime.algebraOfLiesOver (p.under f.range) p
      let e : Localization.AtPrime (p.under f.range) ≃ₐ[R] Localization.AtPrime p :=
        .ofBijective (IsScalarTower.toAlgHom _ _ _)
          (Localization.localRingHom_bijective_of_not_conductor_le hf
            (by simp [← AlgHom.map_adjoin_singleton f]) _)
      exact .of_algHom_localization _ _ e.symm.toAlgHom e.symm.surjective
    refine .of_adjoin_eq_top _ ⟨f X, X, rfl⟩ ?_
    simp [← (Subalgebra.map_injective (f := Subalgebra.val _) Subtype.val_injective).eq_iff,
      ← AlgHom.map_adjoin_singleton f, Subalgebra.range_val]
  · refine ⟨⟨x, by simpa using hx 1⟩, hxp, top_le_iff.mp fun s _ => ⟨_, ⟨1, rfl⟩, ?_⟩⟩
    simpa [Algebra.mem_bot] using hx s

open scoped Pointwise in
-- Subsumed by `ZariskisMainProperty.of_finiteType`.
/--
lemma `ZariskisMainProperty.of_algHom_mvPolynomial` / 引理 `ZariskisMainProperty.of_algHom_mvPolynomial`

English:
lemma ZariskisMainProperty.of_algHom_mvPolynomial
  proof: by
  classical
  induction n generalizing R S with
  | zero =>
    have : Module.Finite R S := by
      rw [← RingHom.finite_algebraMap]
      convert! RingHom.Finite.comp hf (RingHom.Finite.of_surjective _ (MvPolynomial.C_surjective _))
      exact f.comp_algebraMap.symm
    exact .of_isIntegral _
  | succ n IH =>
    let f' := f.comp (MvPolynomial.finSuccEquiv _ _).symm.toAlgHom
    let := (f'.toRingHom.comp C).toAlgebra
    have : IsScalarTower R (MvPolynomial (Fin n) R) S := .of_algebraMap_eq fun r =>
      (f.commutes r).symm.trans congr(f ($(MvPolynomial.finSuccEquiv_comp_C_eq_C n) r)).symm
    let f'' : (MvPolynomial (Fin n) R)[X] ->ₐ[MvPolynomial (Fin n) R] S :=
      ⟨f'.toRingHom, fun _ => rfl⟩
    have : Algebra.WeaklyQuasiFiniteAt (MvPolynomial (Fin n) R) p := by
      exact .of_restrictScalars R _ _
    have := ZariskisMainProperty.of_algHom_polynomial p f''
      (RingHom.Finite.comp hf (MvPolynomial.finSuccEquiv R n).symm.toRingEquiv.finite)
    choose r hrp hr m hm using zariskisMainProperty_iff.mp this
    obtain ⟨⟨s, hs⟩⟩ : Algebra.FiniteType R S := by
      rw [← RingHom.finiteType_algebraMap]; rw [← f.comp_algebraMap]
      exact RingHom.FiniteType.comp hf.finiteType (RingHom.finiteType_algebraMap.mpr inferInstance)
    let R' : Subalgebra R S :=
      Algebra.adjoin R ↑(Finset.univ.image (f ∘ .X ∘ Fin.succ) union r ^ (s.sup m) • s union {r})
    have hrR' : r in R' := Algebra.subset_adjoin (by simp)
    have : Algebra.WeaklyQuasiFiniteAt R (p.under R') := by
      let := Localization.AtPrime.algebraOfLiesOver (p.under R') p
      let e : Localization.AtPrime (p.under R') ≃ₐ[R] Localization.AtPrime p :=
.ofBijective (IsScalarTower.toAlgHom _ _ _) by
          refine Localization.localRingHom_bijective_of_saturated_inf_eq_top _ ?_ _
          rw [← top_le_iff]; rw [← hs]; rw [Algebra.adjoin_le_iff]
          intro x hx
          refine ⟨r ^ (s.sup m), pow_mem (by exact ⟨hrp, hrR'⟩) _, Algebra.subset_adjoin ?_⟩
          simp [Set.smul_mem_smul_set hx, ← smul_eq_mul]
      exact .of_algHom_localization _ _ e.symm.toAlgHom e.symm.surjective
    let φ : MvPolynomial (Fin n) R ->ₐ[R] R' :=
      MvPolynomial.aeval fun i => ⟨f (.X i.succ), Algebra.subset_adjoin (by simp)⟩
have := IH (R := R) (S := R') (p.under R') φ by
      refine RingHom.finite_iff_isIntegral_and_finiteType.mpr ⟨?_, ?_⟩
      · let := φ.toAlgebra
have : IsScalarTower (MvPolynomial (Fin n) R) R' S := .of_algebraMap_eq' by
          ext <;> simp [φ, (f'.toRingHom.comp C).algebraMap_toAlgebra, φ.algebraMap_toAlgebra, f',
            MvPolynomial.finSuccEquiv, MvPolynomial.optionEquivLeft]
        refine algebraMap_isIntegral_iff.mpr (integralClosure_eq_top_iff.mp ?_)
        apply Subalgebra.restrictScalars_injective R
        rw [← (Subalgebra.map_injective (f := R'.val) Subtype.val_injective).eq_iff]
        simp only [Subalgebra.restrictScalars_top, Algebra.map_top]
        refine le_antisymm (Set.image_subset_range _ _) ?_
        suffices (forall (a : Fin n), IsIntegral (MvPolynomial (Fin n) R) (f (MvPolynomial.X a.succ))) ∧
            forall a in s, IsIntegral (MvPolynomial (Fin n) R) (r ^ s.sup m * a) by
          simp +contextual only [Subalgebra.range_val, Algebra.adjoin_le_iff, Subalgebra.coe_map,
            Subalgebra.coe_val, Set.subset_def, SetLike.mem_coe, Algebra.mem_adjoin_of_mem,
            Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right, R']
          simpa [R', mem_integralClosure_iff,
            ← isIntegral_algebraMap_iff (FaithfulSMul.algebraMap_injective R' S),
            forall_and, hr, or_imp, Finset.mem_smul_finset]
        refine ⟨fun i => ?_, fun a has => ?_⟩
        · convert! isIntegral_algebraMap (x := MvPolynomial.X i)
          simp [RingHom.algebraMap_toAlgebra, f', MvPolynomial.finSuccEquiv,
            MvPolynomial.optionEquivLeft]
        · rw [← Nat.sub_add_cancel (s.le_sup has), pow_add, mul_assoc]
          exact (hr.pow _).mul (hm _)
      · refine .of_comp_finiteType (f := algebraMap R _) ?_
        rw [AlgHom.toRingHom_eq_coe]; rw [φ.comp_algebraMap]; rw [RingHom.finiteType_algebraMap]
        exact ⟨(Subalgebra.fg_top _).mpr ⟨_, rfl⟩⟩
    refine this.trans _ ⟨⟨r, hrR'⟩, hrp, ?_⟩
    suffices ⊤ <= R'.saturation (.powers r) (by simpa [Submonoid.powers_le]) by
      simpa [SetLike.le_def, Subalgebra.smul_def, Submonoid.mem_powers_iff,
        SetLike.ext_iff, Algebra.mem_bot] using this
    rw [← hs]; rw [Algebra.adjoin_le_iff]
    intro x hx
    refine ⟨_, ⟨s.sup m, rfl⟩, Algebra.subset_adjoin ?_⟩
    simp [Set.smul_mem_smul_set hx, ← smul_eq_mul]

中文:
引理 ZariskisMainProperty.of_algHom_mvPolynomial
  证明: by
  classical
  induction n generalizing R S with
  | zero =>
    have : Module.Finite R S := by
      rw [← RingHom.finite_algebraMap]
      convert! RingHom.Finite.comp hf (RingHom.Finite.of_surjective _ (MvPolynomial.C_surjective _))
      exact f.comp_algebraMap.symm
    exact .of_isIntegral _
  | succ n IH =>
    let f' := f.comp (MvPolynomial.finSuccEquiv _ _).symm.toAlgHom
    let := (f'.toRingHom.comp C).toAlgebra
    have : IsScalarTower R (MvPolynomial (Fin n) R) S := .of_algebraMap_eq fun r =>
      (f.commutes r).symm.trans congr(f ($(MvPolynomial.finSuccEquiv_comp_C_eq_C n) r)).symm
    let f'' : (MvPolynomial (Fin n) R)[X] ->ₐ[MvPolynomial (Fin n) R] S :=
      ⟨f'.toRingHom, fun _ => rfl⟩
    have : Algebra.WeaklyQuasiFiniteAt (MvPolynomial (Fin n) R) p := by
      exact .of_restrictScalars R _ _
    have := ZariskisMainProperty.of_algHom_polynomial p f''
      (RingHom.Finite.comp hf (MvPolynomial.finSuccEquiv R n).symm.toRingEquiv.finite)
    choose r hrp hr m hm using zariskisMainProperty_iff.mp this
    obtain ⟨⟨s, hs⟩⟩ : Algebra.FiniteType R S := by
      rw [← RingHom.finiteType_algebraMap]; rw [← f.comp_algebraMap]
      exact RingHom.FiniteType.comp hf.finiteType (RingHom.finiteType_algebraMap.mpr inferInstance)
    let R' : Subalgebra R S :=
      Algebra.adjoin R ↑(Finset.univ.image (f ∘ .X ∘ Fin.succ) union r ^ (s.sup m) • s union {r})
    have hrR' : r in R' := Algebra.subset_adjoin (by simp)
    have : Algebra.WeaklyQuasiFiniteAt R (p.under R') := by
      let := Localization.AtPrime.algebraOfLiesOver (p.under R') p
      let e : Localization.AtPrime (p.under R') ≃ₐ[R] Localization.AtPrime p :=
.ofBijective (IsScalarTower.toAlgHom _ _ _) by
          refine Localization.localRingHom_bijective_of_saturated_inf_eq_top _ ?_ _
          rw [← top_le_iff]; rw [← hs]; rw [Algebra.adjoin_le_iff]
          intro x hx
          refine ⟨r ^ (s.sup m), pow_mem (by exact ⟨hrp, hrR'⟩) _, Algebra.subset_adjoin ?_⟩
          simp [Set.smul_mem_smul_set hx, ← smul_eq_mul]
      exact .of_algHom_localization _ _ e.symm.toAlgHom e.symm.surjective
    let φ : MvPolynomial (Fin n) R ->ₐ[R] R' :=
      MvPolynomial.aeval fun i => ⟨f (.X i.succ), Algebra.subset_adjoin (by simp)⟩
have := IH (R := R) (S := R') (p.under R') φ by
      refine RingHom.finite_iff_isIntegral_and_finiteType.mpr ⟨?_, ?_⟩
      · let := φ.toAlgebra
have : IsScalarTower (MvPolynomial (Fin n) R) R' S := .of_algebraMap_eq' by
          ext <;> simp [φ, (f'.toRingHom.comp C).algebraMap_toAlgebra, φ.algebraMap_toAlgebra, f',
            MvPolynomial.finSuccEquiv, MvPolynomial.optionEquivLeft]
        refine algebraMap_isIntegral_iff.mpr (integralClosure_eq_top_iff.mp ?_)
        apply Subalgebra.restrictScalars_injective R
        rw [← (Subalgebra.map_injective (f := R'.val) Subtype.val_injective).eq_iff]
        simp only [Subalgebra.restrictScalars_top, Algebra.map_top]
        refine le_antisymm (Set.image_subset_range _ _) ?_
        suffices (forall (a : Fin n), IsIntegral (MvPolynomial (Fin n) R) (f (MvPolynomial.X a.succ))) ∧
            forall a in s, IsIntegral (MvPolynomial (Fin n) R) (r ^ s.sup m * a) by
          simp +contextual only [Subalgebra.range_val, Algebra.adjoin_le_iff, Subalgebra.coe_map,
            Subalgebra.coe_val, Set.subset_def, SetLike.mem_coe, Algebra.mem_adjoin_of_mem,
            Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right, R']
          simpa [R', mem_integralClosure_iff,
            ← isIntegral_algebraMap_iff (FaithfulSMul.algebraMap_injective R' S),
            forall_and, hr, or_imp, Finset.mem_smul_finset]
        refine ⟨fun i => ?_, fun a has => ?_⟩
        · convert! isIntegral_algebraMap (x := MvPolynomial.X i)
          simp [RingHom.algebraMap_toAlgebra, f', MvPolynomial.finSuccEquiv,
            MvPolynomial.optionEquivLeft]
        · rw [← Nat.sub_add_cancel (s.le_sup has), pow_add, mul_assoc]
          exact (hr.pow _).mul (hm _)
      · refine .of_comp_finiteType (f := algebraMap R _) ?_
        rw [AlgHom.toRingHom_eq_coe]; rw [φ.comp_algebraMap]; rw [RingHom.finiteType_algebraMap]
        exact ⟨(Subalgebra.fg_top _).mpr ⟨_, rfl⟩⟩
    refine this.trans _ ⟨⟨r, hrR'⟩, hrp, ?_⟩
    suffices ⊤ <= R'.saturation (.powers r) (by simpa [Submonoid.powers_le]) by
      simpa [SetLike.le_def, Subalgebra.smul_def, Submonoid.mem_powers_iff,
        SetLike.ext_iff, Algebra.mem_bot] using this
    rw [← hs]; rw [Algebra.adjoin_le_iff]
    intro x hx
    refine ⟨_, ⟨s.sup m, rfl⟩, Algebra.subset_adjoin ?_⟩
    simp [Set.smul_mem_smul_set hx, ← smul_eq_mul]
-/
private lemma ZariskisMainProperty.of_algHom_mvPolynomial
    (p : Ideal S) [p.IsPrime] [Algebra.WeaklyQuasiFiniteAt R p] {n : Nat}
    (f : MvPolynomial (Fin n) R ->ₐ[R] S) (hf : f.Finite) : ZariskisMainProperty R p := by
  classical
  induction n generalizing R S with
  | zero =>
    have : Module.Finite R S := by
      rw [← RingHom.finite_algebraMap]
      convert! RingHom.Finite.comp hf (RingHom.Finite.of_surjective _ (MvPolynomial.C_surjective _))
      exact f.comp_algebraMap.symm
    exact .of_isIntegral _
  | succ n IH =>
    let f' := f.comp (MvPolynomial.finSuccEquiv _ _).symm.toAlgHom
    let := (f'.toRingHom.comp C).toAlgebra
    have : IsScalarTower R (MvPolynomial (Fin n) R) S := .of_algebraMap_eq fun r =>
      (f.commutes r).symm.trans congr(f ($(MvPolynomial.finSuccEquiv_comp_C_eq_C n) r)).symm
    let f'' : (MvPolynomial (Fin n) R)[X] ->ₐ[MvPolynomial (Fin n) R] S :=
      ⟨f'.toRingHom, fun _ => rfl⟩
    have : Algebra.WeaklyQuasiFiniteAt (MvPolynomial (Fin n) R) p := by
      exact .of_restrictScalars R _ _
    have := ZariskisMainProperty.of_algHom_polynomial p f''
      (RingHom.Finite.comp hf (MvPolynomial.finSuccEquiv R n).symm.toRingEquiv.finite)
    choose r hrp hr m hm using zariskisMainProperty_iff.mp this
    obtain ⟨⟨s, hs⟩⟩ : Algebra.FiniteType R S := by
      rw [← RingHom.finiteType_algebraMap]; rw [← f.comp_algebraMap]
      exact RingHom.FiniteType.comp hf.finiteType (RingHom.finiteType_algebraMap.mpr inferInstance)
    let R' : Subalgebra R S :=
      Algebra.adjoin R ↑(Finset.univ.image (f ∘ .X ∘ Fin.succ) union r ^ (s.sup m) • s union {r})
    have hrR' : r in R' := Algebra.subset_adjoin (by simp)
    have : Algebra.WeaklyQuasiFiniteAt R (p.under R') := by
      let := Localization.AtPrime.algebraOfLiesOver (p.under R') p
      let e : Localization.AtPrime (p.under R') ≃ₐ[R] Localization.AtPrime p :=
.ofBijective (IsScalarTower.toAlgHom _ _ _) by
          refine Localization.localRingHom_bijective_of_saturated_inf_eq_top _ ?_ _
          rw [← top_le_iff]; rw [← hs]; rw [Algebra.adjoin_le_iff]
          intro x hx
          refine ⟨r ^ (s.sup m), pow_mem (by exact ⟨hrp, hrR'⟩) _, Algebra.subset_adjoin ?_⟩
          simp [Set.smul_mem_smul_set hx, ← smul_eq_mul]
      exact .of_algHom_localization _ _ e.symm.toAlgHom e.symm.surjective
    let φ : MvPolynomial (Fin n) R ->ₐ[R] R' :=
      MvPolynomial.aeval fun i => ⟨f (.X i.succ), Algebra.subset_adjoin (by simp)⟩
have := IH (R := R) (S := R') (p.under R') φ by
      refine RingHom.finite_iff_isIntegral_and_finiteType.mpr ⟨?_, ?_⟩
      · let := φ.toAlgebra
have : IsScalarTower (MvPolynomial (Fin n) R) R' S := .of_algebraMap_eq' by
          ext <;> simp [φ, (f'.toRingHom.comp C).algebraMap_toAlgebra, φ.algebraMap_toAlgebra, f',
            MvPolynomial.finSuccEquiv, MvPolynomial.optionEquivLeft]
        refine algebraMap_isIntegral_iff.mpr (integralClosure_eq_top_iff.mp ?_)
        apply Subalgebra.restrictScalars_injective R
        rw [← (Subalgebra.map_injective (f := R'.val) Subtype.val_injective).eq_iff]
        simp only [Subalgebra.restrictScalars_top, Algebra.map_top]
        refine le_antisymm (Set.image_subset_range _ _) ?_
        suffices (forall (a : Fin n), IsIntegral (MvPolynomial (Fin n) R) (f (MvPolynomial.X a.succ))) ∧
            forall a in s, IsIntegral (MvPolynomial (Fin n) R) (r ^ s.sup m * a) by
          simp +contextual only [Subalgebra.range_val, Algebra.adjoin_le_iff, Subalgebra.coe_map,
            Subalgebra.coe_val, Set.subset_def, SetLike.mem_coe, Algebra.mem_adjoin_of_mem,
            Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right, R']
          simpa [R', mem_integralClosure_iff,
            ← isIntegral_algebraMap_iff (FaithfulSMul.algebraMap_injective R' S),
            forall_and, hr, or_imp, Finset.mem_smul_finset]
        refine ⟨fun i => ?_, fun a has => ?_⟩
        · convert! isIntegral_algebraMap (x := MvPolynomial.X i)
          simp [RingHom.algebraMap_toAlgebra, f', MvPolynomial.finSuccEquiv,
            MvPolynomial.optionEquivLeft]
        · rw [← Nat.sub_add_cancel (s.le_sup has), pow_add, mul_assoc]
          exact (hr.pow _).mul (hm _)
      · refine .of_comp_finiteType (f := algebraMap R _) ?_
        rw [AlgHom.toRingHom_eq_coe]; rw [φ.comp_algebraMap]; rw [RingHom.finiteType_algebraMap]
        exact ⟨(Subalgebra.fg_top _).mpr ⟨_, rfl⟩⟩
    refine this.trans _ ⟨⟨r, hrR'⟩, hrp, ?_⟩
    suffices ⊤ <= R'.saturation (.powers r) (by simpa [Submonoid.powers_le]) by
      simpa [SetLike.le_def, Subalgebra.smul_def, Submonoid.mem_powers_iff,
        SetLike.ext_iff, Algebra.mem_bot] using this
    rw [← hs]; rw [Algebra.adjoin_le_iff]
    intro x hx
    refine ⟨_, ⟨s.sup m, rfl⟩, Algebra.subset_adjoin ?_⟩
    simp [Set.smul_mem_smul_set hx, ← smul_eq_mul]

end FixedUniverse

@[stacks 00Q9]
/--
lemma `ZariskisMainProperty.of_finiteType_of_weaklyQuasiFiniteAt.` / 引理 `ZariskisMainProperty.of_finiteType_of_weaklyQuasiFiniteAt.`

English:
lemma ZariskisMainProperty.of_finiteType_of_weaklyQuasiFiniteAt.{u,
  statement: v}
  proof: by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹_›
  have : Small.{u} S := small_of_surjective hf
  have := ZariskisMainProperty.of_algHom_mvPolynomial (p.comap (Shrink.algEquiv R S).toRingHom)
    ((Shrink.algEquiv R S).symm.toAlgHom.comp f)
    (.of_surjective _ <| (Shrink.algEquiv R S).symm.surjective.comp hf)
  rw [zariskisMainProperty_iff'] at this ⊢
  obtain ⟨r, hr, H⟩ := this
  refine ⟨Shrink.algEquiv R S r, hr, fun x => ?_⟩
  obtain ⟨m, hm⟩ := H ((Shrink.algEquiv R S).symm x)
  exact ⟨m, by simpa [-Shrink.algEquiv_apply, -Shrink.algEquiv_symm_apply]
    using hm.map (Shrink.algEquiv R S).toAlgHom⟩

中文:
引理 ZariskisMainProperty.of_finiteType_of_weaklyQuasiFiniteAt.{u,
  结论: v}
  证明: by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹_›
  have : Small.{u} S := small_of_surjective hf
  have := ZariskisMainProperty.of_algHom_mvPolynomial (p.comap (Shrink.algEquiv R S).toRingHom)
    ((Shrink.algEquiv R S).symm.toAlgHom.comp f)
    (.of_surjective _ <| (Shrink.algEquiv R S).symm.surjective.comp hf)
  rw [zariskisMainProperty_iff'] at this ⊢
  obtain ⟨r, hr, H⟩ := this
  refine ⟨Shrink.algEquiv R S r, hr, fun x => ?_⟩
  obtain ⟨m, hm⟩ := H ((Shrink.algEquiv R S).symm x)
  exact ⟨m, by simpa [-Shrink.algEquiv_apply, -Shrink.algEquiv_symm_apply]
    using hm.map (Shrink.algEquiv R S).toAlgHom⟩

Depends on / 依赖: Algebra, Algebra.FiniteType.iff_quotient_mvPolynomial, FiniteType, Shrink, Shrink.algEquiv, ZariskisMainProperty, ZariskisMainProperty.of_algHom_mvPolynomial, algEquiv, iff_quotient_mvPolynomial, of_algHom_mvPolynomial, of_surjective, p.comap, small_of_surjective, surjective, symm.surjective.comp, symm.toAlgHom.comp, toAlgHom, toRingHom, zariskisMainProperty_iff
-/
lemma ZariskisMainProperty.of_finiteType_of_weaklyQuasiFiniteAt.{u, v}
    {R : Type u} {S : Type v} [CommRing R]
    [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    (p : Ideal S) [p.IsPrime] [Algebra.WeaklyQuasiFiniteAt R p] : ZariskisMainProperty R p := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹_›
  have : Small.{u} S := small_of_surjective hf
  have := ZariskisMainProperty.of_algHom_mvPolynomial (p.comap (Shrink.algEquiv R S).toRingHom)
    ((Shrink.algEquiv R S).symm.toAlgHom.comp f)
    (.of_surjective _ <| (Shrink.algEquiv R S).symm.surjective.comp hf)
  rw [zariskisMainProperty_iff'] at this ⊢
  obtain ⟨r, hr, H⟩ := this
  refine ⟨Shrink.algEquiv R S r, hr, fun x => ?_⟩
  obtain ⟨m, hm⟩ := H ((Shrink.algEquiv R S).symm x)
  exact ⟨m, by simpa [-Shrink.algEquiv_apply, -Shrink.algEquiv_symm_apply]
    using hm.map (Shrink.algEquiv R S).toAlgHom⟩

/--
The algebraic version of **Zariski's Main Theorem**:
Given a finite type `R`-algebra `S` that is quasi-finite at a prime `p`,
there exists a `f ∉ p` such that `S[1/f]` is isomorphic to `R'[1/f]` where `R'` is the integral
closure of `R` in `S`.
-/
@[stacks 00Q9]
/--
lemma `ZariskisMainProperty.of_finiteType.` / 引理 `ZariskisMainProperty.of_finiteType.`

English:
lemma ZariskisMainProperty.of_finiteType.{u,
  given: v} {R
  statement: Type u} {S : Type v} [CommRing R]
  proof: .of_finiteType_of_weaklyQuasiFiniteAt _

中文:
引理 ZariskisMainProperty.of_finiteType.{u,
  条件: v} {R
  结论: 类型u} {S : 类型v} [交换环 R]
  证明: .of_finiteType_of_weaklyQuasiFiniteAt _

Depends on / 依赖: of_finiteType_of_weaklyQuasiFiniteAt
-/
lemma ZariskisMainProperty.of_finiteType.{u, v} {R : Type u} {S : Type v} [CommRing R]
    [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    (p : Ideal S) [p.IsPrime] [Algebra.QuasiFiniteAt R p] : ZariskisMainProperty R p :=
  .of_finiteType_of_weaklyQuasiFiniteAt _

set_option backward.isDefEq.respectTransparency false in
/--
lemma `ZariskisMainProperty.exists_fg_and_exists_notMem_and_awayMap_bijective` / 引理 `ZariskisMainProperty.exists_fg_and_exists_notMem_and_awayMap_bijective`

English:
lemma ZariskisMainProperty.exists_fg_and_exists_notMem_and_awayMap_bijective
  proof: by
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := S)
  choose r hrp hr m hm using zariskisMainProperty_iff.mp H
  let t := insert r { r ^ m x * x | x in s }
  let r' : Algebra.adjoin R t := ⟨r, Algebra.subset_adjoin (by simp [t])⟩
  refine ⟨Algebra.adjoin R t, fg_adjoin_of_finite ?_ ?_, ?_⟩
  · simp only [t, Set.finite_insert]
    exact s.finite_toSet.image (fun x => r ^ m x * x)
  · rintro a (rfl | ⟨x, hx, rfl⟩); exacts [hr, hm _]
  refine ⟨r', hrp,
    IsLocalization.map_injective_of_injective _ _ _ Subtype.val_injective, ?_⟩
  have : (IsScalarTower.toAlgHom R S _).range <=
      (Localization.awayMapₐ (Algebra.adjoin R t).val r').range := by
    rw [← Algebra.map_top]; rw [← hs]; rw [Subalgebra.map_le]; rw [Algebra.adjoin_le_iff]
    intro x hx
    suffices exists a in Algebra.adjoin R t, exists n, r ^ n in Algebra.adjoin R t ∧
        exists k, r ^ k * a = r ^ k * (x * r ^ n) by
      simpa [(IsLocalization.mk'_surjective (.powers r')).exists,
        (IsLocalization.mk'_surjective (.powers r)).forall, Localization.awayMapₐ,
        IsLocalization.Away.map, IsLocalization.map_mk', Submonoid.mem_powers_iff,
        Subtype.ext_iff, IsLocalization.mk'_eq_iff_eq_mul, ← map_mul, ← map_pow,
        IsLocalization.eq_iff_exists (.powers r), Subalgebra.val]
    exact ⟨_, Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨x, hx, mul_comm _ _⟩),
      m x, pow_mem r'.2 _, 1, rfl⟩
  intro x
  obtain ⟨x, ⟨_, n, rfl⟩, rfl⟩ := IsLocalization.exists_mk'_eq
    (.powers ((Algebra.adjoin R t).val.toRingHom r')) x
  obtain ⟨y, hy : Localization.awayMap _ _ _ = _⟩ := this ⟨x, rfl⟩
  refine ⟨y * Localization.Away.invSelf _ ^ n, ?_⟩
  simp only [map_mul, map_pow, hy]
  simp [Localization.Away.invSelf, Localization.awayMap, ← Algebra.smul_def,
    IsLocalization.Away.map, IsLocalization.map_mk', Localization.mk_eq_mk',
    ← IsLocalization.mk'_pow]

中文:
引理 ZariskisMainProperty.存在_fg_and_存在_notMem_and_awayMap_bijective
  证明: by
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := S)
  choose r hrp hr m hm using zariskisMainProperty_iff.mp H
  let t := insert r { r ^ m x * x | x in s }
  let r' : Algebra.adjoin R t := ⟨r, Algebra.subset_adjoin (by simp [t])⟩
  refine ⟨Algebra.adjoin R t, fg_adjoin_of_finite ?_ ?_, ?_⟩
  · simp only [t, Set.finite_insert]
    exact s.finite_toSet.image (fun x => r ^ m x * x)
  · rintro a (rfl | ⟨x, hx, rfl⟩); exacts [hr, hm _]
  refine ⟨r', hrp,
    IsLocalization.map_injective_of_injective _ _ _ Subtype.val_injective, ?_⟩
  have : (IsScalarTower.toAlgHom R S _).range <=
      (Localization.awayMapₐ (Algebra.adjoin R t).val r').range := by
    rw [← Algebra.map_top]; rw [← hs]; rw [Subalgebra.map_le]; rw [Algebra.adjoin_le_iff]
    intro x hx
    suffices exists a in Algebra.adjoin R t, exists n, r ^ n in Algebra.adjoin R t ∧
        exists k, r ^ k * a = r ^ k * (x * r ^ n) by
      simpa [(IsLocalization.mk'_surjective (.powers r')).exists,
        (IsLocalization.mk'_surjective (.powers r)).forall, Localization.awayMapₐ,
        IsLocalization.Away.map, IsLocalization.map_mk', Submonoid.mem_powers_iff,
        Subtype.ext_iff, IsLocalization.mk'_eq_iff_eq_mul, ← map_mul, ← map_pow,
        IsLocalization.eq_iff_exists (.powers r), Subalgebra.val]
    exact ⟨_, Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨x, hx, mul_comm _ _⟩),
      m x, pow_mem r'.2 _, 1, rfl⟩
  intro x
  obtain ⟨x, ⟨_, n, rfl⟩, rfl⟩ := IsLocalization.exists_mk'_eq
    (.powers ((Algebra.adjoin R t).val.toRingHom r')) x
  obtain ⟨y, hy : Localization.awayMap _ _ _ = _⟩ := this ⟨x, rfl⟩
  refine ⟨y * Localization.Away.invSelf _ ^ n, ?_⟩
  simp only [map_mul, map_pow, hy]
  simp [Localization.Away.invSelf, Localization.awayMap, ← Algebra.smul_def,
    IsLocalization.Away.map, IsLocalization.map_mk', Localization.mk_eq_mk',
    ← IsLocalization.mk'_pow]

Depends on / 依赖: Algebra, Algebra.FiniteType.out, Algebra.adjoin, Algebra.subset_adjoin, FiniteType, IsLocalization, IsLocalization.map_injective_of_injective, Set.finite_insert, Subtyp, adjoin, exacts, fg_adjoin_of_finite, finite_insert, finite_toSet, insert, map_injective_of_injective, s.finite_toSet.image, subset_adjoin, zariskisMainProperty_iff, zariskisMainProperty_iff.mp
-/
lemma ZariskisMainProperty.exists_fg_and_exists_notMem_and_awayMap_bijective
    [Algebra.FiniteType R S] (p : Ideal S) (H : ZariskisMainProperty R p) :
    exists S' : Subalgebra R S, S'.toSubmodule.FG ∧ exists r : S',
      r.1 ∉ p ∧ Function.Bijective (Localization.awayMap S'.val.toRingHom r) := by
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := S)
  choose r hrp hr m hm using zariskisMainProperty_iff.mp H
  let t := insert r { r ^ m x * x | x in s }
  let r' : Algebra.adjoin R t := ⟨r, Algebra.subset_adjoin (by simp [t])⟩
  refine ⟨Algebra.adjoin R t, fg_adjoin_of_finite ?_ ?_, ?_⟩
  · simp only [t, Set.finite_insert]
    exact s.finite_toSet.image (fun x => r ^ m x * x)
  · rintro a (rfl | ⟨x, hx, rfl⟩); exacts [hr, hm _]
  refine ⟨r', hrp,
    IsLocalization.map_injective_of_injective _ _ _ Subtype.val_injective, ?_⟩
  have : (IsScalarTower.toAlgHom R S _).range <=
      (Localization.awayMapₐ (Algebra.adjoin R t).val r').range := by
    rw [← Algebra.map_top]; rw [← hs]; rw [Subalgebra.map_le]; rw [Algebra.adjoin_le_iff]
    intro x hx
    suffices exists a in Algebra.adjoin R t, exists n, r ^ n in Algebra.adjoin R t ∧
        exists k, r ^ k * a = r ^ k * (x * r ^ n) by
      simpa [(IsLocalization.mk'_surjective (.powers r')).exists,
        (IsLocalization.mk'_surjective (.powers r)).forall, Localization.awayMapₐ,
        IsLocalization.Away.map, IsLocalization.map_mk', Submonoid.mem_powers_iff,
        Subtype.ext_iff, IsLocalization.mk'_eq_iff_eq_mul, ← map_mul, ← map_pow,
        IsLocalization.eq_iff_exists (.powers r), Subalgebra.val]
    exact ⟨_, Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨x, hx, mul_comm _ _⟩),
      m x, pow_mem r'.2 _, 1, rfl⟩
  intro x
  obtain ⟨x, ⟨_, n, rfl⟩, rfl⟩ := IsLocalization.exists_mk'_eq
    (.powers ((Algebra.adjoin R t).val.toRingHom r')) x
  obtain ⟨y, hy : Localization.awayMap _ _ _ = _⟩ := this ⟨x, rfl⟩
  refine ⟨y * Localization.Away.invSelf _ ^ n, ?_⟩
  simp only [map_mul, map_pow, hy]
  simp [Localization.Away.invSelf, Localization.awayMap, ← Algebra.smul_def,
    IsLocalization.Away.map, IsLocalization.map_mk', Localization.mk_eq_mk',
    ← IsLocalization.mk'_pow]

/--
lemma `QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective` / 引理 `QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective`

English:
lemma QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective
  proof: ZariskisMainProperty.exists_fg_and_exists_notMem_and_awayMap_bijective _
    (.of_finiteType_of_weaklyQuasiFiniteAt _)

中文:
引理 QuasiFiniteAt.存在_fg_and_存在_notMem_and_awayMap_bijective
  证明: ZariskisMainProperty.exists_fg_and_exists_notMem_and_awayMap_bijective _
    (.of_finiteType_of_weaklyQuasiFiniteAt _)

Depends on / 依赖: ZariskisMainProperty, ZariskisMainProperty.exists_fg_and_exists_notMem_and_awayMap_bijective, exists_fg_and_exists_notMem_and_awayMap_bijective, of_finiteType_of_weaklyQuasiFiniteAt
-/
lemma QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective
    [Algebra.FiniteType R S] (p : Ideal S) [p.IsPrime] [WeaklyQuasiFiniteAt R p] :
    exists S' : Subalgebra R S, S'.toSubmodule.FG ∧ exists r : S',
      r.1 ∉ p ∧ Function.Bijective (Localization.awayMap S'.val.toRingHom r) :=
  ZariskisMainProperty.exists_fg_and_exists_notMem_and_awayMap_bijective _
    (.of_finiteType_of_weaklyQuasiFiniteAt _)

/--
lemma `ZariskisMainProperty.quasiFiniteAt` / 引理 `ZariskisMainProperty.quasiFiniteAt`

English:
lemma ZariskisMainProperty.quasiFiniteAt
  proof: by
  obtain ⟨S', hS', r, hrp, H⟩ := H.exists_fg_and_exists_notMem_and_awayMap_bijective _
  have : Module.Finite R S' := ⟨(Submodule.fg_top _).mpr hS'⟩
  have : Algebra.QuasiFinite R (Localization.Away r) :=
    .trans _ S' _
  have : Algebra.QuasiFinite R (Localization.Away r.1) :=
    .of_surjective_algHom (Localization.awayMapₐ S'.val r) H.2
  let f : Localization.Away r.1 ->ₐ[S] Localization.AtPrime p :=
IsLocalization.Away.liftAlgHom r.1 (f := Algebra.ofId _ _)
      IsLocalization.map_units (M := p.primeCompl) (Localization.AtPrime p) ⟨r, hrp⟩
  refine .of_forall_exists_mul_mem_range (f.restrictScalars R) fun x => ?_
  obtain ⟨x, ⟨s, hs⟩, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl x
  exact ⟨algebraMap _ _ s, by simpa using IsLocalization.map_units _ ⟨s, hs⟩,
    algebraMap _ _ x, by simp⟩

中文:
引理 ZariskisMainProperty.quasiFiniteAt
  证明: by
  obtain ⟨S', hS', r, hrp, H⟩ := H.exists_fg_and_exists_notMem_and_awayMap_bijective _
  have : Module.Finite R S' := ⟨(Submodule.fg_top _).mpr hS'⟩
  have : Algebra.QuasiFinite R (Localization.Away r) :=
    .trans _ S' _
  have : Algebra.QuasiFinite R (Localization.Away r.1) :=
    .of_surjective_algHom (Localization.awayMapₐ S'.val r) H.2
  let f : Localization.Away r.1 ->ₐ[S] Localization.AtPrime p :=
IsLocalization.Away.liftAlgHom r.1 (f := Algebra.ofId _ _)
      IsLocalization.map_units (M := p.primeCompl) (Localization.AtPrime p) ⟨r, hrp⟩
  refine .of_forall_exists_mul_mem_range (f.restrictScalars R) fun x => ?_
  obtain ⟨x, ⟨s, hs⟩, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl x
  exact ⟨algebraMap _ _ s, by simpa using IsLocalization.map_units _ ⟨s, hs⟩,
    algebraMap _ _ x, by simp⟩

Depends on / 依赖: Algebra, Algebra.QuasiFinite, Algebra.ofId, AtPrime, Finite, H.exists_fg_and_exists_notMem_and_awayMap_bijective, IsLocalization, IsLocalization.Away.liftAlgHom, IsLocalization.map_units, Localization, Localization.AtPrime, Localization.Away, Localization.awayMap, Module, Module.Finite, QuasiFinite, Submodule, Submodule.fg_top, exists_fg_and_exists_notMem_and_awayMap_bijective, fg_top
-/
lemma ZariskisMainProperty.quasiFiniteAt
    [Algebra.FiniteType R S] (p : Ideal S) [p.IsPrime] (H : ZariskisMainProperty R p) :
    Algebra.QuasiFiniteAt R p := by
  obtain ⟨S', hS', r, hrp, H⟩ := H.exists_fg_and_exists_notMem_and_awayMap_bijective _
  have : Module.Finite R S' := ⟨(Submodule.fg_top _).mpr hS'⟩
  have : Algebra.QuasiFinite R (Localization.Away r) :=
    .trans _ S' _
  have : Algebra.QuasiFinite R (Localization.Away r.1) :=
    .of_surjective_algHom (Localization.awayMapₐ S'.val r) H.2
  let f : Localization.Away r.1 ->ₐ[S] Localization.AtPrime p :=
IsLocalization.Away.liftAlgHom r.1 (f := Algebra.ofId _ _)
      IsLocalization.map_units (M := p.primeCompl) (Localization.AtPrime p) ⟨r, hrp⟩
  refine .of_forall_exists_mul_mem_range (f.restrictScalars R) fun x => ?_
  obtain ⟨x, ⟨s, hs⟩, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl x
  exact ⟨algebraMap _ _ s, by simpa using IsLocalization.map_units _ ⟨s, hs⟩,
    algebraMap _ _ x, by simp⟩

/--
lemma `QuasiFiniteAt.of_weaklyQuasiFiniteAt` / 引理 `QuasiFiniteAt.of_weaklyQuasiFiniteAt`

English:
lemma QuasiFiniteAt.of_weaklyQuasiFiniteAt
  proof: ZariskisMainProperty.quasiFiniteAt _ (.of_finiteType_of_weaklyQuasiFiniteAt _)

中文:
引理 QuasiFiniteAt.of_weaklyQuasiFiniteAt
  证明: ZariskisMainProperty.quasiFiniteAt _ (.of_finiteType_of_weaklyQuasiFiniteAt _)

Depends on / 依赖: ZariskisMainProperty, ZariskisMainProperty.quasiFiniteAt, of_finiteType_of_weaklyQuasiFiniteAt, quasiFiniteAt
-/
lemma QuasiFiniteAt.of_weaklyQuasiFiniteAt
    [Algebra.FiniteType R S] (p : Ideal S) [p.IsPrime] [Algebra.WeaklyQuasiFiniteAt R p] :
    Algebra.QuasiFiniteAt R p :=
  ZariskisMainProperty.quasiFiniteAt _ (.of_finiteType_of_weaklyQuasiFiniteAt _)

/--
lemma `QuasiFiniteAt.of_quasiFiniteAt_residueField` / 引理 `QuasiFiniteAt.of_quasiFiniteAt_residueField`

English:
lemma QuasiFiniteAt.of_quasiFiniteAt_residueField
  proof: have : Algebra.WeaklyQuasiFiniteAt R q := .of_quasiFiniteAt_residueField p q Q hQ
  .of_weaklyQuasiFiniteAt _

中文:
引理 QuasiFiniteAt.of_quasiFiniteAt_residueField
  证明: have : Algebra.WeaklyQuasiFiniteAt R q := .of_quasiFiniteAt_residueField p q Q hQ
  .of_weaklyQuasiFiniteAt _

Depends on / 依赖: Algebra, Algebra.WeaklyQuasiFiniteAt, WeaklyQuasiFiniteAt, of_quasiFiniteAt_residueField, of_weaklyQuasiFiniteAt
-/
lemma QuasiFiniteAt.of_quasiFiniteAt_residueField
    [FiniteType R S] (p : Ideal R) (q : Ideal S) [q.IsPrime]
    [p.IsPrime] [q.LiesOver p]
    (Q : Ideal (p.Fiber S)) [Q.IsPrime]
    (hQ : Q.comap Algebra.TensorProduct.includeRight.toRingHom = q)
    [Algebra.QuasiFiniteAt p.ResidueField Q] :
    Algebra.QuasiFiniteAt R q :=
  have : Algebra.WeaklyQuasiFiniteAt R q := .of_quasiFiniteAt_residueField p q Q hQ
  .of_weaklyQuasiFiniteAt _

/--
lemma `QuasiFiniteAt.of_isOpen_singleton_fiber` / 引理 `QuasiFiniteAt.of_isOpen_singleton_fiber`

English:
lemma QuasiFiniteAt.of_isOpen_singleton_fiber
  proof: by
  let p := q.comap (algebraMap R S)
  let e := PrimeSpectrum.preimageHomeomorphFiber R S p
  suffices Algebra.QuasiFiniteAt p.asIdeal.ResidueField (e ⟨q, rfl⟩).asIdeal from
    .of_quasiFiniteAt_residueField _ q.asIdeal (e ⟨q, rfl⟩).asIdeal
      congr($(e.symm_apply_apply ⟨q, rfl⟩).1.asIdeal)
  refine .of_isOpen_singleton _ ?_
  rwa [← Set.image_singleton, e.isOpen_image]

中文:
引理 QuasiFiniteAt.of_isOpen_singleton_fiber
  证明: by
  let p := q.comap (algebraMap R S)
  let e := PrimeSpectrum.preimageHomeomorphFiber R S p
  suffices Algebra.QuasiFiniteAt p.asIdeal.ResidueField (e ⟨q, rfl⟩).asIdeal from
    .of_quasiFiniteAt_residueField _ q.asIdeal (e ⟨q, rfl⟩).asIdeal
      congr($(e.symm_apply_apply ⟨q, rfl⟩).1.asIdeal)
  refine .of_isOpen_singleton _ ?_
  rwa [← Set.image_singleton, e.isOpen_image]

Depends on / 依赖: algebraMap, q.comap
-/
lemma QuasiFiniteAt.of_isOpen_singleton_fiber
    [FiniteType R S] (q : PrimeSpectrum S)
    (H : IsOpen (X := .comap (algebraMap R S) ⁻¹' {q.comap (algebraMap R S)}) {⟨q, rfl⟩}) :
    Algebra.QuasiFiniteAt R q.asIdeal := by
  let p := q.comap (algebraMap R S)
  let e := PrimeSpectrum.preimageHomeomorphFiber R S p
  suffices Algebra.QuasiFiniteAt p.asIdeal.ResidueField (e ⟨q, rfl⟩).asIdeal from
    .of_quasiFiniteAt_residueField _ q.asIdeal (e ⟨q, rfl⟩).asIdeal
      congr($(e.symm_apply_apply ⟨q, rfl⟩).1.asIdeal)
  refine .of_isOpen_singleton _ ?_
  rwa [← Set.image_singleton, e.isOpen_image]

/--
lemma `quasiFiniteAt_iff_isOpen_singleton_fiber` / 引理 `quasiFiniteAt_iff_isOpen_singleton_fiber`

English:
lemma quasiFiniteAt_iff_isOpen_singleton_fiber
  proof: by
  refine ⟨fun H => ?_, .of_isOpen_singleton_fiber q⟩
  let p := q.comap (algebraMap R S)
  let e := PrimeSpectrum.preimageHomeomorphFiber R S p
  rw [← e.isOpen_image]; rw [Set.image_singleton]
  suffices Algebra.QuasiFiniteAt p.asIdeal.ResidueField (e ⟨q, rfl⟩).asIdeal from
    (QuasiFiniteAt.isClopen_singleton (R := p.asIdeal.ResidueField) _).isOpen
  exact .baseChange q.asIdeal _ congr($(e.symm_apply_apply ⟨q, rfl⟩).1.asIdeal).symm

中文:
引理 quasiFiniteAt_iff_isOpen_singleton_fiber
  证明: by
  refine ⟨fun H => ?_, .of_isOpen_singleton_fiber q⟩
  let p := q.comap (algebraMap R S)
  let e := PrimeSpectrum.preimageHomeomorphFiber R S p
  rw [← e.isOpen_image]; rw [Set.image_singleton]
  suffices Algebra.QuasiFiniteAt p.asIdeal.ResidueField (e ⟨q, rfl⟩).asIdeal from
    (QuasiFiniteAt.isClopen_singleton (R := p.asIdeal.ResidueField) _).isOpen
  exact .baseChange q.asIdeal _ congr($(e.symm_apply_apply ⟨q, rfl⟩).1.asIdeal).symm

Depends on / 依赖: Algebra, Algebra.QuasiFiniteAt, PrimeSpectrum, PrimeSpectrum.preimageHomeomorphFiber, QuasiFiniteAt, QuasiFiniteAt.isClopen_singleton, ResidueField, Set.image_singleton, algebraMap, asIdeal, baseChange, e.isOpen_image, e.symm_apply_apply, image_singleton, isClopen_singleton, isOpen, isOpen_image, of_isOpen_singleton_fiber, p.asIdeal.ResidueField, preimageHomeomorphFiber
-/
lemma quasiFiniteAt_iff_isOpen_singleton_fiber
    [FiniteType R S] (q : PrimeSpectrum S) :
    Algebra.QuasiFiniteAt R q.asIdeal ↔
      IsOpen (X := .comap (algebraMap R S) ⁻¹' {q.comap (algebraMap R S)}) {⟨q, rfl⟩} := by
  refine ⟨fun H => ?_, .of_isOpen_singleton_fiber q⟩
  let p := q.comap (algebraMap R S)
  let e := PrimeSpectrum.preimageHomeomorphFiber R S p
  rw [← e.isOpen_image]; rw [Set.image_singleton]
  suffices Algebra.QuasiFiniteAt p.asIdeal.ResidueField (e ⟨q, rfl⟩).asIdeal from
    (QuasiFiniteAt.isClopen_singleton (R := p.asIdeal.ResidueField) _).isOpen
  exact .baseChange q.asIdeal _ congr($(e.symm_apply_apply ⟨q, rfl⟩).1.asIdeal).symm

end Algebra
