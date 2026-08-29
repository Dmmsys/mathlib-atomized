/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
public import Mathlib.RingTheory.Unramified.Dedekind

/-!
# Every number field has a ramified prime over `ℚ`

...except `ℚ` itself.

This is a trivial corollary of `NumberField.not_dvd_discr_iff_forall_mem` and
`NumberField.abs_discr_gt_two` but is placed in a separate file to avoid large imports.

-/
@[expose] public section

open scoped NumberField nonZeroDivisors

variable {K 𝒪 : Type*} [Field K] [NumberField K] [CommRing 𝒪] [Algebra 𝒪 K]
variable [IsIntegralClosure 𝒪 Int K]

/--
lemma `NumberField.exists_not_isUnramifiedIn` / 引理 `NumberField.exists_not_isUnramifiedIn`

English:
lemma NumberField.exists_not_isUnramifiedIn
  given: (H : Module.finrank Rat K != 1)
  proof: by
  have : 0 < Module.finrank Rat K := Module.finrank_pos
  have : 2 < |discr K| := abs_discr_gt_two (by lia)
  obtain ⟨p, hp1, hp2⟩ := (discr K).exists_prime_and_dvd (by linarith)
  use p.natAbs, p.prime_iff_natAbs_prime.mp hp1
  simpa [← not_dvd_discr_iff_isUnramifiedIn K 𝒪 hp1]

中文:
引理 数域.存在_not_isUnramifiedIn
  条件: (H : 模.finrank 有理数 K != 1)
  证明: by
  have : 0 < Module.finrank Rat K := Module.finrank_pos
  have : 2 < |discr K| := abs_discr_gt_two (by lia)
  obtain ⟨p, hp1, hp2⟩ := (discr K).exists_prime_and_dvd (by linarith)
  use p.natAbs, p.prime_iff_natAbs_prime.mp hp1
  simpa [← not_dvd_discr_iff_isUnramifiedIn K 𝒪 hp1]

Depends on / 依赖: Module, Module.finrank, Module.finrank_pos, abs_discr_gt_two, exists_prime_and_dvd, finrank, finrank_pos, natAbs, not_dvd_discr_iff_isUnramifiedIn, p.natAbs, p.prime_iff_natAbs_prime.mp, prime_iff_natAbs_prime
-/
lemma NumberField.exists_not_isUnramifiedIn (H : Module.finrank Rat K != 1) :
    exists p : Nat, p.Prime ∧ ¬ Algebra.IsUnramifiedIn 𝒪 (Ideal.span {(p : Int)}) := by
  have : 0 < Module.finrank Rat K := Module.finrank_pos
  have : 2 < |discr K| := abs_discr_gt_two (by lia)
  obtain ⟨p, hp1, hp2⟩ := (discr K).exists_prime_and_dvd (by linarith)
  use p.natAbs, p.prime_iff_natAbs_prime.mp hp1
  simpa [← not_dvd_discr_iff_isUnramifiedIn K 𝒪 hp1]

/--
lemma `NumberField.exists_not_isUnramifiedAt_int` / 引理 `NumberField.exists_not_isUnramifiedAt_int`

English:
lemma NumberField.exists_not_isUnramifiedAt_int
  given: (H : Module.finrank Rat K != 1)
  proof: by
  obtain ⟨p, hp1, hp2⟩ := NumberField.exists_not_isUnramifiedIn (𝒪 := 𝒪) H
  have := (IsIntegralClosure.algebraMap_injective 𝒪 Int K).isDomain
  have := IsIntegralClosure.isDedekindDomain Int Rat K 𝒪
  have := IsIntegralClosure.isTorsionFree Int (A := 𝒪) K
  have := IsIntegralClosure.isIntegral_a

中文:
引理 数域.存在_not_isUnramifiedAt_int
  条件: (H : 模.finrank 有理数 K != 1)
  证明: by
  obtain ⟨p, hp1, hp2⟩ := NumberField.exists_not_isUnramifiedIn (𝒪 := 𝒪) H
  have := (IsIntegralClosure.algebraMap_injective 𝒪 Int K).isDomain
  have := IsIntegralClosure.isDedekindDomain Int Rat K 𝒪
  have := IsIntegralClosure.isTorsionFree Int (A := 𝒪) K
  have := IsIntegralClosure.isIntegral_a

Depends on / 依赖: Algebra, Algebra.isUnramifiedIn_iff_forall_of_isDedekindDomain, IsIntegralClosure, IsIntegralClosure.algebraMap_injective, IsIntegralClosure.isDedekindDomain, IsIntegralClosure.isIntegral_algebra, IsIntegralClosure.isTorsionFree, NumberField, NumberField.exists_not_isUnramifiedIn, algebraMap_injective, exists_not_isUnramifiedIn, isDedekindDomain, isDomain, isIntegral_algebra, isTorsionFree, isUnramifiedIn_iff_forall_of_isDedekindDomain
-/
lemma NumberField.exists_not_isUnramifiedAt_int (H : Module.finrank Rat K != 1) :
    exists (P : Ideal 𝒪) (_ : P.IsMaximal), ¬ Algebra.IsUnramifiedAt Int P := by
  obtain ⟨p, hp1, hp2⟩ := NumberField.exists_not_isUnramifiedIn (𝒪 := 𝒪) H
  have := (IsIntegralClosure.algebraMap_injective 𝒪 Int K).isDomain
  have := IsIntegralClosure.isDedekindDomain Int Rat K 𝒪
  have := IsIntegralClosure.isTorsionFree Int (A := 𝒪) K
  have := IsIntegralClosure.isIntegral_algebra Int (A := 𝒪) K
  grind [Algebra.isUnramifiedIn_iff_forall_of_isDedekindDomain]

/--
lemma `NumberField.finrank_eq_one_of_unramified` / 引理 `NumberField.finrank_eq_one_of_unramified`

English:
lemma NumberField.finrank_eq_one_of_unramified
  given: [Algebra.Unramified Int 𝒪]
  proof: by
  by_contra H
  obtain ⟨P, _, H⟩ := NumberField.exists_not_isUnramifiedAt_int (𝒪 := 𝒪) H
  exact H inferInstance

中文:
引理 数域.finrank_eq_one_of_unramified
  条件: [代数.非分歧 整数 𝒪]
  证明: by
  by_contra H
  obtain ⟨P, _, H⟩ := NumberField.exists_not_isUnramifiedAt_int (𝒪 := 𝒪) H
  exact H inferInstance

Depends on / 依赖: NumberField, NumberField.exists_not_isUnramifiedAt_int, exists_not_isUnramifiedAt_int
-/
lemma NumberField.finrank_eq_one_of_unramified [Algebra.Unramified Int 𝒪] :
    Module.finrank Rat K = 1 := by
  by_contra H
  obtain ⟨P, _, H⟩ := NumberField.exists_not_isUnramifiedAt_int (𝒪 := 𝒪) H
  exact H inferInstance

/--
lemma `bijective_algebraMap_int_of_finite_of_unramified` / 引理 `bijective_algebraMap_int_of_finite_of_unramified`

English:
lemma bijective_algebraMap_int_of_finite_of_unramified
  proof: by
  have := isDedekindDomain.of_formallyUnramified Int 𝒪
  let K := FractionRing 𝒪
  let : Algebra Int K := Ring.toIntAlgebra K
  have : CharZero 𝒪 := Algebra.charZero_of_charZero Int _
  have : NumberField K := { to_finiteDimensional := Module.Finite.of_isLocalization Int 𝒪 Int⁰ }
  have := Number

中文:
引理 bijective_algebraMap_int_of_finite_of_unramified
  证明: by
  have := isDedekindDomain.of_formallyUnramified Int 𝒪
  let K := FractionRing 𝒪
  let : Algebra Int K := Ring.toIntAlgebra K
  have : CharZero 𝒪 := Algebra.charZero_of_charZero Int _
  have : NumberField K := { to_finiteDimensional := Module.Finite.of_isLocalization Int 𝒪 Int⁰ }
  have := Number

Depends on / 依赖: Algebra, Algebra.charZero_of_charZero, Algebra.finrank_eq_one_iff_bijective_algebraMap.mp, CharZero, Finite, FractionRing, IsIntegralClosure, IsScalarTower, IsScalarTower.toAlgHom, Module, Module.Finite.of_isLocalization, NumberField, NumberField.finrank_eq_one_of_unramified, Ring.toIntAlgebra, charZero_of_charZero, finrank_eq_one_iff_bijective_algebraMap, finrank_eq_one_of_unramified, isDedekindDomain, isDedekindDomain.of_formallyUnramified, ofBijective
-/
lemma bijective_algebraMap_int_of_finite_of_unramified
    [Module.Finite Int 𝒪] [Algebra.Unramified Int 𝒪] [IsDomain 𝒪] [FaithfulSMul Int 𝒪] :
    Function.Bijective (algebraMap Int 𝒪) := by
  have := isDedekindDomain.of_formallyUnramified Int 𝒪
  let K := FractionRing 𝒪
  let : Algebra Int K := Ring.toIntAlgebra K
  have : CharZero 𝒪 := Algebra.charZero_of_charZero Int _
  have : NumberField K := { to_finiteDimensional := Module.Finite.of_isLocalization Int 𝒪 Int⁰ }
  have := NumberField.finrank_eq_one_of_unramified (K := K) (𝒪 := 𝒪)
  have : IsIntegralClosure Int Int K := .of_algEquiv _ (.ofBijective (IsScalarTower.toAlgHom _ _ _)
    (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp this)) (by simp)
  exact bijective_algebraMap_of_linearEquiv (IsIntegralClosure.equiv Int Int K 𝒪).toLinearEquiv

/--
lemma `NumberField.exists_not_isUnramifiedAt_int_of_isGalois` / 引理 `NumberField.exists_not_isUnramifiedAt_int_of_isGalois`

English:
lemma NumberField.exists_not_isUnramifiedAt_int_of_isGalois
  statement: [IsGalois Rat K]
  proof: by
  have := (IsIntegralClosure.algebraMap_injective 𝒪 Int K).isDomain
  have := IsIntegralClosure.isDedekindDomain Int Rat K 𝒪
  have := IsIntegralClosure.isFractionRing_of_finite_extension Int Rat K 𝒪
  have := IsIntegralClosure.finite Int Rat K 𝒪
  have := CharZero.of_module (R := 𝒪) K
  let : Mu

中文:
引理 数域.存在_not_isUnramifiedAt_int_of_isGalois
  结论: [是Galois 有理数 K]
  证明: by
  have := (IsIntegralClosure.algebraMap_injective 𝒪 Int K).isDomain
  have := IsIntegralClosure.isDedekindDomain Int Rat K 𝒪
  have := IsIntegralClosure.isFractionRing_of_finite_extension Int Rat K 𝒪
  have := IsIntegralClosure.finite Int Rat K 𝒪
  have := CharZero.of_module (R := 𝒪) K
  let : Mu

Depends on / 依赖: CharZero, CharZero.of_module, IsGaloisGroup, IsGaloisGroup.of_isFractionRing, IsIntegralClosure, IsIntegralClosure.MulSemiringAction, IsIntegralClosure.algebraMap_injective, IsIntegralClosure.finite, IsIntegralClosure.isDedekindDomain, IsIntegralClosure.isFractionRing_of_finite_extension, MulSemiringAction, NumberField, NumberField.exists_not_isUnramifiedAt_int, algebraMap_injective, exists_not_isUnramifiedAt_int, finite, isDedekindDomain, isDomain, isFractionRing_of_finite_extension, of_isFractionRing
-/
lemma NumberField.exists_not_isUnramifiedAt_int_of_isGalois [IsGalois Rat K]
    (H : 1 < Module.finrank Rat K) :
    exists p : Nat, p.Prime ∧ forall (P : Ideal 𝒪) (_ : P.IsPrime), ↑p in P -> ¬ Algebra.IsUnramifiedAt Int P := by
  have := (IsIntegralClosure.algebraMap_injective 𝒪 Int K).isDomain
  have := IsIntegralClosure.isDedekindDomain Int Rat K 𝒪
  have := IsIntegralClosure.isFractionRing_of_finite_extension Int Rat K 𝒪
  have := IsIntegralClosure.finite Int Rat K 𝒪
  have := CharZero.of_module (R := 𝒪) K
  let : MulSemiringAction Gal(K/Rat) 𝒪 := IsIntegralClosure.MulSemiringAction Int Rat K 𝒪
  have := IsGaloisGroup.of_isFractionRing Gal(K/Rat) Int 𝒪 Rat K
  obtain ⟨P, _, hP'⟩ := NumberField.exists_not_isUnramifiedAt_int (𝒪 := 𝒪) H.ne'
  obtain ⟨p, hp : _ = Ideal.span _⟩ := IsPrincipalIdealRing.principal (P.under Int)
  have hp0 : p != 0 := fun hp0 => Ideal.IsMaximal.ne_bot_of_isIntegral_int _
    (Ideal.eq_bot_of_comap_eq_bot (hp.trans (by aesop)))
  have : Prime p := by rw [← Ideal.span_singleton_prime hp0, ← hp]; infer_instance
  refine ⟨p.natAbs, Int.prime_iff_natAbs_prime.mp this, fun Q _ hQ => ?_⟩
  replace hQ : (p : 𝒪) in Q := Q.mem_of_dvd
    (map_dvd (algebraMap _ _) p.associated_natAbs.symm.dvd) (by simpa using hQ)
  have : .span {p} = Ideal.under Int Q :=
    ((Ideal.liesOver_span_iff Ideal.IsPrime.ne_top' this).mpr hQ).1
  rwa [← Ideal.ramificationIdx_eq_one_iff,
    ← Ideal.ramificationIdxIn_eq_ramificationIdx (Q.under Int) _ Gal(K/Rat), ← this, ← hp,
    Ideal.ramificationIdxIn_eq_ramificationIdx _ P Gal(K/Rat), Ideal.ramificationIdx_eq_one_iff]
