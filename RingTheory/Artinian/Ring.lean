/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Junyan Xu, Jujian Zhang
-/
module

public import Mathlib.Algebra.Field.Equiv
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Artinian rings

A ring is said to be left (or right) Artinian if it is Artinian as a left (or right) module over
itself, or simply Artinian if it is both left and right Artinian.

## Main definitions

* `IsArtinianRing R` is the proposition that `R` is a left Artinian ring.

## Main results

* `IsArtinianRing.localization_surjective`: the canonical homomorphism from a commutative Artinian
  ring to any localization of itself is surjective.

* `IsArtinianRing.isNilpotent_jacobson_bot`: the Jacobson radical of a commutative Artinian ring
  is a nilpotent ideal.

## Implementation Details

The predicate `IsArtinianRing` is defined in `Mathlib/RingTheory/Artinian/Ring.lean` instead,
so that we can apply basic API on Artinian modules to division rings without a heavy import.

## References

* [M. F. Atiyah and I. G. Macdonald, *Introduction to commutative algebra*][atiyah-macdonald]
* [P. Samuel, *Algebraic Theory of Numbers*][samuel1967]

## Tags

Artinian, artinian, Artinian ring, artinian ring

-/

public section

open Set Submodule IsArtinian

namespace IsArtinianRing

@[stacks 00J8]
/--
theorem `isNilpotent_jacobson_bot` / 定理 `isNilpotent_jacobson_bot`

English:
theorem isNilpotent_jacobson_bot
  given: {R} [Ring R] [IsArtinianRing R]
  proof: Ideal.jacobson_bot (R := R) ▸ IsSemiprimaryRing.isNilpotent

中文:
定理 isNilpotent_jacobson_bot
  条件: {R} [Ring R] [IsArtinianRing R]
  证明: Ideal.jacobson_bot (R := R) ▸ IsSemiprimaryRing.isNilpotent

Depends on / 依赖: Ideal.jacobson_bot, IsSemiprimaryRing, IsSemiprimaryRing.isNilpotent, isNilpotent, jacobson_bot
-/
theorem isNilpotent_jacobson_bot {R} [Ring R] [IsArtinianRing R] :
    IsNilpotent (Ideal.jacobson (⊥ : Ideal R)) :=
  Ideal.jacobson_bot (R := R) ▸ IsSemiprimaryRing.isNilpotent

variable {R : Type*} [CommRing R] [IsArtinianRing R]

/--
lemma `jacobson_eq_radical` / 引理 `jacobson_eq_radical`

English:
lemma jacobson_eq_radical
  given: (I : Ideal R)
  statement: I.jacobson = I.radical
  proof: by
  simp_rw [Ideal.jacobson, Ideal.radical_eq_sInf, IsArtinianRing.isPrime_iff_isMaximal]

中文:
引理 jacobson_eq_radical
  条件: (I : Ideal R)
  结论: I.jacobson = I.radical
  证明: by
  simp_rw [Ideal.jacobson, Ideal.radical_eq_sInf, IsArtinianRing.isPrime_iff_isMaximal]

Depends on / 依赖: Ideal.jacobson, Ideal.radical_eq_sInf, IsArtinianRing, IsArtinianRing.isPrime_iff_isMaximal, isPrime_iff_isMaximal, jacobson, radical_eq_sInf, simp_rw
-/
lemma jacobson_eq_radical (I : Ideal R) : I.jacobson = I.radical := by
  simp_rw [Ideal.jacobson, Ideal.radical_eq_sInf, IsArtinianRing.isPrime_iff_isMaximal]

/--
theorem `isNilpotent_nilradical` / 定理 `isNilpotent_nilradical`

English:
theorem isNilpotent_nilradical
  statement: IsNilpotent (nilradical R)
  proof: by
  rw [nilradical]; rw [← jacobson_eq_radical]
  exact isNilpotent_jacobson_bot

中文:
定理 isNilpotent_nilradical
  结论: IsNilpotent (nilradical R)
  证明: by
  rw [nilradical]; rw [← jacobson_eq_radical]
  exact isNilpotent_jacobson_bot

Depends on / 依赖: isNilpotent_jacobson_bot, jacobson_eq_radical, nilradical
-/
theorem isNilpotent_nilradical : IsNilpotent (nilradical R) := by
  rw [nilradical]; rw [← jacobson_eq_radical]
  exact isNilpotent_jacobson_bot

variable (R) in
/--
theorem `isField_of_isReduced_of_isLocalRing` / 定理 `isField_of_isReduced_of_isLocalRing`

English:
theorem isField_of_isReduced_of_isLocalRing
  given: [IsReduced R] [IsLocalRing R]
  statement: IsField R
  proof: .toMulEquiv.isField (IsArtinianRing.equivPi R).toRingEquiv.trans (RingEquiv.piUnique _)
    (Ideal.Quotient.field _).toIsField

中文:
定理 isField_of_isReduced_of_isLocalRing
  条件: [IsReduced R] [IsLocalRing R]
  结论: IsField R
  证明: .toMulEquiv.isField (IsArtinianRing.equivPi R).toRingEquiv.trans (RingEquiv.piUnique _)
    (Ideal.Quotient.field _).toIsField

Depends on / 依赖: Ideal.Quotient.field, IsArtinianRing, IsArtinianRing.equivPi, Quotient, RingEquiv, RingEquiv.piUnique, equivPi, isField, piUnique, toIsField, toMulEquiv, toMulEquiv.isField, toRingEquiv, toRingEquiv.trans
-/
theorem isField_of_isReduced_of_isLocalRing [IsReduced R] [IsLocalRing R] : IsField R :=
.toMulEquiv.isField (IsArtinianRing.equivPi R).toRingEquiv.trans (RingEquiv.piUnique _)
    (Ideal.Quotient.field _).toIsField

section Localization

variable (S : Submonoid R) (L : Type*) [CommSemiring L] [Algebra R L] [IsLocalization S L]
include S

/--
theorem `localization_surjective` / 定理 `localization_surjective`

English:
theorem localization_surjective
  statement: Function.Surjective (algebraMap R L)
  proof: by
  intro r'
  obtain ⟨r₁, s, rfl⟩ := IsLocalization.exists_mk'_eq S r'
  rsuffices ⟨r₂, h⟩ : exists r : R, IsLocalization.mk' L 1 s = algebraMap R L r
  · exact ⟨r₁ * r₂, by rw [IsLocalization.mk'_eq_mul_mk'_one, map_mul, h]⟩
  obtain ⟨n, r, hr⟩ := IsArtinian.exists_pow_succ_smul_dvd (s : R) (1 : 

中文:
定理 localization_surjective
  结论: Function.Surjective (algebraMap R L)
  证明: by
  intro r'
  obtain ⟨r₁, s, rfl⟩ := IsLocalization.exists_mk'_eq S r'
  rsuffices ⟨r₂, h⟩ : exists r : R, IsLocalization.mk' L 1 s = algebraMap R L r
  · exact ⟨r₁ * r₂, by rw [IsLocalization.mk'_eq_mul_mk'_one, map_mul, h]⟩
  obtain ⟨n, r, hr⟩ := IsArtinian.exists_pow_succ_smul_dvd (s : R) (1 : 

Depends on / 依赖: IsArtinian, IsArtinian.exists_pow_succ_smul_dvd, IsLocalization, IsLocalization.exists_mk, IsLocalization.mk, _eq_iff_, _eq_mul_mk, _one, algebraMap, apply_fun, exists_mk, exists_pow_succ_smul_dvd, map_mul, mul_assoc, pow_succ, rsuffices, smul_eq_mul
-/
theorem localization_surjective : Function.Surjective (algebraMap R L) := by
  intro r'
  obtain ⟨r₁, s, rfl⟩ := IsLocalization.exists_mk'_eq S r'
  rsuffices ⟨r₂, h⟩ : exists r : R, IsLocalization.mk' L 1 s = algebraMap R L r
  · exact ⟨r₁ * r₂, by rw [IsLocalization.mk'_eq_mul_mk'_one, map_mul, h]⟩
  obtain ⟨n, r, hr⟩ := IsArtinian.exists_pow_succ_smul_dvd (s : R) (1 : R)
  use r
  rw [smul_eq_mul]; rw [smul_eq_mul]; rw [pow_succ]; rw [mul_assoc] at hr
  apply_fun algebraMap R L at hr
  simp only [map_mul] at hr
  rw [← IsLocalization.mk'_one (M := S) L]; rw [IsLocalization.mk'_eq_iff_eq]; rw [mul_one]; rw [Submonoid.coe_one]; rw [← (IsLocalization.map_units L (s ^ n)).mul_left_cancel hr]; rw [map_mul]

/--
theorem `localization_artinian` / 定理 `localization_artinian`

English:
theorem localization_artinian
  statement: IsArtinianRing L
  proof: (localization_surjective S L).isArtinianRing

中文:
定理 localization_artinian
  结论: IsArtinianRing L
  证明: (localization_surjective S L).isArtinianRing

Depends on / 依赖: isArtinianRing, localization_surjective
-/
theorem localization_artinian : IsArtinianRing L :=
  (localization_surjective S L).isArtinianRing

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsArtinianRing (Localization S)
  body: localization_artinian S _

中文:
实例 :
  签名: IsArtinianRing (Localization S)
  定义体: localization_artinian S _

Depends on / 依赖: localization_artinian
-/
instance : IsArtinianRing (Localization S) :=
  localization_artinian S _

end Localization

end IsArtinianRing
