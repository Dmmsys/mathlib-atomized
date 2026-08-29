/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
module

public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.GroupTheory.MonoidLocalization.Cardinality
public import Mathlib.RingTheory.OreLocalization.Cardinality

/-!
# Cardinality of localizations

In this file, we establish the cardinality of localizations. In most cases, a localization has
cardinality equal to the base ring. If there are zero-divisors, however, this is no longer true -
for example, `ZMod 6` localized at `{2, 4}` is equal to `ZMod 3`, and if you have zero in your
submonoid, then your localization is trivial (see `IsLocalization.uniqueOfZeroMem`).

## Main statements

* `IsLocalization.cardinalMk_le`: A localization has cardinality no larger than the base ring.
* `IsLocalization.cardinalMk`: If you don't localize at zero-divisors, the localization of a ring
  has cardinality equal to its base ring.

-/

public section


open Cardinal nonZeroDivisors

universe u v

section CommSemiring

variable {R : Type u} [CommSemiring R] {L : Type v} [CommSemiring L] [Algebra R L]

namespace IsLocalization

/--
theorem `lift_cardinalMk_le` / 定理 `lift_cardinalMk_le`

English:
theorem lift_cardinalMk_le
  given: (S : Submonoid R) [IsLocalization S L]
  proof: by
  have := Localization.cardinalMk_le S
  rwa [← lift_le.{v}, lift_mk_eq'.2 ⟨(Localization.algEquiv S L).toEquiv⟩] at this

中文:
定理 lift_cardinalMk_le
  条件: (S : Submonoid R) [IsLocalization S L]
  证明: by
  have := Localization.cardinalMk_le S
  rwa [← lift_le.{v}, lift_mk_eq'.2 ⟨(Localization.algEquiv S L).toEquiv⟩] at this

Depends on / 依赖: Localization, Localization.algEquiv, Localization.cardinalMk_le, algEquiv, cardinalMk_le, lift_le, lift_mk_eq, toEquiv
-/
theorem lift_cardinalMk_le (S : Submonoid R) [IsLocalization S L] :
    Cardinal.lift.{u} #L <= Cardinal.lift.{v} #R := by
  have := Localization.cardinalMk_le S
  rwa [← lift_le.{v}, lift_mk_eq'.2 ⟨(Localization.algEquiv S L).toEquiv⟩] at this

/--
theorem `cardinalMk_le` / 定理 `cardinalMk_le`

English:
theorem cardinalMk_le
  statement: {L : Type u} [CommSemiring L] [Algebra R L]
  proof: by
  simpa using lift_cardinalMk_le (L := L) S

中文:
定理 cardinalMk_le
  结论: {L : 类型u} [CommSemiring L] [Algebra R L]
  证明: by
  simpa using lift_cardinalMk_le (L := L) S

Depends on / 依赖: Finite, Finite.to_properlyDiscontinuousSMul, lift_cardinalMk_le, to_properlyDiscontinuousSMul
-/
theorem cardinalMk_le {L : Type u} [CommSemiring L] [Algebra R L]
    (S : Submonoid R) [IsLocalization S L] : #L <= #R := by
  simpa using lift_cardinalMk_le (L := L) S

end IsLocalization

end CommSemiring

section CommRing

variable {R : Type u} [CommRing R] {L : Type v} [CommRing L] [Algebra R L]

namespace Localization

/--
theorem `cardinalMk` / 定理 `cardinalMk`

English:
theorem cardinalMk
  given: {S : Submonoid R} (hS : S <= R⁰)
  statement: #(Localization S) = #R
  proof: by
  apply OreLocalization.cardinalMk
  rwa [nonZeroDivisorsLeft_eq_nonZeroDivisors]

中文:
定理 cardinalMk
  条件: {S : Submonoid R} (hS : S <= R⁰)
  结论: #(Localization S) = #R
  证明: by
  apply OreLocalization.cardinalMk
  rwa [nonZeroDivisorsLeft_eq_nonZeroDivisors]

Depends on / 依赖: OreLocalization, OreLocalization.cardinalMk, cardinalMk, nonZeroDivisorsLeft_eq_nonZeroDivisors
-/
theorem cardinalMk {S : Submonoid R} (hS : S <= R⁰) : #(Localization S) = #R := by
  apply OreLocalization.cardinalMk
  rwa [nonZeroDivisorsLeft_eq_nonZeroDivisors]

end Localization

namespace IsLocalization

variable (L)

/--
theorem `lift_cardinalMk` / 定理 `lift_cardinalMk`

English:
theorem lift_cardinalMk
  given: (S : Submonoid R) [IsLocalization S L] (hS : S <= R⁰)
  proof: by
  have := Localization.cardinalMk hS
  rwa [← lift_inj.{u, v}, lift_mk_eq'.2 ⟨(Localization.algEquiv S L).toEquiv⟩] at this

中文:
定理 lift_cardinalMk
  条件: (S : Submonoid R) [IsLocalization S L] (hS : S <= R⁰)
  证明: by
  have := Localization.cardinalMk hS
  rwa [← lift_inj.{u, v}, lift_mk_eq'.2 ⟨(Localization.algEquiv S L).toEquiv⟩] at this

Depends on / 依赖: Localization, Localization.algEquiv, Localization.cardinalMk, algEquiv, cardinalMk, lift_inj, lift_mk_eq, toEquiv
-/
theorem lift_cardinalMk (S : Submonoid R) [IsLocalization S L] (hS : S <= R⁰) :
    Cardinal.lift.{u} #L = Cardinal.lift.{v} #R := by
  have := Localization.cardinalMk hS
  rwa [← lift_inj.{u, v}, lift_mk_eq'.2 ⟨(Localization.algEquiv S L).toEquiv⟩] at this

/--
theorem `cardinalMk` / 定理 `cardinalMk`

English:
theorem cardinalMk
  statement: (L : Type u) [CommRing L] [Algebra R L]
  proof: by
  simpa using lift_cardinalMk L S hS

中文:
定理 cardinalMk
  结论: (L : 类型u) [CommRing L] [Algebra R L]
  证明: by
  simpa using lift_cardinalMk L S hS

Depends on / 依赖: T2Space, lift_cardinalMk, t2Space_of_properlyDiscontinuousSMul_of_t2Space
-/
theorem cardinalMk (L : Type u) [CommRing L] [Algebra R L]
    (S : Submonoid R) [IsLocalization S L] (hS : S <= R⁰) : #L = #R := by
  simpa using lift_cardinalMk L S hS

end IsLocalization

@[simp]
/--
theorem `Cardinal.mk_fractionRing` / 定理 `Cardinal.mk_fractionRing`

English:
theorem Cardinal.mk_fractionRing
  given: (R : Type u) [CommRing R]
  statement: #(FractionRing R) = #R
  proof: IsLocalization.cardinalMk (FractionRing R) R⁰ le_rfl

alias FractionRing.cardinalMk := Cardinal.mk_fractionRing

中文:
定理 Cardinal.mk_fractionRing
  条件: (R : 类型u) [CommRing R]
  结论: #(FractionRing R) = #R
  证明: IsLocalization.cardinalMk (FractionRing R) R⁰ le_rfl

alias FractionRing.cardinalMk := Cardinal.mk_fractionRing

Depends on / 依赖: FractionRing, IsLocalization, IsLocalization.cardinalMk, cardinalMk, le_rfl
-/
theorem Cardinal.mk_fractionRing (R : Type u) [CommRing R] : #(FractionRing R) = #R :=
  IsLocalization.cardinalMk (FractionRing R) R⁰ le_rfl

alias FractionRing.cardinalMk := Cardinal.mk_fractionRing

namespace IsFractionRing

variable (R L)

/--
theorem `lift_cardinalMk` / 定理 `lift_cardinalMk`

English:
theorem lift_cardinalMk
  given: [IsFractionRing R L]
  statement: Cardinal.lift.{u} #L = Cardinal.lift.{v} #R
  proof: IsLocalization.lift_cardinalMk L _ le_rfl

中文:
定理 lift_cardinalMk
  条件: [IsFractionRing R L]
  结论: Cardinal.lift.{u} #L = Cardinal.lift.{v} #R
  证明: IsLocalization.lift_cardinalMk L _ le_rfl

Depends on / 依赖: IsLocalization, IsLocalization.lift_cardinalMk, le_rfl, lift_cardinalMk
-/
theorem lift_cardinalMk [IsFractionRing R L] : Cardinal.lift.{u} #L = Cardinal.lift.{v} #R :=
  IsLocalization.lift_cardinalMk L _ le_rfl

/--
theorem `cardinalMk` / 定理 `cardinalMk`

English:
theorem cardinalMk
  given: (L : Type u) [CommRing L] [Algebra R L] [IsFractionRing R L]
  statement: #L = #R
  proof: IsLocalization.cardinalMk L _ le_rfl

中文:
定理 cardinalMk
  条件: (L : 类型u) [CommRing L] [Algebra R L] [IsFractionRing R L]
  结论: #L = #R
  证明: IsLocalization.cardinalMk L _ le_rfl

Depends on / 依赖: IsLocalization, IsLocalization.cardinalMk, cardinalMk, le_rfl
-/
theorem cardinalMk (L : Type u) [CommRing L] [Algebra R L] [IsFractionRing R L] : #L = #R :=
  IsLocalization.cardinalMk L _ le_rfl

end IsFractionRing

end CommRing
