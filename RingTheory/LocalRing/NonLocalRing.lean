/-
Copyright (c) 2025 Michal Staromiejski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Staromiejski
-/
module

public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Spectrum.Maximal.Basic

/-!

# Non-local rings

This file gathers some results about non-local rings.

## Main results

- `not_isLocalRing_of_nontrivial_pi`: for an index type `ι` with at least two elements and
  an indexed family of (semi)rings `R : ι → Type*`, the indexed product (semi)ring
  `Π i, R i` is not local.
- `not_isLocalRing_of_prod_of_nontrivial`: the product of two nontrivial (semi)rings is not
  local.
- `not_isLocalRing_tfae`: the following conditions are equivalent for a commutative (semi)ring `R`:
    * `R` is not local,
    * the maximal spectrum of `R` is nontrivial,
    * `R` has two distinct maximal ideals.
- `exists_surjective_of_not_isLocalRing`: there exists a surjective ring homomorphism from
  a non-local commutative ring onto a product of two fields.

-/

public section

namespace IsLocalRing

/--
theorem `not_isLocalRing_def` / 定理 `not_isLocalRing_def`

English:
theorem not_isLocalRing_def
  statement: {R : Type*} [Semiring R] {a b : R} (ha : ¬IsUnit a) (hb : ¬IsUnit b)
  proof: fun _ => hb (isUnit_or_isUnit_of_add_one hab).resolve_left ha

中文:
定理 not_isLocalRing_def
  结论: {R : 类型} [半环 R] {a b : R} (ha : ¬是单位 a) (hb : ¬是单位 b)
  证明: fun _ => hb (isUnit_or_isUnit_of_add_one hab).resolve_left ha

Depends on / 依赖: isUnit_or_isUnit_of_add_one, resolve_left
-/
theorem not_isLocalRing_def {R : Type*} [Semiring R] {a b : R} (ha : ¬IsUnit a) (hb : ¬IsUnit b)
    (hab : a + b = 1) : ¬IsLocalRing R :=
fun _ => hb (isUnit_or_isUnit_of_add_one hab).resolve_left ha

/--
theorem `not_isLocalRing_of_nontrivial_pi` / 定理 `not_isLocalRing_of_nontrivial_pi`

English:
theorem not_isLocalRing_of_nontrivial_pi
  statement: {ι : Type*} [Nontrivial ι] (R : ι -> Type*)
  proof: by
  classical
  let ⟨i₁, i₂, hi⟩ := exists_pair_ne ι
  have ha : ¬IsUnit (fun i => if i = i₁ then 0 else 1 : Π i, R i) :=
    fun h => not_isUnit_zero (M₀ := R i₁) (by simpa using h.map (Pi.evalRingHom R i₁))
  have hb : ¬IsUnit (fun i => if i = i₁ then 1 else 0 : Π i, R i) :=
    fun h => not_isUnit_zero (M₀ := R i₂) (by simpa [hi.symm] using h.map (Pi.evalRingHom R i₂))
  exact not_isLocalRing_def ha hb (by ext; dsimp; split <;> simp)

中文:
定理 not_isLocalRing_of_nontrivial_pi
  结论: {ι : 类型} [非平凡 ι] (R : ι -> 类型)
  证明: by
  classical
  let ⟨i₁, i₂, hi⟩ := exists_pair_ne ι
  have ha : ¬IsUnit (fun i => if i = i₁ then 0 else 1 : Π i, R i) :=
    fun h => not_isUnit_zero (M₀ := R i₁) (by simpa using h.map (Pi.evalRingHom R i₁))
  have hb : ¬IsUnit (fun i => if i = i₁ then 1 else 0 : Π i, R i) :=
    fun h => not_isUnit_zero (M₀ := R i₂) (by simpa [hi.symm] using h.map (Pi.evalRingHom R i₂))
  exact not_isLocalRing_def ha hb (by ext; dsimp; split <;> simp)

Depends on / 依赖: IsUnit, Pi.evalRingHom, classical, evalRingHom, exists_pair_ne, h.map, hi.symm, not_isLocalRing_def, not_isUnit_zero
-/
theorem not_isLocalRing_of_nontrivial_pi {ι : Type*} [Nontrivial ι] (R : ι -> Type*)
    [forall i, Semiring (R i)] [forall i, Nontrivial (R i)] : ¬IsLocalRing (Π i, R i) := by
  classical
  let ⟨i₁, i₂, hi⟩ := exists_pair_ne ι
  have ha : ¬IsUnit (fun i => if i = i₁ then 0 else 1 : Π i, R i) :=
    fun h => not_isUnit_zero (M₀ := R i₁) (by simpa using h.map (Pi.evalRingHom R i₁))
  have hb : ¬IsUnit (fun i => if i = i₁ then 1 else 0 : Π i, R i) :=
    fun h => not_isUnit_zero (M₀ := R i₂) (by simpa [hi.symm] using h.map (Pi.evalRingHom R i₂))
  exact not_isLocalRing_def ha hb (by ext; dsimp; split <;> simp)

/--
theorem `not_isLocalRing_of_prod_of_nontrivial` / 定理 `not_isLocalRing_of_prod_of_nontrivial`

English:
theorem not_isLocalRing_of_prod_of_nontrivial
  statement: (R₁ R₂ : Type*) [Semiring R₁] [Semiring R₂]
  proof: have ha : ¬IsUnit ((1, 0) : R₁ × R₂) :=
    fun h => not_isUnit_zero (M₀ := R₁) (by simpa using h.map (RingHom.snd R₁ R₂))
  have hb : ¬IsUnit ((0, 1) : R₁ × R₂) :=
    fun h => not_isUnit_zero (M₀ := R₂) (by simpa using h.map (RingHom.fst R₁ R₂))
  not_isLocalRing_def ha hb (by simp)

中文:
定理 not_isLocalRing_of_prod_of_nontrivial
  结论: (R₁ R₂ : 类型) [半环 R₁] [半环 R₂]
  证明: have ha : ¬IsUnit ((1, 0) : R₁ × R₂) :=
    fun h => not_isUnit_zero (M₀ := R₁) (by simpa using h.map (RingHom.snd R₁ R₂))
  have hb : ¬IsUnit ((0, 1) : R₁ × R₂) :=
    fun h => not_isUnit_zero (M₀ := R₂) (by simpa using h.map (RingHom.fst R₁ R₂))
  not_isLocalRing_def ha hb (by simp)

Depends on / 依赖: IsUnit, RingHom, RingHom.fst, RingHom.snd, h.map, not_isLocalRing_def, not_isUnit_zero
-/
theorem not_isLocalRing_of_prod_of_nontrivial (R₁ R₂ : Type*) [Semiring R₁] [Semiring R₂]
    [Nontrivial R₁] [Nontrivial R₂] : ¬IsLocalRing (R₁ × R₂) :=
  have ha : ¬IsUnit ((1, 0) : R₁ × R₂) :=
    fun h => not_isUnit_zero (M₀ := R₁) (by simpa using h.map (RingHom.snd R₁ R₂))
  have hb : ¬IsUnit ((0, 1) : R₁ × R₂) :=
    fun h => not_isUnit_zero (M₀ := R₂) (by simpa using h.map (RingHom.fst R₁ R₂))
  not_isLocalRing_def ha hb (by simp)

/--
theorem `not_isLocalRing_tfae` / 定理 `not_isLocalRing_tfae`

English:
theorem not_isLocalRing_tfae
  given: {R : Type*} [CommSemiring R] [Nontrivial R]
  proof: by
  tfae_have 1 -> 2
  | h => not_subsingleton_iff_nontrivial.mp fun _ => h of_singleton_maximalSpectrum
  tfae_have 2 -> 3
  | ⟨⟨m₁, hm₁⟩, ⟨m₂, hm₂⟩, h⟩ => ⟨m₁, m₂, ⟨hm₁, hm₂, fun _ => h (by congr)⟩⟩
  tfae_have 3 -> 1
| ⟨m₁, m₂, ⟨hm₁, hm₂, h⟩⟩ => fun _ => h (eq_maximalIdeal hm₁).trans (eq_maximalIdeal hm₂).symm
  tfae_finish

中文:
定理 not_isLocalRing_tfae
  条件: {R : 类型} [交换半环 R] [非平凡 R]
  证明: by
  tfae_have 1 -> 2
  | h => not_subsingleton_iff_nontrivial.mp fun _ => h of_singleton_maximalSpectrum
  tfae_have 2 -> 3
  | ⟨⟨m₁, hm₁⟩, ⟨m₂, hm₂⟩, h⟩ => ⟨m₁, m₂, ⟨hm₁, hm₂, fun _ => h (by congr)⟩⟩
  tfae_have 3 -> 1
| ⟨m₁, m₂, ⟨hm₁, hm₂, h⟩⟩ => fun _ => h (eq_maximalIdeal hm₁).trans (eq_maximalIdeal hm₂).symm
  tfae_finish

Depends on / 依赖: eq_maximalIdeal, not_subsingleton_iff_nontrivial, not_subsingleton_iff_nontrivial.mp, of_singleton_maximalSpectrum, tfae_finish, tfae_have
-/
theorem not_isLocalRing_tfae {R : Type*} [CommSemiring R] [Nontrivial R] :
    List.TFAE [
      ¬IsLocalRing R,
      Nontrivial (MaximalSpectrum R),
      exists m₁ m₂ : Ideal R, m₁.IsMaximal ∧ m₂.IsMaximal ∧ m₁ != m₂] := by
  tfae_have 1 -> 2
  | h => not_subsingleton_iff_nontrivial.mp fun _ => h of_singleton_maximalSpectrum
  tfae_have 2 -> 3
  | ⟨⟨m₁, hm₁⟩, ⟨m₂, hm₂⟩, h⟩ => ⟨m₁, m₂, ⟨hm₁, hm₂, fun _ => h (by congr)⟩⟩
  tfae_have 3 -> 1
| ⟨m₁, m₂, ⟨hm₁, hm₂, h⟩⟩ => fun _ => h (eq_maximalIdeal hm₁).trans (eq_maximalIdeal hm₂).symm
  tfae_finish

/--
theorem `exists_surjective_of_not_isLocalRing.` / 定理 `exists_surjective_of_not_isLocalRing.`

English:
theorem exists_surjective_of_not_isLocalRing.{u}
  statement: {R : Type u} [CommRing R] [Nontrivial R]
  proof: by
  /- get two different maximal ideals and project on the product of quotients -/
  obtain ⟨m₁, m₂, _, _, hm₁m₂⟩ := (not_isLocalRing_tfae.out 0 2).mp h
let e := Ideal.quotientInfEquivQuotientProd m₁ m₂ Ideal.isCoprime_of_isMaximal hm₁m₂
let f := e.toRingHom.comp Ideal.Quotient.mk (m₁ ⊓ m₂)
  use R ⧸ m₁, R ⧸ m₂, Ideal.Quotient.field m₁, Ideal.Quotient.field m₂, f
  apply Function.Surjective.comp e.surjective Ideal.Quotient.mk_surjective

中文:
定理 存在_surjective_of_not_isLocalRing.{u}
  结论: {R : 类型u} [交换环 R] [非平凡 R]
  证明: by
  /- get two different maximal ideals and project on the product of quotients -/
  obtain ⟨m₁, m₂, _, _, hm₁m₂⟩ := (not_isLocalRing_tfae.out 0 2).mp h
let e := Ideal.quotientInfEquivQuotientProd m₁ m₂ Ideal.isCoprime_of_isMaximal hm₁m₂
let f := e.toRingHom.comp Ideal.Quotient.mk (m₁ ⊓ m₂)
  use R ⧸ m₁, R ⧸ m₂, Ideal.Quotient.field m₁, Ideal.Quotient.field m₂, f
  apply Function.Surjective.comp e.surjective Ideal.Quotient.mk_surjective
-/
theorem exists_surjective_of_not_isLocalRing.{u} {R : Type u} [CommRing R] [Nontrivial R]
    (h : ¬IsLocalRing R) :
    exists (K₁ K₂ : Type u) (_ : Field K₁) (_ : Field K₂) (f : R ->+* K₁ × K₂),
      Function.Surjective f := by
  /- get two different maximal ideals and project on the product of quotients -/
  obtain ⟨m₁, m₂, _, _, hm₁m₂⟩ := (not_isLocalRing_tfae.out 0 2).mp h
let e := Ideal.quotientInfEquivQuotientProd m₁ m₂ Ideal.isCoprime_of_isMaximal hm₁m₂
let f := e.toRingHom.comp Ideal.Quotient.mk (m₁ ⊓ m₂)
  use R ⧸ m₁, R ⧸ m₂, Ideal.Quotient.field m₁, Ideal.Quotient.field m₂, f
  apply Function.Surjective.comp e.surjective Ideal.Quotient.mk_surjective

end IsLocalRing
