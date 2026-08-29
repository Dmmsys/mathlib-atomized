/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.Away.Lemmas

/-!
# Target local closure of ring homomorphism properties

If `P` is a property of ring homomorphisms, we call `Locally P` the closure of `P` with
respect to standard open coverings on the (algebraic) target (i.e. geometric source). Hence
for `f : R →+* S`, the property `Locally P` holds if it holds locally on `S`, i.e. if there exists
a subset `{ t }` of `S` generating the unit ideal, such that `P` holds for all compositions
`R →+* Sₜ`.

Assuming without further mention that `P` is stable under composition with isomorphisms,
`Locally P` is local on the target by construction, i.e. it satisfies
`RingHom.OfLocalizationSpanTarget`. If `P` itself is local on the target,
`Locally P` coincides with `P`.

The `Locally` construction preserves various properties of `P`, e.g. if `P` is stable under
composition, base change, etc., so is `Locally P`.

## Main results

- `RingHom.locally_ofLocalizationSpanTarget`: `Locally P` is local on the target.
- `RingHom.locally_holdsForLocalizationAway`: `Locally P` holds for localization away maps
  if `P` does.
- `RingHom.locally_isStableUnderBaseChange`: `Locally P` is stable under base change if `P` is.
- `RingHom.locally_stableUnderComposition`: `Locally P` is stable under composition
  if `P` is and `P` is preserved under localizations.
- `RingHom.locally_stableUnderCompositionWithLocalizationAwayTarget` and
  `RingHom.locally_stableUnderCompositionWithLocalizationAwaySource`: `Locally P` is stable under
  composition with localization away maps if `P` is.
- `RingHom.locally_localizationPreserves`: If `P` is preserved by localizations, then so is
  `Locally P`.

-/

@[expose] public section

universe u v

open TensorProduct

namespace RingHom

variable (P : forall {R S : Type u} [CommRing R] [CommRing S] (_ : R ->+* S), Prop)

/--
Definition of `Locally` / `Locally` 的定义

English:
definition Locally
  signature: {R S : Type u} [CommRing R] [CommRing S] (f : R ->+* S)
  body: exists (s : Set S) (_ : Ideal.span s = ⊤),
    forall t in s, P ((algebraMap S (Localization.Away t)).comp f)

中文:
定义 Locally
  签名: {R S : 类型u} [CommRing R] [CommRing S] (f : R ->+* S)
  定义体: exists (s : Set S) (_ : Ideal.span s = ⊤),
    forall t in s, P ((algebraMap S (Localization.Away t)).comp f)

Depends on / 依赖: Ideal.span, Localization, Localization.Away, algebraMap
-/
def Locally {R S : Type u} [CommRing R] [CommRing S] (f : R ->+* S) : Prop :=
  exists (s : Set S) (_ : Ideal.span s = ⊤),
    forall t in s, P ((algebraMap S (Localization.Away t)).comp f)

variable {R S : Type u} [CommRing R] [CommRing S]

/--
lemma `locally_iff_span_eq_top` / 引理 `locally_iff_span_eq_top`

English:
lemma locally_iff_span_eq_top
  given: {f : R ->+* S}
  proof: by
  refine ⟨fun ⟨s, hs, h⟩ => ?_, fun h => ⟨_, h, fun g hg => hg⟩⟩
  rw [eq_top_iff]; rw [← hs]; rw [Ideal.span_le]
  intro g hg
  exact Ideal.subset_span (h _ hg)

alias ⟨Locally.span_eq_top, _⟩ := locally_iff_span_eq_top

中文:
引理 locally_iff_span_eq_top
  条件: {f : R ->+* S}
  证明: by
  refine ⟨fun ⟨s, hs, h⟩ => ?_, fun h => ⟨_, h, fun g hg => hg⟩⟩
  rw [eq_top_iff]; rw [← hs]; rw [Ideal.span_le]
  intro g hg
  exact Ideal.subset_span (h _ hg)

alias ⟨Locally.span_eq_top, _⟩ := locally_iff_span_eq_top

Depends on / 依赖: Ideal.span_le, Ideal.subset_span, eq_top_iff, span_le, subset_span
-/
lemma locally_iff_span_eq_top {f : R ->+* S} :
    Locally P f ↔ Ideal.span {g : S | P ((algebraMap S (Localization.Away g)).comp f)} = ⊤ := by
  refine ⟨fun ⟨s, hs, h⟩ => ?_, fun h => ⟨_, h, fun g hg => hg⟩⟩
  rw [eq_top_iff]; rw [← hs]; rw [Ideal.span_le]
  intro g hg
  exact Ideal.subset_span (h _ hg)

alias ⟨Locally.span_eq_top, _⟩ := locally_iff_span_eq_top

/--
lemma `locally_iff_finite` / 引理 `locally_iff_finite`

English:
lemma locally_iff_finite
  given: (f : R ->+* S)
  proof: by
  constructor
  · intro ⟨s, hsone, hs⟩
    obtain ⟨s', h₁, h₂⟩ := (Ideal.span_eq_top_iff_finite s).mp hsone
    exact ⟨s', h₂, fun t ht => hs t (h₁ ht)⟩
  · intro ⟨s, hsone, hs⟩
    use s, hsone, hs

中文:
引理 locally_iff_finite
  条件: (f : R ->+* S)
  证明: by
  constructor
  · intro ⟨s, hsone, hs⟩
    obtain ⟨s', h₁, h₂⟩ := (Ideal.span_eq_top_iff_finite s).mp hsone
    exact ⟨s', h₂, fun t ht => hs t (h₁ ht)⟩
  · intro ⟨s, hsone, hs⟩
    use s, hsone, hs

Depends on / 依赖: Ideal.span_eq_top_iff_finite, span_eq_top_iff_finite
-/
lemma locally_iff_finite (f : R ->+* S) :
    Locally P f ↔ exists (s : Finset S) (_ : Ideal.span (s : Set S) = ⊤),
      forall t in s, P ((algebraMap S (Localization.Away t)).comp f) := by
  constructor
  · intro ⟨s, hsone, hs⟩
    obtain ⟨s', h₁, h₂⟩ := (Ideal.span_eq_top_iff_finite s).mp hsone
    exact ⟨s', h₂, fun t ht => hs t (h₁ ht)⟩
  · intro ⟨s, hsone, hs⟩
    use s, hsone, hs

variable {P}

/--
lemma `locally_of_exists` / 引理 `locally_of_exists`

English:
lemma locally_of_exists
  statement: (hP : RespectsIso P) (f : R ->+* S) {ι : Type*} (s : ι -> S)
  proof: by
  use Set.range s, hsone
  rintro - ⟨i, rfl⟩
  let e : Localization.Away (s i) ≃+* Sₜ i :=
    (IsLocalization.algEquiv (Submonoid.powers (s i)) _ _).toRingEquiv
  have : algebraMap S (Localization.Away (s i)) = e.symm.toRingHom.comp (algebraMap S (Sₜ i)) :=
    RingHom.ext (fun x => (AlgEquiv.co

中文:
引理 locally_of_exists
  结论: (hP : RespectsIso P) (f : R ->+* S) {ι : 类型} (s : ι -> S)
  证明: by
  use Set.range s, hsone
  rintro - ⟨i, rfl⟩
  let e : Localization.Away (s i) ≃+* Sₜ i :=
    (IsLocalization.algEquiv (Submonoid.powers (s i)) _ _).toRingEquiv
  have : algebraMap S (Localization.Away (s i)) = e.symm.toRingHom.comp (algebraMap S (Sₜ i)) :=
    RingHom.ext (fun x => (AlgEquiv.co

Depends on / 依赖: AlgEquiv, AlgEquiv.commutes, IsLocalization, IsLocalization.algEquiv, Localization, Localization.Away, RingHom, RingHom.comp_assoc, RingHom.ext, Set.range, Submonoid, Submonoid.powers, algEquiv, algebraMap, commutes, comp_assoc, e.symm.toRingHom.comp, hP.left, powers, toRingEquiv
-/
lemma locally_of_exists (hP : RespectsIso P) (f : R ->+* S) {ι : Type*} (s : ι -> S)
    (hsone : Ideal.span (Set.range s) = ⊤)
    (Sₜ : ι -> Type u) [forall i, CommRing (Sₜ i)] [forall i, Algebra S (Sₜ i)]
    [forall i, IsLocalization.Away (s i) (Sₜ i)] (hf : forall i, P ((algebraMap S (Sₜ i)).comp f)) :
    Locally P f := by
  use Set.range s, hsone
  rintro - ⟨i, rfl⟩
  let e : Localization.Away (s i) ≃+* Sₜ i :=
    (IsLocalization.algEquiv (Submonoid.powers (s i)) _ _).toRingEquiv
  have : algebraMap S (Localization.Away (s i)) = e.symm.toRingHom.comp (algebraMap S (Sₜ i)) :=
    RingHom.ext (fun x => (AlgEquiv.commutes (IsLocalization.algEquiv _ _ _).symm _).symm)
  rw [this]; rw [RingHom.comp_assoc]
  exact hP.left _ _ (hf i)

/--
lemma `locally_iff_exists` / 引理 `locally_iff_exists`

English:
lemma locally_iff_exists
  given: (hP : RespectsIso P) (f : R ->+* S)
  proof: ⟨fun ⟨s, hsone, hs⟩ => ⟨s, fun t : s => (t : S), by simpa, fun t => Localization.Away (t : S),
      inferInstance, inferInstance, inferInstance, fun t => hs t.val t.property⟩,
    fun ⟨ι, s, hsone, Sₜ, _, _, hislocal, hs⟩ => locally_of_exists hP f s hsone Sₜ hs⟩

中文:
引理 locally_iff_exists
  条件: (hP : RespectsIso P) (f : R ->+* S)
  证明: ⟨fun ⟨s, hsone, hs⟩ => ⟨s, fun t : s => (t : S), by simpa, fun t => Localization.Away (t : S),
      inferInstance, inferInstance, inferInstance, fun t => hs t.val t.property⟩,
    fun ⟨ι, s, hsone, Sₜ, _, _, hislocal, hs⟩ => locally_of_exists hP f s hsone Sₜ hs⟩

Depends on / 依赖: Localization, Localization.Away, hislocal, locally_of_exists, property, t.property, t.val
-/
lemma locally_iff_exists (hP : RespectsIso P) (f : R ->+* S) :
    Locally P f ↔ exists (ι : Type u) (s : ι -> S) (_ : Ideal.span (Set.range s) = ⊤) (Sₜ : ι -> Type u)
      (_ : (i : ι) -> CommRing (Sₜ i)) (_ : (i : ι) -> Algebra S (Sₜ i))
      (_ : (i : ι) -> IsLocalization.Away (s i : S) (Sₜ i)),
      forall i, P ((algebraMap S (Sₜ i)).comp f) :=
  ⟨fun ⟨s, hsone, hs⟩ => ⟨s, fun t : s => (t : S), by simpa, fun t => Localization.Away (t : S),
      inferInstance, inferInstance, inferInstance, fun t => hs t.val t.property⟩,
    fun ⟨ι, s, hsone, Sₜ, _, _, hislocal, hs⟩ => locally_of_exists hP f s hsone Sₜ hs⟩

/--
lemma `locally_iff_isLocalization` / 引理 `locally_iff_isLocalization`

English:
lemma locally_iff_isLocalization
  given: (hP : RespectsIso P) (f : R ->+* S)
  proof: by
  rw [locally_iff_finite P f]
  refine ⟨fun ⟨s, hsone, hs⟩ => ⟨s, hsone, fun t ht Sₜ _ _ _ => ?_⟩, fun ⟨s, hsone, hs⟩ => ?_⟩
  · let e : Localization.Away t ≃+* Sₜ :=
      (IsLocalization.algEquiv (Submonoid.powers t) _ _).toRingEquiv
    have : algebraMap S Sₜ = e.toRingHom.comp (algebraMap S (

中文:
引理 locally_iff_isLocalization
  条件: (hP : RespectsIso P) (f : R ->+* S)
  证明: by
  rw [locally_iff_finite P f]
  refine ⟨fun ⟨s, hsone, hs⟩ => ⟨s, hsone, fun t ht Sₜ _ _ _ => ?_⟩, fun ⟨s, hsone, hs⟩ => ?_⟩
  · let e : Localization.Away t ≃+* Sₜ :=
      (IsLocalization.algEquiv (Submonoid.powers t) _ _).toRingEquiv
    have : algebraMap S Sₜ = e.toRingHom.comp (algebraMap S (

Depends on / 依赖: AlgEquiv, AlgEquiv.commutes, IsLocalization, IsLocalization.algEquiv, Localization, Localization.Away, RingHom, RingHom.comp_assoc, RingHom.ext, Submonoid, Submonoid.powers, algEquiv, algebraMap, commutes, comp_assoc, e.toRingHom.comp, hP.left, locally_iff_finite, powers, toRingEquiv
-/
lemma locally_iff_isLocalization (hP : RespectsIso P) (f : R ->+* S) :
    Locally P f ↔ exists (s : Finset S) (_ : Ideal.span (s : Set S) = ⊤),
      forall t in s, forall (Sₜ : Type u) [CommRing Sₜ] [Algebra S Sₜ] [IsLocalization.Away t Sₜ],
      P ((algebraMap S Sₜ).comp f) := by
  rw [locally_iff_finite P f]
  refine ⟨fun ⟨s, hsone, hs⟩ => ⟨s, hsone, fun t ht Sₜ _ _ _ => ?_⟩, fun ⟨s, hsone, hs⟩ => ?_⟩
  · let e : Localization.Away t ≃+* Sₜ :=
      (IsLocalization.algEquiv (Submonoid.powers t) _ _).toRingEquiv
    have : algebraMap S Sₜ = e.toRingHom.comp (algebraMap S (Localization.Away t)) :=
      RingHom.ext (fun x => (AlgEquiv.commutes (IsLocalization.algEquiv _ _ _) _).symm)
    rw [this]; rw [RingHom.comp_assoc]
    exact hP.left _ _ (hs t ht)
  · exact ⟨s, hsone, fun t ht => hs t ht _⟩

/--
lemma `locally_of` / 引理 `locally_of`

English:
lemma locally_of
  given: (hP : RespectsIso P) (f : R ->+* S) (hf : P f)
  statement: Locally P f
  proof: by
  use {1}
  let e : S ≃+* Localization.Away (1 : S) :=
    (IsLocalization.atUnits S (Submonoid.powers 1) (by simp)).toRingEquiv
  simp only [Set.mem_singleton_iff, forall_eq, Ideal.span_singleton_one, exists_const]
  exact hP.left f e hf

中文:
引理 locally_of
  条件: (hP : RespectsIso P) (f : R ->+* S) (hf : P f)
  结论: Locally P f
  证明: by
  use {1}
  let e : S ≃+* Localization.Away (1 : S) :=
    (IsLocalization.atUnits S (Submonoid.powers 1) (by simp)).toRingEquiv
  simp only [Set.mem_singleton_iff, forall_eq, Ideal.span_singleton_one, exists_const]
  exact hP.left f e hf

Depends on / 依赖: Ideal.span_singleton_one, IsLocalization, IsLocalization.atUnits, Localization, Localization.Away, Set.mem_singleton_iff, Submonoid, Submonoid.powers, atUnits, exists_const, forall_eq, hP.left, mem_singleton_iff, powers, span_singleton_one, toRingEquiv
-/
lemma locally_of (hP : RespectsIso P) (f : R ->+* S) (hf : P f) : Locally P f := by
  use {1}
  let e : S ≃+* Localization.Away (1 : S) :=
    (IsLocalization.atUnits S (Submonoid.powers 1) (by simp)).toRingEquiv
  simp only [Set.mem_singleton_iff, forall_eq, Ideal.span_singleton_one, exists_const]
  exact hP.left f e hf

/--
lemma `locally_of_locally` / 引理 `locally_of_locally`

English:
lemma locally_of_locally
  statement: {Q : forall {R S : Type u} [CommRing R] [CommRing S], (R ->+* S) -> Prop}
  proof: by
  obtain ⟨s, hsone, hs⟩ := hf
  exact ⟨s, hsone, fun t ht => hPQ (hs t ht)⟩

中文:
引理 locally_of_locally
  结论: {Q : 对任意 {R S : 类型u} [CommRing R] [CommRing S], (R ->+* S) -> 命题}
  证明: by
  obtain ⟨s, hsone, hs⟩ := hf
  exact ⟨s, hsone, fun t ht => hPQ (hs t ht)⟩
-/
lemma locally_of_locally {Q : forall {R S : Type u} [CommRing R] [CommRing S], (R ->+* S) -> Prop}
    (hPQ : forall {R S : Type u} [CommRing R] [CommRing S] {f : R ->+* S}, P f -> Q f)
    {R S : Type u} [CommRing R] [CommRing S] {f : R ->+* S} (hf : Locally P f) : Locally Q f := by
  obtain ⟨s, hsone, hs⟩ := hf
  exact ⟨s, hsone, fun t ht => hPQ (hs t ht)⟩

/--
lemma `locally_iff_of_localizationSpanTarget` / 引理 `locally_iff_of_localizationSpanTarget`

English:
lemma locally_iff_of_localizationSpanTarget
  statement: (hPi : RespectsIso P)
  proof: ⟨fun ⟨s, hsone, hs⟩ => hPs f s hsone (fun a => hs a.val a.property), locally_of hPi f⟩

中文:
引理 locally_iff_of_localizationSpanTarget
  结论: (hPi : RespectsIso P)
  证明: ⟨fun ⟨s, hsone, hs⟩ => hPs f s hsone (fun a => hs a.val a.property), locally_of hPi f⟩

Depends on / 依赖: a.property, a.val, locally_of, property
-/
lemma locally_iff_of_localizationSpanTarget (hPi : RespectsIso P)
    (hPs : OfLocalizationSpanTarget P) {R S : Type u} [CommRing R] [CommRing S] (f : R ->+* S) :
    Locally P f ↔ P f :=
  ⟨fun ⟨s, hsone, hs⟩ => hPs f s hsone (fun a => hs a.val a.property), locally_of hPi f⟩

section OfLocalizationSpanTarget

/--
lemma `locally_ofLocalizationSpanTarget` / 引理 `locally_ofLocalizationSpanTarget`

English:
lemma locally_ofLocalizationSpanTarget
  given: (hP : RespectsIso P)
  proof: by
  intro R S _ _ f s hsone hs
  choose t htone ht using hs
  rw [locally_iff_exists hP]
  refine ⟨(a : s) × t a, IsLocalization.Away.mulNumerator s t,
      IsLocalization.Away.span_range_mulNumerator_eq_top hsone htone,
      fun ⟨a, b⟩ => Localization.Away b.val, inferInstance, inferInstance, fu

中文:
引理 locally_ofLocalizationSpanTarget
  条件: (hP : RespectsIso P)
  证明: by
  intro R S _ _ f s hsone hs
  choose t htone ht using hs
  rw [locally_iff_exists hP]
  refine ⟨(a : s) × t a, IsLocalization.Away.mulNumerator s t,
      IsLocalization.Away.span_range_mulNumerator_eq_top hsone htone,
      fun ⟨a, b⟩ => Localization.Away b.val, inferInstance, inferInstance, fu

Depends on / 依赖: IsLocalization, IsLocalization.Away, IsLocalization.Away.mulNumerator, IsLocalization.Away.of_associated, IsLocalization.Away.sec, IsLocalization.Away.span_range_mulNumerator_eq_top, Localization, Localization.Away, a.val, algebraMap, b.val, locally_iff_exists, mulNumerator, of_associated, span_range_mulNumerator_eq_top
-/
lemma locally_ofLocalizationSpanTarget (hP : RespectsIso P) :
    OfLocalizationSpanTarget (Locally P) := by
  intro R S _ _ f s hsone hs
  choose t htone ht using hs
  rw [locally_iff_exists hP]
  refine ⟨(a : s) × t a, IsLocalization.Away.mulNumerator s t,
      IsLocalization.Away.span_range_mulNumerator_eq_top hsone htone,
      fun ⟨a, b⟩ => Localization.Away b.val, inferInstance, inferInstance, fun ⟨a, b⟩ => ?_, ?_⟩
  · have : IsLocalization.Away ((algebraMap S (Localization.Away a.val))
        (IsLocalization.Away.sec a.val b.val).1) (Localization.Away b.val) := by
      apply IsLocalization.Away.of_associated (r := b.val)
      rw [← IsLocalization.Away.sec_spec]
      apply associated_mul_unit_right
      rw [map_pow _ _]
      exact IsUnit.pow _ (IsLocalization.Away.algebraMap_isUnit _)
    apply IsLocalization.Away.mul' (Localization.Away a.val) (Localization.Away b.val)
  · intro ⟨a, b⟩
    rw [IsScalarTower.algebraMap_eq S (Localization.Away a.val) (Localization.Away b.val)]
    apply ht _ _ b.property

end OfLocalizationSpanTarget

section Stability

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `locally_respectsIso` / 引理 `locally_respectsIso`

English:
lemma locally_respectsIso
  given: (hPi : RespectsIso P)
  statement: RespectsIso (Locally P) where
  proof: fun ⟨s, hsone, hs⟩ => by
    refine ⟨e '' s, ?_, ?_⟩
    · rw [← Ideal.map_span, hsone, Ideal.map_top]
    · rintro - ⟨a, ha, rfl⟩
      let e' : Localization.Away a ≃+* Localization.Away (e a) :=
        IsLocalization.ringEquivOfRingEquiv _ _ e (Submonoid.map_powers e a)
      have : (algebraMap T

中文:
引理 locally_respectsIso
  条件: (hPi : RespectsIso P)
  结论: RespectsIso (Locally P) where
  证明: fun ⟨s, hsone, hs⟩ => by
    refine ⟨e '' s, ?_, ?_⟩
    · rw [← Ideal.map_span, hsone, Ideal.map_top]
    · rintro - ⟨a, ha, rfl⟩
      let e' : Localization.Away a ≃+* Localization.Away (e a) :=
        IsLocalization.ringEquivOfRingEquiv _ _ e (Submonoid.map_powers e a)
      have : (algebraMap T

Depends on / 依赖: Ideal.map_span, Ideal.map_top, IsLocalization, IsLocalization.ringEquivOfRingEquiv, Localization, Localization.Away, RingHom, RingHom.comp_assoc, Submonoid, Submonoid.map_powers, algebraMap, comp_assoc, e.toRingHom, hPi.left, map_powers, map_span, map_top, ringEquivOfRingEquiv, toRingHom, toRingHom.comp
-/
lemma locally_respectsIso (hPi : RespectsIso P) : RespectsIso (Locally P) where
  left {R S T} _ _ _ f e := fun ⟨s, hsone, hs⟩ => by
    refine ⟨e '' s, ?_, ?_⟩
    · rw [← Ideal.map_span, hsone, Ideal.map_top]
    · rintro - ⟨a, ha, rfl⟩
      let e' : Localization.Away a ≃+* Localization.Away (e a) :=
        IsLocalization.ringEquivOfRingEquiv _ _ e (Submonoid.map_powers e a)
      have : (algebraMap T (Localization.Away (e a))).comp e.toRingHom =
          e'.toRingHom.comp (algebraMap S (Localization.Away a)) := by
        ext x
        simp [e']
      rw [← RingHom.comp_assoc]; rw [this]; rw [RingHom.comp_assoc]
      apply hPi.left
      exact hs a ha
  right {R S T} _ _ _ f e := fun ⟨s, hsone, hs⟩ =>
    ⟨s, hsone, fun a ha => (RingHom.comp_assoc _ _ _).symm ▸ hPi.right _ _ (hs a ha)⟩

/--
lemma `locally_holdsForLocalizationAway` / 引理 `locally_holdsForLocalizationAway`

English:
lemma locally_holdsForLocalizationAway
  given: (hPa : HoldsForLocalizationAway P)
  proof: by
  introv R _
  use {1}
  simp only [Set.mem_singleton_iff, forall_eq, Ideal.span_singleton_one, exists_const]
  let e : S ≃ₐ[R] (Localization.Away (1 : S)) :=
    (IsLocalization.atUnits S (Submonoid.powers 1) (by simp)).restrictScalars R
  have : IsLocalization.Away r (Localization.Away (1 : S))

中文:
引理 locally_holdsForLocalizationAway
  条件: (hPa : HoldsForLocalizationAway P)
  证明: by
  introv R _
  use {1}
  simp only [Set.mem_singleton_iff, forall_eq, Ideal.span_singleton_one, exists_const]
  let e : S ≃ₐ[R] (Localization.Away (1 : S)) :=
    (IsLocalization.atUnits S (Submonoid.powers 1) (by simp)).restrictScalars R
  have : IsLocalization.Away r (Localization.Away (1 : S))

Depends on / 依赖: Ideal.span_singleton_one, IsLocalization, IsLocalization.Away, IsLocalization.atUnits, IsLocalization.isLocalization_of_algEquiv, IsScalarTower, IsScalarTower.algebraMap_eq, Localization, Localization.Away, Set.mem_singleton_iff, Submonoid, Submonoid.powers, algebraMap_eq, atUnits, exists_const, forall_eq, introv, isLocalization_of_algEquiv, mem_singleton_iff, powers
-/
lemma locally_holdsForLocalizationAway (hPa : HoldsForLocalizationAway P) :
    HoldsForLocalizationAway (Locally P) := by
  introv R _
  use {1}
  simp only [Set.mem_singleton_iff, forall_eq, Ideal.span_singleton_one, exists_const]
  let e : S ≃ₐ[R] (Localization.Away (1 : S)) :=
    (IsLocalization.atUnits S (Submonoid.powers 1) (by simp)).restrictScalars R
  have : IsLocalization.Away r (Localization.Away (1 : S)) :=
    IsLocalization.isLocalization_of_algEquiv (Submonoid.powers r) e
  rw [← IsScalarTower.algebraMap_eq]
  apply hPa _ r

/--
lemma `locally_stableUnderComposition` / 引理 `locally_stableUnderComposition`

English:
lemma locally_stableUnderComposition
  statement: (hPi : RespectsIso P) (hPl : LocalizationPreserves P)
  proof: by
  classical
  intro R S T _ _ _ f g hf hg
  rw [locally_iff_finite] at hf hg
  obtain ⟨sf, hsfone, hsf⟩ := hf
  obtain ⟨sg, hsgone, hsg⟩ := hg
  rw [locally_iff_exists hPi]
  refine ⟨sf × sg, fun (a, b) => g a * b, ?_,
      fun (a, b) => Localization.Away ((algebraMap T (Localization.Away b.val)

中文:
引理 locally_stableUnderComposition
  结论: (hPi : RespectsIso P) (hPl : LocalizationPreserves P)
  证明: by
  classical
  intro R S T _ _ _ f g hf hg
  rw [locally_iff_finite] at hf hg
  obtain ⟨sf, hsfone, hsf⟩ := hf
  obtain ⟨sg, hsgone, hsg⟩ := hg
  rw [locally_iff_exists hPi]
  refine ⟨sf × sg, fun (a, b) => g a * b, ?_,
      fun (a, b) => Localization.Away ((algebraMap T (Localization.Away b.val)

Depends on / 依赖: Ideal.mem_span, Ideal.span, Ideal.span_le, Localization, Localization.Away, Set.range, a.val, algebraMap, b.val, classical, eq_top_iff, hsfone, hsgone, locally_iff_exists, locally_iff_finite, mem_span, span_le
-/
lemma locally_stableUnderComposition (hPi : RespectsIso P) (hPl : LocalizationPreserves P)
    (hPc : StableUnderComposition P) :
    StableUnderComposition (Locally P) := by
  classical
  intro R S T _ _ _ f g hf hg
  rw [locally_iff_finite] at hf hg
  obtain ⟨sf, hsfone, hsf⟩ := hf
  obtain ⟨sg, hsgone, hsg⟩ := hg
  rw [locally_iff_exists hPi]
  refine ⟨sf × sg, fun (a, b) => g a * b, ?_,
      fun (a, b) => Localization.Away ((algebraMap T (Localization.Away b.val)) (g a.val)),
      inferInstance, inferInstance, inferInstance, ?_⟩
  · rw [eq_top_iff, ← hsgone, Ideal.span_le]
    intro t ht
    have : 1 in Ideal.span (Set.range <| fun a : sf => a.val) := by simp [hsfone]
    simp only [Ideal.mem_span_range_iff_exists_fun, SetLike.mem_coe] at this ⊢
    obtain ⟨cf, hcf⟩ := this
    let cg : sg -> T := Pi.single ⟨t, ht⟩ 1
    use fun (a, b) => g (cf a) * cg b
    simp [cg, Pi.single_apply, Fintype.sum_prod_type, ← mul_assoc, ← Finset.sum_mul, ← map_mul,
      ← map_sum, hcf] at hcf ⊢
  · intro ⟨a, b⟩
    let g' := (algebraMap T (Localization.Away b.val)).comp g
    let a' := (algebraMap T (Localization.Away b.val)) (g a.val)
    have : (algebraMap T <| Localization.Away a').comp (g.comp f) =
        (Localization.awayMap g' a.val).comp ((algebraMap S (Localization.Away a.val)).comp f) := by
      ext x
      simp only [coe_comp, Function.comp_apply, a']
      change _ = Localization.awayMap g' a.val (algebraMap S _ (f x))
      simp only [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
      rfl
    simp only [this, a']
    apply hPc _ _ (hsf a.val a.property)
    apply @hPl _ _ _ _ g' _ _ _ _ _ _ _ _ ?_ (hsg b.val b.property)
    exact IsLocalization.Away.instMapRingHomPowersOfCoe (Localization.Away (g' a.val)) a.val

/--
lemma `locally_stableUnderCompositionWithLocalizationAwayTarget` / 引理 `locally_stableUnderCompositionWithLocalizationAwayTarget`

English:
lemma locally_stableUnderCompositionWithLocalizationAwayTarget
  proof: by
  intro R S T _ _ _ _ t _ f hf
  obtain ⟨s, hsone, hs⟩ := hf
  refine ⟨algebraMap S T '' s, ?_, ?_⟩
  · rw [← Ideal.map_span, hsone, Ideal.map_top]
  · rintro - ⟨a, ha, rfl⟩
    let : Algebra (Localization.Away a) (Localization.Away (algebraMap S T a)) :=
      (IsLocalization.Away.map _ _ (algeb

中文:
引理 locally_stableUnderCompositionWithLocalizationAwayTarget
  证明: by
  intro R S T _ _ _ _ t _ f hf
  obtain ⟨s, hsone, hs⟩ := hf
  refine ⟨algebraMap S T '' s, ?_, ?_⟩
  · rw [← Ideal.map_span, hsone, Ideal.map_top]
  · rintro - ⟨a, ha, rfl⟩
    let : Algebra (Localization.Away a) (Localization.Away (algebraMap S T a)) :=
      (IsLocalization.Away.map _ _ (algeb

Depends on / 依赖: Algebra, Ideal.map_span, Ideal.map_top, IsLocalization, IsLocalization.Away.map, Localization, Localization.Away, algebraMap, map_span, map_top, toAlgebra
-/
lemma locally_stableUnderCompositionWithLocalizationAwayTarget
    (hPa : StableUnderCompositionWithLocalizationAwayTarget P) :
    StableUnderCompositionWithLocalizationAwayTarget (Locally P) := by
  intro R S T _ _ _ _ t _ f hf
  obtain ⟨s, hsone, hs⟩ := hf
  refine ⟨algebraMap S T '' s, ?_, ?_⟩
  · rw [← Ideal.map_span, hsone, Ideal.map_top]
  · rintro - ⟨a, ha, rfl⟩
    let : Algebra (Localization.Away a) (Localization.Away (algebraMap S T a)) :=
      (IsLocalization.Away.map _ _ (algebraMap S T) a).toAlgebra
    have : (algebraMap (Localization.Away a) (Localization.Away (algebraMap S T a))).comp
        (algebraMap S (Localization.Away a)) =
        (algebraMap T (Localization.Away (algebraMap S T a))).comp (algebraMap S T) := by
      simp [algebraMap_toAlgebra, IsLocalization.Away.map]
    rw [← comp_assoc]; rw [← this]; rw [comp_assoc]
    have : IsScalarTower S (Localization.Away a) (Localization.Away ((algebraMap S T) a)) := by
      apply IsScalarTower.of_algebraMap_eq
      intro x
      simp [algebraMap_toAlgebra, IsLocalization.Away.map, ← IsScalarTower.algebraMap_apply]
    have : IsLocalization.Away (algebraMap S (Localization.Away a) t)
        (Localization.Away (algebraMap S T a)) :=
      IsLocalization.Away.commutes _ T ((Localization.Away (algebraMap S T a))) a t
    apply hPa _ (algebraMap S (Localization.Away a) t)
    apply hs a ha

@[deprecated (since := "2026-02-11")]
alias locally_StableUnderCompositionWithLocalizationAwayTarget :=
  locally_stableUnderCompositionWithLocalizationAwayTarget

/--
lemma `locally_stableUnderCompositionWithLocalizationAwaySource` / 引理 `locally_stableUnderCompositionWithLocalizationAwaySource`

English:
lemma locally_stableUnderCompositionWithLocalizationAwaySource
  proof: by
  intro R S T _ _ _ _ r _ f ⟨s, hsone, hs⟩
  refine ⟨s, hsone, fun t ht => ?_⟩
  rw [← comp_assoc]
  exact hPa _ r _ (hs t ht)

@[deprecated (since := "2026-02-11")]
alias locally_StableUnderCompositionWithLocalizationAwaySource :=
  locally_stableUnderCompositionWithLocalizationAwaySource

中文:
引理 locally_stableUnderCompositionWithLocalizationAwaySource
  证明: by
  intro R S T _ _ _ _ r _ f ⟨s, hsone, hs⟩
  refine ⟨s, hsone, fun t ht => ?_⟩
  rw [← comp_assoc]
  exact hPa _ r _ (hs t ht)

@[deprecated (since := "2026-02-11")]
alias locally_StableUnderCompositionWithLocalizationAwaySource :=
  locally_stableUnderCompositionWithLocalizationAwaySource

Depends on / 依赖: comp_assoc
-/
lemma locally_stableUnderCompositionWithLocalizationAwaySource
    (hPa : StableUnderCompositionWithLocalizationAwaySource P) :
    StableUnderCompositionWithLocalizationAwaySource (Locally P) := by
  intro R S T _ _ _ _ r _ f ⟨s, hsone, hs⟩
  refine ⟨s, hsone, fun t ht => ?_⟩
  rw [← comp_assoc]
  exact hPa _ r _ (hs t ht)

@[deprecated (since := "2026-02-11")]
alias locally_StableUnderCompositionWithLocalizationAwaySource :=
  locally_stableUnderCompositionWithLocalizationAwaySource

/--
lemma `locally_isStableUnderBaseChange` / 引理 `locally_isStableUnderBaseChange`

English:
lemma locally_isStableUnderBaseChange
  given: (hPi : RespectsIso P) (hPb : IsStableUnderBaseChange P)
  proof: by
  apply IsStableUnderBaseChange.mk (locally_respectsIso hPi)
  introv hf
  rw [locally_iff_span_eq_top]; rw [eq_top_iff]; rw [← Ideal.map_top Algebra.TensorProduct.includeRight]; rw [← hf.span_eq_top]; rw [Ideal.map_le_iff_le_comap]; rw [Ideal.span_le]
  intro g hg
  apply Ideal.subset_span
  sim

中文:
引理 locally_isStableUnderBaseChange
  条件: (hPi : RespectsIso P) (hPb : IsStableUnderBaseChange P)
  证明: by
  apply IsStableUnderBaseChange.mk (locally_respectsIso hPi)
  introv hf
  rw [locally_iff_span_eq_top]; rw [eq_top_iff]; rw [← Ideal.map_top Algebra.TensorProduct.includeRight]; rw [← hf.span_eq_top]; rw [Ideal.map_le_iff_le_comap]; rw [Ideal.span_le]
  intro g hg
  apply Ideal.subset_span
  sim

Depends on / 依赖: Algebra, Algebra.TensorProduct.includeRight, Algebra.TensorProduct.includeRight_apply, Ideal.map_le_iff_le_comap, Ideal.map_top, Ideal.span_le, Ideal.subset_span, IsLocalization, IsLocalization.Away.tensorProductEquivTMulRight, IsScalarTower, IsScalarTower.algebraMap_eq, IsStableUnderBaseChange, IsStableUnderBaseChange.mk, Localization, Localization.Away, Set.mem_ofPred_eq, TensorProduct, algebraMap_eq, e.toAlgHom.co, eq_top_iff
-/
lemma locally_isStableUnderBaseChange (hPi : RespectsIso P) (hPb : IsStableUnderBaseChange P) :
    IsStableUnderBaseChange (Locally P) := by
  apply IsStableUnderBaseChange.mk (locally_respectsIso hPi)
  introv hf
  rw [locally_iff_span_eq_top]; rw [eq_top_iff]; rw [← Ideal.map_top Algebra.TensorProduct.includeRight]; rw [← hf.span_eq_top]; rw [Ideal.map_le_iff_le_comap]; rw [Ideal.span_le]
  intro g hg
  apply Ideal.subset_span
  simp only [Set.mem_ofPred_eq, Algebra.TensorProduct.includeRight_apply,
    ← IsScalarTower.algebraMap_eq] at hg ⊢
  let e := IsLocalization.Away.tensorProductEquivTMulRight R S g (Localization.Away g)
  rw [← e.toAlgHom.comp_algebraMap]
  exact hPi.left _ _ (hPb.tensorProduct _ hg)

/--
lemma `locally_localizationAwayPreserves` / 引理 `locally_localizationAwayPreserves`

English:
lemma locally_localizationAwayPreserves
  given: (hPl : LocalizationAwayPreserves P)
  proof: by
  introv R hf
  obtain ⟨s, hsone, hs⟩ := hf
  rw [locally_iff_exists hPl.respectsIso]
  let rₐ (a : s) : Localization.Away a.val := algebraMap _ _ (f r)
  let Sₐ (a : s) := Localization.Away (rₐ a)
  have (a : s) :
      IsLocalization.Away (((algebraMap S (Localization.Away a.val)).comp f) r) (S

中文:
引理 locally_localizationAwayPreserves
  条件: (hPl : LocalizationAwayPreserves P)
  证明: by
  introv R hf
  obtain ⟨s, hsone, hs⟩ := hf
  rw [locally_iff_exists hPl.respectsIso]
  let rₐ (a : s) : Localization.Away a.val := algebraMap _ _ (f r)
  let Sₐ (a : s) := Localization.Away (rₐ a)
  have (a : s) :
      IsLocalization.Away (((algebraMap S (Localization.Away a.val)).comp f) r) (S

Depends on / 依赖: Algebra, Algebra.algebraMapSubmonoid, IsLocalization, IsLocalization.Away, Localization, Localization.Away, Submonoid, Submonoid.map, Submonoid.powers, a.val, algebraMap, algebraMapSubmonoid, convert, hPl.respectsIso, inferInsta, introv, locally_iff_exists, powers, respectsIso
-/
lemma locally_localizationAwayPreserves (hPl : LocalizationAwayPreserves P) :
    LocalizationAwayPreserves (Locally P) := by
  introv R hf
  obtain ⟨s, hsone, hs⟩ := hf
  rw [locally_iff_exists hPl.respectsIso]
  let rₐ (a : s) : Localization.Away a.val := algebraMap _ _ (f r)
  let Sₐ (a : s) := Localization.Away (rₐ a)
  have (a : s) :
      IsLocalization.Away (((algebraMap S (Localization.Away a.val)).comp f) r) (Sₐ a) :=
    inferInstanceAs (IsLocalization.Away (rₐ a) (Sₐ a))
  have (a : s) : IsLocalization (Algebra.algebraMapSubmonoid (Localization.Away a.val)
    (Submonoid.map f (Submonoid.powers r))) (Sₐ a) := by
    convert! (inferInstance : IsLocalization.Away (rₐ a) (Sₐ a))
    simp [rₐ, Algebra.algebraMapSubmonoid]
  have H (a : s) : Submonoid.powers (f r) <=
      (Submonoid.powers (rₐ a)).comap (algebraMap S (Localization.Away a.val)) := by
    simp [rₐ, Submonoid.powers_le]
  let (a : s) : Algebra S' (Sₐ a) :=
    (IsLocalization.map (Sₐ a) (algebraMap S (Localization.Away a.val)) (H a)).toAlgebra
  have (a : s) : IsScalarTower S S' (Sₐ a) :=
    IsScalarTower.of_algebraMap_eq' (IsLocalization.map_comp (H a)).symm
  refine ⟨s, fun a => algebraMap S S' a.val, ?_, Sₐ,
      inferInstance, inferInstance, fun a => ?_, fun a => ?_⟩
  · rw [← Set.image_eq_range, ← Ideal.map_span, hsone, Ideal.map_top]
  · convert!
    IsLocalization.commutes (T := Sₐ a) (M₁ := (Submonoid.powers r).map f) (S₁ := S') (S₂ :=
      Localization.Away a.val) (M₂ := Submonoid.powers a.val)
    simp [Algebra.algebraMapSubmonoid]
  · rw [algebraMap_toAlgebra, IsLocalization.Away.map, IsLocalization.map_comp_map]
    exact hPl ((algebraMap _ (Localization.Away a.val)).comp f) r R' (Sₐ a) (hs _ a.2)

/--
lemma `locally_localizationPreserves` / 引理 `locally_localizationPreserves`

English:
lemma locally_localizationPreserves
  given: (hPl : LocalizationPreserves P)
  proof: by
  introv R hf
  obtain ⟨s, hsone, hs⟩ := hf
  rw [locally_iff_exists hPl.away.respectsIso]
  let Mₐ (a : s) : Submonoid (Localization.Away a.val) :=
    (M.map f).map (algebraMap S (Localization.Away a.val))
  let Sₐ (a : s) := Localization (Mₐ a)
  have hM (a : s) : M.map ((algebraMap S (Localiz

中文:
引理 locally_localizationPreserves
  条件: (hPl : LocalizationPreserves P)
  证明: by
  introv R hf
  obtain ⟨s, hsone, hs⟩ := hf
  rw [locally_iff_exists hPl.away.respectsIso]
  let Mₐ (a : s) : Submonoid (Localization.Away a.val) :=
    (M.map f).map (algebraMap S (Localization.Away a.val))
  let Sₐ (a : s) := Localization (Mₐ a)
  have hM (a : s) : M.map ((algebraMap S (Localiz

Depends on / 依赖: IsLocalization, Localization, Localization.Away, M.map, M.map_map, Submonoid, a.val, algebraMap, hPl.away.respectsIso, infer_instance, introv, locally_iff_exists, map_map, respectsIso
-/
lemma locally_localizationPreserves (hPl : LocalizationPreserves P) :
    LocalizationPreserves (Locally P) := by
  introv R hf
  obtain ⟨s, hsone, hs⟩ := hf
  rw [locally_iff_exists hPl.away.respectsIso]
  let Mₐ (a : s) : Submonoid (Localization.Away a.val) :=
    (M.map f).map (algebraMap S (Localization.Away a.val))
  let Sₐ (a : s) := Localization (Mₐ a)
  have hM (a : s) : M.map ((algebraMap S (Localization.Away a.val)).comp f) = Mₐ a :=
    (M.map_map _ _).symm
  have (a : s) :
      IsLocalization (M.map ((algebraMap S (Localization.Away a.val)).comp f)) (Sₐ a) := by
    rw [hM]
    infer_instance
  have (a : s) :
      IsLocalization (Algebra.algebraMapSubmonoid (Localization.Away a.val) (M.map f)) (Sₐ a) :=
inferInstanceAs IsLocalization (Mₐ a) (Sₐ a)
  let (a : s) : Algebra S' (Sₐ a) :=
    (IsLocalization.map (Sₐ a) (algebraMap S (Localization.Away a.val))
      (M.map f).le_comap_map).toAlgebra
  have (a : s) : IsScalarTower S S' (Sₐ a) :=
    IsScalarTower.of_algebraMap_eq' (IsLocalization.map_comp (M.map f).le_comap_map).symm
  refine ⟨s, fun a => algebraMap S S' a.val, ?_, Sₐ,
      inferInstance, inferInstance, fun a => ?_, fun a => ?_⟩
  · rw [← Set.image_eq_range, ← Ideal.map_span, hsone, Ideal.map_top]
  · convert!
    IsLocalization.commutes (T := Sₐ a) (M₁ := M.map f) (S₁ := S') (S₂ := Localization.Away a.val)
      (M₂ := Submonoid.powers a.val)
    simp [Algebra.algebraMapSubmonoid]
  · rw [algebraMap_toAlgebra, IsLocalization.map_comp_map]
    apply hPl
    exact hs a.val a.property

/--
lemma `locally_propertyIsLocal` / 引理 `locally_propertyIsLocal`

English:
lemma locally_propertyIsLocal
  statement: (hPl : LocalizationAwayPreserves P)
  proof: locally_localizationAwayPreserves hPl
  StableUnderCompositionWithLocalizationAwayTarget :=
    locally_stableUnderCompositionWithLocalizationAwayTarget hPa.right
  ofLocalizationSpan := (locally_ofLocalizationSpanTarget hPl.respectsIso).ofLocalizationSpan
    (locally_stableUnderCompositionWithLoca

中文:
引理 locally_propertyIsLocal
  结论: (hPl : LocalizationAwayPreserves P)
  证明: locally_localizationAwayPreserves hPl
  StableUnderCompositionWithLocalizationAwayTarget :=
    locally_stableUnderCompositionWithLocalizationAwayTarget hPa.right
  ofLocalizationSpan := (locally_ofLocalizationSpanTarget hPl.respectsIso).ofLocalizationSpan
    (locally_stableUnderCompositionWithLoca

Depends on / 依赖: locally_localizationAwayPreserves
-/
lemma locally_propertyIsLocal (hPl : LocalizationAwayPreserves P)
    (hPa : StableUnderCompositionWithLocalizationAway P) : PropertyIsLocal (Locally P) where
  localizationAwayPreserves := locally_localizationAwayPreserves hPl
  StableUnderCompositionWithLocalizationAwayTarget :=
    locally_stableUnderCompositionWithLocalizationAwayTarget hPa.right
  ofLocalizationSpan := (locally_ofLocalizationSpanTarget hPl.respectsIso).ofLocalizationSpan
    (locally_stableUnderCompositionWithLocalizationAwaySource hPa.left)
  ofLocalizationSpanTarget := locally_ofLocalizationSpanTarget hPl.respectsIso

end Stability

end RingHom
