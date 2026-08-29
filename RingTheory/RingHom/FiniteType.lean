/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.Finiteness.FiniteTypeLocal
public import Mathlib.RingTheory.Localization.InvSubmonoid
public import Mathlib.RingTheory.RingHom.Finite

/-!

# The meta properties of finite-type ring homomorphisms.

## Main results

Let `R` be a commutative ring, `S` is an `R`-algebra, `M` be a submonoid of `R`.

* `finiteType_localizationPreserves` : If `S` is a finite type `R`-algebra, then `S' = M⁻¹S` is a
  finite type `R' = M⁻¹R`-algebra.
* `finiteType_ofLocalizationSpan` : `S` is a finite type `R`-algebra if there exists
  a set `{ r }` that spans `R` such that `Sᵣ` is a finite type `Rᵣ`-algebra.
* `RingHom.finiteType_isLocal`: `RingHom.FiniteType` is a local property.

-/

public section

namespace RingHom

open scoped Pointwise TensorProduct

universe u

variable {R S : Type*} [CommRing R] [CommRing S] (M : Submonoid R) (f : R ->+* S)
variable (R' S' : Type*) [CommRing R'] [CommRing S']
variable [Algebra R R'] [Algebra S S']

/--
theorem `finiteType_stableUnderComposition` / 定理 `finiteType_stableUnderComposition`

English:
theorem finiteType_stableUnderComposition
  statement: StableUnderComposition @FiniteType
  proof: by
  introv R hf hg
  exact hg.comp hf

中文:
定理 finiteType_stableUnderComposition
  结论: StableUnderComposition @有限型
  证明: by
  introv R hf hg
  exact hg.comp hf

Depends on / 依赖: hg.comp, introv
-/
theorem finiteType_stableUnderComposition : StableUnderComposition @FiniteType := by
  introv R hf hg
  exact hg.comp hf

/--
theorem `finiteType_respectsIso` / 定理 `finiteType_respectsIso`

English:
theorem finiteType_respectsIso
  statement: RingHom.RespectsIso @RingHom.FiniteType
  proof: by
  refine finiteType_stableUnderComposition.respectsIso (fun {R S} _ _ e => ?_)
  algebraize [e.toRingHom]
apply Algebra.FiniteType.equiv (inferInstanceAs <| Algebra.FiniteType R R)
    .ofRingEquiv (congrFun rfl)

中文:
定理 finiteType_respectsIso
  结论: 环态射.RespectsIso @环态射.有限型
  证明: by
  refine finiteType_stableUnderComposition.respectsIso (fun {R S} _ _ e => ?_)
  algebraize [e.toRingHom]
apply Algebra.FiniteType.equiv (inferInstanceAs <| Algebra.FiniteType R R)
    .ofRingEquiv (congrFun rfl)

Depends on / 依赖: Algebra, Algebra.FiniteType, Algebra.FiniteType.equiv, FiniteType, algebraize, e.toRingHom, finiteType_stableUnderComposition, finiteType_stableUnderComposition.respectsIso, ofRingEquiv, respectsIso, toRingHom
-/
theorem finiteType_respectsIso : RingHom.RespectsIso @RingHom.FiniteType := by
  refine finiteType_stableUnderComposition.respectsIso (fun {R S} _ _ e => ?_)
  algebraize [e.toRingHom]
apply Algebra.FiniteType.equiv (inferInstanceAs <| Algebra.FiniteType R R)
    .ofRingEquiv (congrFun rfl)

/--
theorem `finiteType_isStableUnderBaseChange` / 定理 `finiteType_isStableUnderBaseChange`

English:
theorem finiteType_isStableUnderBaseChange
  statement: IsStableUnderBaseChange @FiniteType
  proof: by
  apply IsStableUnderBaseChange.mk
  · exact finiteType_respectsIso
  · introv h
    rw [finiteType_algebraMap] at h
    apply finiteType_algebraMap.mpr
    infer_instance

中文:
定理 finiteType_isStableUnderBaseChange
  结论: 是StableUnderBaseChange @有限型
  证明: by
  apply IsStableUnderBaseChange.mk
  · exact finiteType_respectsIso
  · introv h
    rw [finiteType_algebraMap] at h
    apply finiteType_algebraMap.mpr
    infer_instance

Depends on / 依赖: IsStableUnderBaseChange, IsStableUnderBaseChange.mk, finiteType_algebraMap, finiteType_algebraMap.mpr, finiteType_respectsIso, infer_instance, introv
-/
theorem finiteType_isStableUnderBaseChange : IsStableUnderBaseChange @FiniteType := by
  apply IsStableUnderBaseChange.mk
  · exact finiteType_respectsIso
  · introv h
    rw [finiteType_algebraMap] at h
    apply finiteType_algebraMap.mpr
    infer_instance

/--
theorem `finiteType_localizationPreserves` / 定理 `finiteType_localizationPreserves`

English:
theorem finiteType_localizationPreserves
  statement: RingHom.LocalizationPreserves @RingHom.FiniteType
  proof: finiteType_isStableUnderBaseChange.localizationPreserves

中文:
定理 finiteType_localizationPreserves
  结论: 环态射.LocalizationPreserves @环态射.有限型
  证明: finiteType_isStableUnderBaseChange.localizationPreserves

Depends on / 依赖: finiteType_isStableUnderBaseChange, finiteType_isStableUnderBaseChange.localizationPreserves, localizationPreserves
-/
theorem finiteType_localizationPreserves : RingHom.LocalizationPreserves @RingHom.FiniteType :=
  finiteType_isStableUnderBaseChange.localizationPreserves

/--
theorem `localization_away_map_finiteType` / 定理 `localization_away_map_finiteType`

English:
theorem localization_away_map_finiteType
  statement: (R S R' S' : Type u) [CommRing R] [CommRing S]
  proof: finiteType_localizationPreserves.away _ r _ _ hf

中文:
定理 localization_away_map_finiteType
  结论: (R S R' S' : 类型u) [交换环 R] [交换环 S]
  证明: finiteType_localizationPreserves.away _ r _ _ hf

Depends on / 依赖: finiteType_localizationPreserves, finiteType_localizationPreserves.away
-/
theorem localization_away_map_finiteType (R S R' S' : Type u) [CommRing R] [CommRing S]
    [CommRing R'] [CommRing S'] [Algebra R R'] (f : R ->+* S) [Algebra S S']
    (r : R) [IsLocalization.Away r R']
    [IsLocalization.Away (f r) S'] (hf : f.FiniteType) :
    (IsLocalization.Away.map R' S' f r).FiniteType :=
  finiteType_localizationPreserves.away _ r _ _ hf

/--
theorem `finiteType_ofLocalizationSpan` / 定理 `finiteType_ofLocalizationSpan`

English:
theorem finiteType_ofLocalizationSpan
  statement: RingHom.OfLocalizationSpan @RingHom.FiniteType
  proof: by
  refine OfLocalizationSpan.mk _ finiteType_respectsIso (fun s hs h => ?_)
  simp_rw [finiteType_algebraMap] at h ⊢
  exact Algebra.FiniteType.of_span_eq_top_source s hs h

中文:
定理 finiteType_ofLocalizationSpan
  结论: 环态射.OfLocalizationSpan @环态射.有限型
  证明: by
  refine OfLocalizationSpan.mk _ finiteType_respectsIso (fun s hs h => ?_)
  simp_rw [finiteType_algebraMap] at h ⊢
  exact Algebra.FiniteType.of_span_eq_top_source s hs h

Depends on / 依赖: Algebra, Algebra.FiniteType.of_span_eq_top_source, FiniteType, OfLocalizationSpan, OfLocalizationSpan.mk, finiteType_algebraMap, finiteType_respectsIso, of_span_eq_top_source, simp_rw
-/
theorem finiteType_ofLocalizationSpan : RingHom.OfLocalizationSpan @RingHom.FiniteType := by
  refine OfLocalizationSpan.mk _ finiteType_respectsIso (fun s hs h => ?_)
  simp_rw [finiteType_algebraMap] at h ⊢
  exact Algebra.FiniteType.of_span_eq_top_source s hs h

/--
theorem `finiteType_holdsForLocalizationAway` / 定理 `finiteType_holdsForLocalizationAway`

English:
theorem finiteType_holdsForLocalizationAway
  statement: HoldsForLocalizationAway @FiniteType
  proof: by
  introv R _
  rw [finiteType_algebraMap]
  exact IsLocalization.finiteType_of_monoid_fg (Submonoid.powers r) S

中文:
定理 finiteType_holdsForLocalizationAway
  结论: HoldsForLocalizationAway @有限型
  证明: by
  introv R _
  rw [finiteType_algebraMap]
  exact IsLocalization.finiteType_of_monoid_fg (Submonoid.powers r) S

Depends on / 依赖: IsLocalization, IsLocalization.finiteType_of_monoid_fg, Submonoid, Submonoid.powers, finiteType_algebraMap, finiteType_of_monoid_fg, introv, powers
-/
theorem finiteType_holdsForLocalizationAway : HoldsForLocalizationAway @FiniteType := by
  introv R _
  rw [finiteType_algebraMap]
  exact IsLocalization.finiteType_of_monoid_fg (Submonoid.powers r) S

/--
theorem `finiteType_ofLocalizationSpanTarget` / 定理 `finiteType_ofLocalizationSpanTarget`

English:
theorem finiteType_ofLocalizationSpanTarget
  statement: OfLocalizationSpanTarget @FiniteType
  proof: by
  introv R hs H
  algebraize [f]
  replace H : forall r in s, Algebra.FiniteType R (Localization.Away (r : S)) := by
    intro r hr; simp_rw [RingHom.FiniteType] at H; convert! H ⟨r, hr⟩; ext
    simp_rw [Algebra.smul_def]; rfl
  exact Algebra.FiniteType.of_span_eq_top_target s hs H

中文:
定理 finiteType_ofLocalizationSpanTarget
  结论: OfLocalizationSpanTarget @有限型
  证明: by
  introv R hs H
  algebraize [f]
  replace H : forall r in s, Algebra.FiniteType R (Localization.Away (r : S)) := by
    intro r hr; simp_rw [RingHom.FiniteType] at H; convert! H ⟨r, hr⟩; ext
    simp_rw [Algebra.smul_def]; rfl
  exact Algebra.FiniteType.of_span_eq_top_target s hs H

Depends on / 依赖: Algebra, Algebra.FiniteType, Algebra.FiniteType.of_span_eq_top_target, Algebra.smul_def, FiniteType, Localization, Localization.Away, RingHom, RingHom.FiniteType, algebraize, convert, introv, of_span_eq_top_target, replace, simp_rw, smul_def
-/
theorem finiteType_ofLocalizationSpanTarget : OfLocalizationSpanTarget @FiniteType := by
  introv R hs H
  algebraize [f]
  replace H : forall r in s, Algebra.FiniteType R (Localization.Away (r : S)) := by
    intro r hr; simp_rw [RingHom.FiniteType] at H; convert! H ⟨r, hr⟩; ext
    simp_rw [Algebra.smul_def]; rfl
  exact Algebra.FiniteType.of_span_eq_top_target s hs H

/--
theorem `finiteType_isLocal` / 定理 `finiteType_isLocal`

English:
theorem finiteType_isLocal
  statement: PropertyIsLocal @FiniteType
  proof: ⟨finiteType_localizationPreserves.away,
    finiteType_ofLocalizationSpanTarget,
    finiteType_ofLocalizationSpanTarget.ofLocalizationSpan
      (finiteType_stableUnderComposition.stableUnderCompositionWithLocalizationAway
        finiteType_holdsForLocalizationAway).left,
    (finiteType_stableUnderComposition.stableUnderCompositionWithLocalizationAway
      finiteType_holdsForLocalizationAway).right⟩

中文:
定理 finiteType_isLocal
  结论: PropertyIsLocal @有限型
  证明: ⟨finiteType_localizationPreserves.away,
    finiteType_ofLocalizationSpanTarget,
    finiteType_ofLocalizationSpanTarget.ofLocalizationSpan
      (finiteType_stableUnderComposition.stableUnderCompositionWithLocalizationAway
        finiteType_holdsForLocalizationAway).left,
    (finiteType_stableUnderComposition.stableUnderCompositionWithLocalizationAway
      finiteType_holdsForLocalizationAway).right⟩

Depends on / 依赖: finiteType_holdsForLocalizationAway, finiteType_localizationPreserves, finiteType_localizationPreserves.away, finiteType_ofLocalizationSpanTarget, finiteType_ofLocalizationSpanTarget.ofLocalizationSpan, finiteType_stableUnderComposition, finiteType_stableUnderComposition.stableUnderCompositionWithLocalizationAway, ofLocalizationSpan, stableUnderCompositionWithLocalizationAway
-/
theorem finiteType_isLocal : PropertyIsLocal @FiniteType :=
  ⟨finiteType_localizationPreserves.away,
    finiteType_ofLocalizationSpanTarget,
    finiteType_ofLocalizationSpanTarget.ofLocalizationSpan
      (finiteType_stableUnderComposition.stableUnderCompositionWithLocalizationAway
        finiteType_holdsForLocalizationAway).left,
    (finiteType_stableUnderComposition.stableUnderCompositionWithLocalizationAway
      finiteType_holdsForLocalizationAway).right⟩

end RingHom
