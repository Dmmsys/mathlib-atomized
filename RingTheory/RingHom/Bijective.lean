/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.RingTheory.LocalProperties.Exactness

/-!
# Meta properties of bijective ring homomorphisms

We show some meta properties of bijective ring homomorphisms.

## Implementation details

We don't define a `RingHom.Bijective` predicate, but use `fun f ↦ Function.Bijective f` as
the ring hom property.
-/

public section

open TensorProduct

variable {R S : Type*} [CommRing R] [CommRing S]

namespace RingHom.Bijective

/--
lemma `containsIdentities` / 引理 `containsIdentities`

English:
lemma containsIdentities
  statement: ContainsIdentities (fun f => Function.Bijective f)
  proof: fun _ _ => Function.bijective_id

中文:
引理 containsIdentities
  结论: ContainsIdentities (fun f => Function.Bijective f)
  证明: fun _ _ => Function.bijective_id

Depends on / 依赖: Function, Function.bijective_id, bijective_id
-/
lemma containsIdentities : ContainsIdentities (fun f => Function.Bijective f) :=
  fun _ _ => Function.bijective_id

/--
lemma `stableUnderComposition` / 引理 `stableUnderComposition`

English:
lemma stableUnderComposition
  statement: StableUnderComposition (fun f => Function.Bijective f)
  proof: fun _ _ _ _ _ _ _ _ hf hg => hg.comp hf

中文:
引理 stableUnderComposition
  结论: StableUnderComposition (fun f => Function.Bijective f)
  证明: fun _ _ _ _ _ _ _ _ hf hg => hg.comp hf

Depends on / 依赖: hg.comp
-/
lemma stableUnderComposition : StableUnderComposition (fun f => Function.Bijective f) :=
  fun _ _ _ _ _ _ _ _ hf hg => hg.comp hf

/--
lemma `respectsIso` / 引理 `respectsIso`

English:
lemma respectsIso
  statement: RespectsIso (fun f => Function.Bijective f)
  proof: RingHom.Bijective.stableUnderComposition.respectsIso fun e => e.bijective

中文:
引理 respectsIso
  结论: RespectsIso (fun f => Function.Bijective f)
  证明: RingHom.Bijective.stableUnderComposition.respectsIso fun e => e.bijective

Depends on / 依赖: Bijective, RingHom, RingHom.Bijective.stableUnderComposition.respectsIso, bijective, e.bijective, respectsIso, stableUnderComposition
-/
lemma respectsIso : RespectsIso (fun f => Function.Bijective f) :=
  RingHom.Bijective.stableUnderComposition.respectsIso fun e => e.bijective

/--
lemma `isStableUnderBaseChange` / 引理 `isStableUnderBaseChange`

English:
lemma isStableUnderBaseChange
  statement: IsStableUnderBaseChange (fun f => Function.Bijective f)
  proof: .mk respectsIso fun R _ _ _ _ _ _ _ hf =>
    Algebra.TensorProduct.includeLeft_bijective (S := R) hf

中文:
引理 isStableUnderBaseChange
  结论: IsStableUnderBaseChange (fun f => Function.Bijective f)
  证明: .mk respectsIso fun R _ _ _ _ _ _ _ hf =>
    Algebra.TensorProduct.includeLeft_bijective (S := R) hf

Depends on / 依赖: Algebra, Algebra.TensorProduct.includeLeft_bijective, TensorProduct, includeLeft_bijective, respectsIso
-/
lemma isStableUnderBaseChange : IsStableUnderBaseChange (fun f => Function.Bijective f) :=
  .mk respectsIso fun R _ _ _ _ _ _ _ hf =>
    Algebra.TensorProduct.includeLeft_bijective (S := R) hf

/--
lemma `ofLocalizationSpan` / 引理 `ofLocalizationSpan`

English:
lemma ofLocalizationSpan
  statement: OfLocalizationSpan (fun f => Function.Bijective f)
  proof: fun _ _ _ _ f s hs hf => bijective_of_isLocalization_of_span_eq_top (s := s) hs
    (fun r => Localization.Away r.val) (fun r => Localization.Away (f r.val)) f hf

中文:
引理 ofLocalizationSpan
  结论: OfLocalizationSpan (fun f => Function.Bijective f)
  证明: fun _ _ _ _ f s hs hf => bijective_of_isLocalization_of_span_eq_top (s := s) hs
    (fun r => Localization.Away r.val) (fun r => Localization.Away (f r.val)) f hf

Depends on / 依赖: Localization, Localization.Away, bijective_of_isLocalization_of_span_eq_top, r.val
-/
lemma ofLocalizationSpan : OfLocalizationSpan (fun f => Function.Bijective f) :=
  fun _ _ _ _ f s hs hf => bijective_of_isLocalization_of_span_eq_top (s := s) hs
    (fun r => Localization.Away r.val) (fun r => Localization.Away (f r.val)) f hf

end RingHom.Bijective
