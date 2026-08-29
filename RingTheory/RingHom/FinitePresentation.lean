/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.RingHom.FiniteType
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot
public import Mathlib.RingTheory.Finiteness.FinitePresentationLocal

/-!

# The meta properties of finitely-presented ring homomorphisms.

The main result is `RingHom.finitePresentation_isLocal`.

-/

public section

open scoped Pointwise TensorProduct

namespace RingHom

/--
theorem `finitePresentation_stableUnderComposition` / 定理 `finitePresentation_stableUnderComposition`

English:
theorem finitePresentation_stableUnderComposition
  statement: StableUnderComposition @FinitePresentation
  proof: by
  introv R hf hg
  exact hg.comp hf

中文:
定理 finitePresentation_stableUnderComposition
  结论: StableUnderComposition @有限呈现
  证明: by
  introv R hf hg
  exact hg.comp hf

Depends on / 依赖: hg.comp, introv
-/
theorem finitePresentation_stableUnderComposition : StableUnderComposition @FinitePresentation := by
  introv R hf hg
  exact hg.comp hf

/--
theorem `finitePresentation_respectsIso` / 定理 `finitePresentation_respectsIso`

English:
theorem finitePresentation_respectsIso
  statement: RingHom.RespectsIso @RingHom.FinitePresentation
  proof: finitePresentation_stableUnderComposition.respectsIso
fun e => .of_surjective _ e.surjective by simpa using! Submodule.fg_bot

中文:
定理 finitePresentation_respectsIso
  结论: 环态射.RespectsIso @环态射.有限呈现
  证明: finitePresentation_stableUnderComposition.respectsIso
fun e => .of_surjective _ e.surjective by simpa using! Submodule.fg_bot

Depends on / 依赖: Submodule, Submodule.fg_bot, e.surjective, fg_bot, finitePresentation_stableUnderComposition, finitePresentation_stableUnderComposition.respectsIso, of_surjective, respectsIso, surjective
-/
theorem finitePresentation_respectsIso : RingHom.RespectsIso @RingHom.FinitePresentation :=
  finitePresentation_stableUnderComposition.respectsIso
fun e => .of_surjective _ e.surjective by simpa using! Submodule.fg_bot

/--
theorem `finitePresentation_isStableUnderBaseChange` / 定理 `finitePresentation_isStableUnderBaseChange`

English:
theorem finitePresentation_isStableUnderBaseChange
  proof: by
  apply IsStableUnderBaseChange.mk
  · exact finitePresentation_respectsIso
  · simp only [finitePresentation_algebraMap]
    intros
    infer_instance

中文:
定理 finitePresentation_isStableUnderBaseChange
  证明: by
  apply IsStableUnderBaseChange.mk
  · exact finitePresentation_respectsIso
  · simp only [finitePresentation_algebraMap]
    intros
    infer_instance

Depends on / 依赖: IsStableUnderBaseChange, IsStableUnderBaseChange.mk, finitePresentation_algebraMap, finitePresentation_respectsIso, infer_instance, intros
-/
theorem finitePresentation_isStableUnderBaseChange :
    IsStableUnderBaseChange @FinitePresentation := by
  apply IsStableUnderBaseChange.mk
  · exact finitePresentation_respectsIso
  · simp only [finitePresentation_algebraMap]
    intros
    infer_instance

/--
theorem `finitePresentation_localizationPreserves` / 定理 `finitePresentation_localizationPreserves`

English:
theorem finitePresentation_localizationPreserves
  statement: LocalizationPreserves @FinitePresentation
  proof: finitePresentation_isStableUnderBaseChange.localizationPreserves

中文:
定理 finitePresentation_localizationPreserves
  结论: LocalizationPreserves @有限呈现
  证明: finitePresentation_isStableUnderBaseChange.localizationPreserves

Depends on / 依赖: finitePresentation_isStableUnderBaseChange, finitePresentation_isStableUnderBaseChange.localizationPreserves, localizationPreserves
-/
theorem finitePresentation_localizationPreserves : LocalizationPreserves @FinitePresentation :=
  finitePresentation_isStableUnderBaseChange.localizationPreserves

/--
theorem `finitePresentation_holdsForLocalizationAway` / 定理 `finitePresentation_holdsForLocalizationAway`

English:
theorem finitePresentation_holdsForLocalizationAway
  proof: by
  introv R _
  rw [finitePresentation_algebraMap]
  exact IsLocalization.Away.finitePresentation r

中文:
定理 finitePresentation_holdsForLocalizationAway
  证明: by
  introv R _
  rw [finitePresentation_algebraMap]
  exact IsLocalization.Away.finitePresentation r

Depends on / 依赖: IsLocalization, IsLocalization.Away.finitePresentation, finitePresentation, finitePresentation_algebraMap, introv
-/
theorem finitePresentation_holdsForLocalizationAway :
    HoldsForLocalizationAway @FinitePresentation := by
  introv R _
  rw [finitePresentation_algebraMap]
  exact IsLocalization.Away.finitePresentation r

/--
theorem `finitePresentation_ofLocalizationSpanTarget` / 定理 `finitePresentation_ofLocalizationSpanTarget`

English:
theorem finitePresentation_ofLocalizationSpanTarget
  proof: by
  introv R hs H
  algebraize [f]
  replace H : forall r in s, Algebra.FinitePresentation R (Localization.Away (r : S)) := by
    intro r hr; simp_rw [RingHom.FinitePresentation] at H; convert! H ⟨r, hr⟩; ext
    simp_rw [Algebra.smul_def]; rfl
  exact Algebra.FinitePresentation.of_span_eq_top_tar

中文:
定理 finitePresentation_ofLocalizationSpanTarget
  证明: by
  introv R hs H
  algebraize [f]
  replace H : forall r in s, Algebra.FinitePresentation R (Localization.Away (r : S)) := by
    intro r hr; simp_rw [RingHom.FinitePresentation] at H; convert! H ⟨r, hr⟩; ext
    simp_rw [Algebra.smul_def]; rfl
  exact Algebra.FinitePresentation.of_span_eq_top_tar

Depends on / 依赖: Algebra, Algebra.FinitePresentation, Algebra.FinitePresentation.of_span_eq_top_target, Algebra.smul_def, FinitePresentation, Localization, Localization.Away, RingHom, RingHom.FinitePresentation, algebraize, convert, introv, of_span_eq_top_target, replace, simp_rw, smul_def
-/
theorem finitePresentation_ofLocalizationSpanTarget :
    OfLocalizationSpanTarget @FinitePresentation := by
  introv R hs H
  algebraize [f]
  replace H : forall r in s, Algebra.FinitePresentation R (Localization.Away (r : S)) := by
    intro r hr; simp_rw [RingHom.FinitePresentation] at H; convert! H ⟨r, hr⟩; ext
    simp_rw [Algebra.smul_def]; rfl
  exact Algebra.FinitePresentation.of_span_eq_top_target s hs H

/--
theorem `finitePresentation_isLocal` / 定理 `finitePresentation_isLocal`

English:
theorem finitePresentation_isLocal
  statement: PropertyIsLocal @FinitePresentation
  proof: ⟨finitePresentation_localizationPreserves.away,
    finitePresentation_ofLocalizationSpanTarget,
    finitePresentation_ofLocalizationSpanTarget.ofLocalizationSpan
      (finitePresentation_stableUnderComposition.stableUnderCompositionWithLocalizationAway
        finitePresentation_holdsForLocalizat

中文:
定理 finitePresentation_isLocal
  结论: PropertyIsLocal @有限呈现
  证明: ⟨finitePresentation_localizationPreserves.away,
    finitePresentation_ofLocalizationSpanTarget,
    finitePresentation_ofLocalizationSpanTarget.ofLocalizationSpan
      (finitePresentation_stableUnderComposition.stableUnderCompositionWithLocalizationAway
        finitePresentation_holdsForLocalizat

Depends on / 依赖: finitePresentation_holdsForLocalizationAway, finitePresentation_localizationPreserves, finitePresentation_localizationPreserves.away, finitePresentation_ofLocalizationSpanTarget, finitePresentation_ofLocalizationSpanTarget.ofLocalizationSpan, finitePresentation_stableUnderComposition, finitePresentation_stableUnderComposition.stableUnderCompositionWithLocalizationAway, ofLocalizationSpan, stableUnderCompositionWithLocalizationAway
-/
theorem finitePresentation_isLocal : PropertyIsLocal @FinitePresentation :=
  ⟨finitePresentation_localizationPreserves.away,
    finitePresentation_ofLocalizationSpanTarget,
    finitePresentation_ofLocalizationSpanTarget.ofLocalizationSpan
      (finitePresentation_stableUnderComposition.stableUnderCompositionWithLocalizationAway
        finitePresentation_holdsForLocalizationAway).left,
    (finitePresentation_stableUnderComposition.stableUnderCompositionWithLocalizationAway
      finitePresentation_holdsForLocalizationAway).right⟩

end RingHom
