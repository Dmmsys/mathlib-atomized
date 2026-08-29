/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
public import Mathlib.CategoryTheory.Sites.LocallySurjective
/-!

# Preserving and reflecting local injectivity and surjectivity

This file proves that precomposition with a cocontinuous functor preserves local injectivity and
surjectivity of morphisms of presheaves, and that precomposition with a cover-preserving and
cover-dense functor reflects the same properties.
-/

public section

open CategoryTheory Functor

variable {C D A : Type*} [Category* C] [Category* D] [Category* A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (H : C ⥤ D) {F G : Dᵒᵖ ⥤ A} (f : F ⟶ G)

namespace CategoryTheory

namespace Presheaf

variable {FA : A -> A -> Type*} {CA : A -> Type*}
variable [forall X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]


/--
lemma `isLocallyInjective_whisker` / 引理 `isLocallyInjective_whisker`

English:
lemma isLocallyInjective_whisker
  given: [H.IsCocontinuous J K] [IsLocallyInjective K f]
  proof: H.cover_lift J K (equalizerSieve_mem K f x y h)

中文:
引理 isLocallyInjective_whisker
  条件: [H.是余continuous J K] [是LocallyInjective K f]
  证明: H.cover_lift J K (equalizerSieve_mem K f x y h)

Depends on / 依赖: H.cover_lift, cover_lift, equalizerSieve_mem
-/
lemma isLocallyInjective_whisker [H.IsCocontinuous J K] [IsLocallyInjective K f] :
    IsLocallyInjective J (whiskerLeft H.op f) where
  equalizerSieve_mem x y h := H.cover_lift J K (equalizerSieve_mem K f x y h)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `isLocallyInjective_of_whisker` / 引理 `isLocallyInjective_of_whisker`

English:
lemma isLocallyInjective_of_whisker
  statement: (hH : CoverPreserving J K H)
  proof: by
    apply K.transitive (H.is_cover_of_isCoverDense K X.unop)
    intro Y g ⟨⟨Z, lift, m, fac⟩⟩
    rw [← fac]; rw [Sieve.pullback_comp]
    apply K.pullback_stable
    refine K.superset_covering (Sieve.functorPullback_pushforward_le H _) ?_
    refine K.superset_covering (Sieve.functorPushforward

中文:
引理 isLocallyInjective_of_whisker
  结论: (hH : 余verPreserving J K H)
  证明: by
    apply K.transitive (H.is_cover_of_isCoverDense K X.unop)
    intro Y g ⟨⟨Z, lift, m, fac⟩⟩
    rw [← fac]; rw [Sieve.pullback_comp]
    apply K.pullback_stable
    refine K.superset_covering (Sieve.functorPullback_pushforward_le H _) ?_
    refine K.superset_covering (Sieve.functorPushforward

Depends on / 依赖: F.map, H.is_cover_of_isCoverDense, H.op, K.pullback_stable, K.superset_covering, K.transitive, NatTrans, Opposite, Opposite.op_unop, Sieve.functorPullback_pushforward_le, Sieve.functorPushforward_monotone, Sieve.pullback_comp, X.unop, comp_obj, cover_preserve, equalizerSieve_mem, functorPullback_pushforward_le, functorPushforward_monotone, hH.cover_preserve, is_cover_of_isCoverDense
-/
lemma isLocallyInjective_of_whisker (hH : CoverPreserving J K H)
    [H.IsCoverDense K] [IsLocallyInjective J (whiskerLeft H.op f)] : IsLocallyInjective K f where
  equalizerSieve_mem {X} a b h := by
    apply K.transitive (H.is_cover_of_isCoverDense K X.unop)
    intro Y g ⟨⟨Z, lift, m, fac⟩⟩
    rw [← fac]; rw [Sieve.pullback_comp]
    apply K.pullback_stable
    refine K.superset_covering (Sieve.functorPullback_pushforward_le H _) ?_
    refine K.superset_covering (Sieve.functorPushforward_monotone H _ ?_)
      (hH.cover_preserve <| equalizerSieve_mem J (whiskerLeft H.op f)
        (F.map m.op a) (F.map m.op b) ?_)
    · intro W q hq
      simpa using hq
    · simp only [comp_obj, op_obj, whiskerLeft_app, Opposite.op_unop]
      rw [NatTrans.naturality_apply]; rw [NatTrans.naturality_apply]; rw [h]

/--
lemma `isLocallyInjective_whisker_iff` / 引理 `isLocallyInjective_whisker_iff`

English:
lemma isLocallyInjective_whisker_iff
  statement: (hH : CoverPreserving J K H) [H.IsCocontinuous J K]
  proof: ⟨fun _ => isLocallyInjective_of_whisker J K H f hH,
    fun _ => isLocallyInjective_whisker J K H f⟩

中文:
引理 isLocallyInjective_whisker_iff
  结论: (hH : 余verPreserving J K H) [H.是余continuous J K]
  证明: ⟨fun _ => isLocallyInjective_of_whisker J K H f hH,
    fun _ => isLocallyInjective_whisker J K H f⟩

Depends on / 依赖: isLocallyInjective_of_whisker, isLocallyInjective_whisker
-/
lemma isLocallyInjective_whisker_iff (hH : CoverPreserving J K H) [H.IsCocontinuous J K]
    [H.IsCoverDense K] : IsLocallyInjective J (whiskerLeft H.op f) ↔ IsLocallyInjective K f :=
  ⟨fun _ => isLocallyInjective_of_whisker J K H f hH,
    fun _ => isLocallyInjective_whisker J K H f⟩

/--
lemma `isLocallySurjective_whisker` / 引理 `isLocallySurjective_whisker`

English:
lemma isLocallySurjective_whisker
  given: [H.IsCocontinuous J K] [IsLocallySurjective K f]
  proof: H.cover_lift J K (imageSieve_mem K f a)

中文:
引理 isLocallySurjective_whisker
  条件: [H.是余continuous J K] [是LocallySurjective K f]
  证明: H.cover_lift J K (imageSieve_mem K f a)

Depends on / 依赖: H.cover_lift, cover_lift, imageSieve_mem
-/
lemma isLocallySurjective_whisker [H.IsCocontinuous J K] [IsLocallySurjective K f] :
    IsLocallySurjective J (whiskerLeft H.op f) where
  imageSieve_mem a := H.cover_lift J K (imageSieve_mem K f a)

/--
lemma `isLocallySurjective_of_whisker` / 引理 `isLocallySurjective_of_whisker`

English:
lemma isLocallySurjective_of_whisker
  statement: (hH : CoverPreserving J K H)
  proof: by
    apply K.transitive (H.is_cover_of_isCoverDense K X)
    intro Y g ⟨⟨Z, lift, m, fac⟩⟩
    rw [← fac]; rw [Sieve.pullback_comp]
    apply K.pullback_stable
have hh := hH.cover_preserve imageSieve_mem J (whiskerLeft H.op f) (G.map m.op a)
    refine K.superset_covering (Sieve.functorPullback_pu

中文:
引理 isLocallySurjective_of_whisker
  结论: (hH : 余verPreserving J K H)
  证明: by
    apply K.transitive (H.is_cover_of_isCoverDense K X)
    intro Y g ⟨⟨Z, lift, m, fac⟩⟩
    rw [← fac]; rw [Sieve.pullback_comp]
    apply K.pullback_stable
have hh := hH.cover_preserve imageSieve_mem J (whiskerLeft H.op f) (G.map m.op a)
    refine K.superset_covering (Sieve.functorPullback_pu

Depends on / 依赖: G.map, H.is_cover_of_isCoverDense, H.op, K.pullback_stable, K.superset_covering, K.transitive, Presieve, Presieve.functorPullback_mem, Sieve.functorPullback_apply, Sieve.functorPullback_pushforward_le, Sieve.functorPushforward_monotone, Sieve.pullback_apply, Sieve.pullback_comp, cover_preserve, functorPullback_apply, functorPullback_mem, functorPullback_pushforward_le, functorPushforward_monotone, hH.cover_preserve, imageSieve_mem
-/
lemma isLocallySurjective_of_whisker (hH : CoverPreserving J K H)
    [H.IsCoverDense K] [IsLocallySurjective J (whiskerLeft H.op f)] : IsLocallySurjective K f where
  imageSieve_mem {X} a := by
    apply K.transitive (H.is_cover_of_isCoverDense K X)
    intro Y g ⟨⟨Z, lift, m, fac⟩⟩
    rw [← fac]; rw [Sieve.pullback_comp]
    apply K.pullback_stable
have hh := hH.cover_preserve imageSieve_mem J (whiskerLeft H.op f) (G.map m.op a)
    refine K.superset_covering (Sieve.functorPullback_pushforward_le H _) ?_
    refine K.superset_covering (Sieve.functorPushforward_monotone H _ ?_) hh
    intro W q ⟨x, h⟩
    simp only [Sieve.functorPullback_apply, Presieve.functorPullback_mem, Sieve.pullback_apply]
    exact ⟨x, by simpa using! h⟩

/--
lemma `isLocallySurjective_whisker_iff` / 引理 `isLocallySurjective_whisker_iff`

English:
lemma isLocallySurjective_whisker_iff
  statement: (hH : CoverPreserving J K H) [H.IsCocontinuous J K]
  proof: ⟨fun _ => isLocallySurjective_of_whisker J K H f hH,
    fun _ => isLocallySurjective_whisker J K H f⟩

中文:
引理 isLocallySurjective_whisker_iff
  结论: (hH : 余verPreserving J K H) [H.是余continuous J K]
  证明: ⟨fun _ => isLocallySurjective_of_whisker J K H f hH,
    fun _ => isLocallySurjective_whisker J K H f⟩

Depends on / 依赖: isLocallySurjective_of_whisker, isLocallySurjective_whisker
-/
lemma isLocallySurjective_whisker_iff (hH : CoverPreserving J K H) [H.IsCocontinuous J K]
    [H.IsCoverDense K] : IsLocallySurjective J (whiskerLeft H.op f) ↔ IsLocallySurjective K f :=
  ⟨fun _ => isLocallySurjective_of_whisker J K H f hH,
    fun _ => isLocallySurjective_whisker J K H f⟩

end Presheaf

end CategoryTheory
