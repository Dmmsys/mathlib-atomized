/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton
-/
module

public import Mathlib.Topology.Category.TopCat.Adjunctions
public import Mathlib.CategoryTheory.Functor.EpiMono

/-!
# Epi- and monomorphisms in `Top`

This file shows that a continuous function is an epimorphism in the category of topological spaces
if and only if it is surjective, and that a continuous function is a monomorphism in the category of
topological spaces if and only if it is injective.
-/

public section


universe u

open CategoryTheory

open TopCat

namespace TopCat

/--
theorem `epi_iff_surjective` / 定理 `epi_iff_surjective`

English:
theorem epi_iff_surjective
  given: {X Y : TopCat.{u}} (f : X ⟶ Y)
  statement: Epi f ↔ Function.Surjective f
  proof: by
  suffices Epi f ↔ Epi ((forget TopCat).map f) by
    rw [this]; rw [CategoryTheory.ofHom_epi_iff_surjective]
  constructor
  · intro
    apply Functor.map_epi -- was `infer_instance`
  · apply Functor.epi_of_epi_map

中文:
定理 epi_iff_surjective
  条件: {X Y : TopCat.{u}} (f : X ⟶ Y)
  结论: Epi f ↔ Function.Surjective f
  证明: by
  suffices Epi f ↔ Epi ((forget TopCat).map f) by
    rw [this]; rw [CategoryTheory.ofHom_epi_iff_surjective]
  constructor
  · intro
    apply Functor.map_epi -- was `infer_instance`
  · apply Functor.epi_of_epi_map

Depends on / 依赖: CategoryTheory, CategoryTheory.ofHom_epi_iff_surjective, Functor, Functor.epi_of_epi_map, Functor.map_epi, TopCat, epi_of_epi_map, forget, infer_instance, map_epi, ofHom_epi_iff_surjective
-/
theorem epi_iff_surjective {X Y : TopCat.{u}} (f : X ⟶ Y) : Epi f ↔ Function.Surjective f := by
  suffices Epi f ↔ Epi ((forget TopCat).map f) by
    rw [this]; rw [CategoryTheory.ofHom_epi_iff_surjective]
  constructor
  · intro
    apply Functor.map_epi -- was `infer_instance`
  · apply Functor.epi_of_epi_map

/--
theorem `mono_iff_injective` / 定理 `mono_iff_injective`

English:
theorem mono_iff_injective
  given: {X Y : TopCat.{u}} (f : X ⟶ Y)
  statement: Mono f ↔ Function.Injective f
  proof: by
  suffices Mono f ↔ Mono ((forget TopCat).map f) by
    rw [this]; rw [CategoryTheory.mono_iff_injective]
    rfl
  constructor
  · intro
    apply Functor.map_mono -- was `infer_instance`
  · apply Functor.mono_of_mono_map

中文:
定理 mono_iff_injective
  条件: {X Y : TopCat.{u}} (f : X ⟶ Y)
  结论: Mono f ↔ Function.Injective f
  证明: by
  suffices Mono f ↔ Mono ((forget TopCat).map f) by
    rw [this]; rw [CategoryTheory.mono_iff_injective]
    rfl
  constructor
  · intro
    apply Functor.map_mono -- was `infer_instance`
  · apply Functor.mono_of_mono_map

Depends on / 依赖: CategoryTheory, CategoryTheory.mono_iff_injective, Functor, Functor.map_mono, Functor.mono_of_mono_map, TopCat, forget, infer_instance, map_mono, mono_iff_injective, mono_of_mono_map
-/
theorem mono_iff_injective {X Y : TopCat.{u}} (f : X ⟶ Y) : Mono f ↔ Function.Injective f := by
  suffices Mono f ↔ Mono ((forget TopCat).map f) by
    rw [this]; rw [CategoryTheory.mono_iff_injective]
    rfl
  constructor
  · intro
    apply Functor.map_mono -- was `infer_instance`
  · apply Functor.mono_of_mono_map

end TopCat
