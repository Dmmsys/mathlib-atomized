/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau, Edison Xie
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Exact

/-! # Short Exact Sequences in Abelian Categories

This file contains lemmas about short exact sequences in abelian categories.

-/

public section

namespace CategoryTheory.ShortExact

universe v₁ v₂ u₁ u₂

open CategoryTheory Limits Preadditive CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
variable {D : Type u₂} [Category.{v₂} D] [Abelian D]
variable (F : C ⥤ D) [PreservesZeroMorphisms F] [F.Faithful]
variable {S : ShortComplex C}

/--
lemma `reflects_shortExact_of_faithful` / 引理 `reflects_shortExact_of_faithful`

English:
lemma reflects_shortExact_of_faithful
  given: (hS : (S.map F).ShortExact)
  statement: S.ShortExact where
  proof: F.reflects_exact_of_faithful _ hS.1
  mono_f := ReflectsMonomorphisms.reflects _ hS.mono_f
  epi_g := ReflectsEpimorphisms.reflects _ hS.epi_g

中文:
引理 reflects_shortExact_of_faithful
  条件: (hS : (S.map F).ShortExact)
  结论: S.ShortExact where
  证明: F.reflects_exact_of_faithful _ hS.1
  mono_f := ReflectsMonomorphisms.reflects _ hS.mono_f
  epi_g := ReflectsEpimorphisms.reflects _ hS.epi_g

Depends on / 依赖: F.reflects_exact_of_faithful, reflects_exact_of_faithful
-/
lemma reflects_shortExact_of_faithful (hS : (S.map F).ShortExact) : S.ShortExact where
  exact := F.reflects_exact_of_faithful _ hS.1
  mono_f := ReflectsMonomorphisms.reflects _ hS.mono_f
  epi_g := ReflectsEpimorphisms.reflects _ hS.epi_g

/--
lemma `shortExact_map_iff` / 引理 `shortExact_map_iff`

English:
lemma shortExact_map_iff
  given: [PreservesFiniteColimits F] [PreservesFiniteLimits F]
  proof: ⟨reflects_shortExact_of_faithful F, fun h => ShortComplex.ShortExact.map_of_exact h F⟩

中文:
引理 shortExact_map_iff
  条件: [PreservesFiniteColimits F] [PreservesFiniteLimits F]
  证明: ⟨reflects_shortExact_of_faithful F, fun h => ShortComplex.ShortExact.map_of_exact h F⟩

Depends on / 依赖: ShortComplex, ShortComplex.ShortExact.map_of_exact, ShortExact, map_of_exact, reflects_shortExact_of_faithful
-/
lemma shortExact_map_iff [PreservesFiniteColimits F] [PreservesFiniteLimits F] :
    (S.map F).ShortExact ↔ S.ShortExact :=
  ⟨reflects_shortExact_of_faithful F, fun h => ShortComplex.ShortExact.map_of_exact h F⟩

end CategoryTheory.ShortExact
