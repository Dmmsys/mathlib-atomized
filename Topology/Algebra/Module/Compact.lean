/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.RingTheory.Noetherian.Defs

/-!

# Compact submodules

-/

public section

variable {R M : Type*} [CommSemiring R] [TopologicalSpace R] [AddCommMonoid M] [Module R M]
variable [TopologicalSpace M] [ContinuousAdd M] [ContinuousSMul R M]

/--
lemma `Submodule.isCompact_of_fg` / 引理 `Submodule.isCompact_of_fg`

English:
lemma Submodule.isCompact_of_fg
  given: [CompactSpace R] {N : Submodule R M} (hN : N.FG)
  proof: by
  obtain ⟨s, hs⟩ := hN
  have : LinearMap.range (Fintype.linearCombination R (α := s) Subtype.val) = N := by
    simp [hs]
  rw [← this]
  refine isCompact_range ?_
  simp only [Fintype.linearCombination, Finset.univ_eq_attach, LinearMap.coe_mk,
    AddHom.coe_mk]
  fun_prop

中文:
引理 Submodule.isCompact_of_fg
  条件: [CompactSpace R] {N : Submodule R M} (hN : N.FG)
  证明: by
  obtain ⟨s, hs⟩ := hN
  have : LinearMap.range (Fintype.linearCombination R (α := s) Subtype.val) = N := by
    simp [hs]
  rw [← this]
  refine isCompact_range ?_
  simp only [Fintype.linearCombination, Finset.univ_eq_attach, LinearMap.coe_mk,
    AddHom.coe_mk]
  fun_prop

Depends on / 依赖: AddHom, AddHom.coe_mk, Finset, Finset.univ_eq_attach, Fintype, Fintype.linearCombination, LinearMap, LinearMap.coe_mk, LinearMap.range, Subtype, Subtype.val, coe_mk, fun_prop, isCompact_range, linearCombination, univ_eq_attach
-/
lemma Submodule.isCompact_of_fg [CompactSpace R] {N : Submodule R M} (hN : N.FG) :
    IsCompact (X := M) N := by
  obtain ⟨s, hs⟩ := hN
  have : LinearMap.range (Fintype.linearCombination R (α := s) Subtype.val) = N := by
    simp [hs]
  rw [← this]
  refine isCompact_range ?_
  simp only [Fintype.linearCombination, Finset.univ_eq_attach, LinearMap.coe_mk,
    AddHom.coe_mk]
  fun_prop

/--
lemma `Ideal.isCompact_of_fg` / 引理 `Ideal.isCompact_of_fg`

English:
lemma Ideal.isCompact_of_fg
  statement: [IsTopologicalSemiring R] [CompactSpace R]
  proof: Submodule.isCompact_of_fg hI

中文:
引理 Ideal.isCompact_of_fg
  结论: [IsTopologicalSemiring R] [CompactSpace R]
  证明: Submodule.isCompact_of_fg hI
-/
lemma Ideal.isCompact_of_fg [IsTopologicalSemiring R] [CompactSpace R]
    {I : Ideal R} (hI : I.FG) : IsCompact (X := R) I :=
  Submodule.isCompact_of_fg hI

variable (R M) in
/--
lemma `Module.Finite.compactSpace` / 引理 `Module.Finite.compactSpace`

English:
lemma Module.Finite.compactSpace
  given: [CompactSpace R] [Module.Finite R M]
  statement: CompactSpace M
  proof: ⟨Submodule.isCompact_of_fg (Module.Finite.fg_top (R := R))⟩

中文:
引理 Module.Finite.compactSpace
  条件: [CompactSpace R] [Module.Finite R M]
  结论: CompactSpace M
  证明: ⟨Submodule.isCompact_of_fg (Module.Finite.fg_top (R := R))⟩

Depends on / 依赖: Finite, Module, Module.Finite.fg_top, Submodule, Submodule.isCompact_of_fg, fg_top, isCompact_of_fg
-/
lemma Module.Finite.compactSpace [CompactSpace R] [Module.Finite R M] : CompactSpace M :=
  ⟨Submodule.isCompact_of_fg (Module.Finite.fg_top (R := R))⟩

instance (priority := low) IsNoetherianRing.isClosed_ideal
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsNoetherianRing R] [CompactSpace R] [T2Space R] (I : Ideal R) :
    IsClosed (X := R) I :=
  (Ideal.isCompact_of_fg (IsNoetherian.noetherian I)).isClosed
