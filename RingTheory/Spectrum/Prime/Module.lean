/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.Support

/-!

# Subsets of prime spectra related to modules

## Main results

- `LocalizedModule.subsingleton_iff_disjoint` : `M[1/f] = 0 ↔ D(f) ∩ Supp M = 0`.
- `Module.isClosed_support` : If `M` is a finite `R`-module, then `Supp M` is closed.

## TODO
- If `M` is finitely presented, the complement of `Supp M` is quasi-compact. (stacks#051B)

-/

public section

variable {R A M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [CommRing A] [Algebra R A] [Module A M]

variable (R M) in
/--
lemma `IsLocalRing.closedPoint_mem_support` / 引理 `IsLocalRing.closedPoint_mem_support`

English:
lemma IsLocalRing.closedPoint_mem_support
  given: [IsLocalRing R] [Nontrivial M]
  proof: by
  obtain ⟨p, hp⟩ := (Module.nonempty_support_iff (R := R)).mpr ‹_›
  exact Module.mem_support_mono le_top hp

中文:
引理 是局部环.closedPoint_mem_support
  条件: [是局部环 R] [非平凡 M]
  证明: by
  obtain ⟨p, hp⟩ := (Module.nonempty_support_iff (R := R)).mpr ‹_›
  exact Module.mem_support_mono le_top hp

Depends on / 依赖: Module, Module.mem_support_mono, Module.nonempty_support_iff, le_top, mem_support_mono, nonempty_support_iff
-/
lemma IsLocalRing.closedPoint_mem_support [IsLocalRing R] [Nontrivial M] :
    IsLocalRing.closedPoint R in Module.support R M := by
  obtain ⟨p, hp⟩ := (Module.nonempty_support_iff (R := R)).mpr ‹_›
  exact Module.mem_support_mono le_top hp

/--
lemma `LocalizedModule.subsingleton_iff_disjoint` / 引理 `LocalizedModule.subsingleton_iff_disjoint`

English:
lemma LocalizedModule.subsingleton_iff_disjoint
  given: {f : R}
  proof: by
  rw [subsingleton_iff_support_subset]; rw [PrimeSpectrum.basicOpen_eq_zeroLocus_compl]; rw [disjoint_compl_left_iff]

中文:
引理 LocalizedModule.subsingleton_iff_disjoint
  条件: {f : R}
  证明: by
  rw [subsingleton_iff_support_subset]; rw [PrimeSpectrum.basicOpen_eq_zeroLocus_compl]; rw [disjoint_compl_left_iff]

Depends on / 依赖: PrimeSpectrum, PrimeSpectrum.basicOpen_eq_zeroLocus_compl, basicOpen_eq_zeroLocus_compl, disjoint_compl_left_iff, subsingleton_iff_support_subset
-/
lemma LocalizedModule.subsingleton_iff_disjoint {f : R} :
    Subsingleton (LocalizedModule.Away f M) ↔
      Disjoint ↑(PrimeSpectrum.basicOpen f) (Module.support R M) := by
  rw [subsingleton_iff_support_subset]; rw [PrimeSpectrum.basicOpen_eq_zeroLocus_compl]; rw [disjoint_compl_left_iff]

/--
lemma `Module.stableUnderSpecialization_support` / 引理 `Module.stableUnderSpecialization_support`

English:
lemma Module.stableUnderSpecialization_support
  statement: StableUnderSpecialization (Module.support R M)
  proof: fun x y e => mem_support_mono (PrimeSpectrum.le_iff_specializes x y).mpr e

中文:
引理 模.stableUnderSpecialization_support
  结论: StableUnderSpecialization (模.support R M)
  证明: fun x y e => mem_support_mono (PrimeSpectrum.le_iff_specializes x y).mpr e

Depends on / 依赖: PrimeSpectrum, PrimeSpectrum.le_iff_specializes, le_iff_specializes, mem_support_mono
-/
lemma Module.stableUnderSpecialization_support : StableUnderSpecialization (Module.support R M) :=
fun x y e => mem_support_mono (PrimeSpectrum.le_iff_specializes x y).mpr e

/--
lemma `Module.isClosed_support` / 引理 `Module.isClosed_support`

English:
lemma Module.isClosed_support
  given: [Module.Finite R M]
  proof: by
  rw [support_eq_zeroLocus]
  apply PrimeSpectrum.isClosed_zeroLocus

中文:
引理 模.isClosed_support
  条件: [模.有限 R M]
  证明: by
  rw [support_eq_zeroLocus]
  apply PrimeSpectrum.isClosed_zeroLocus

Depends on / 依赖: PrimeSpectrum, PrimeSpectrum.isClosed_zeroLocus, isClosed_zeroLocus, support_eq_zeroLocus
-/
lemma Module.isClosed_support [Module.Finite R M] :
    IsClosed (Module.support R M) := by
  rw [support_eq_zeroLocus]
  apply PrimeSpectrum.isClosed_zeroLocus

/--
lemma `Module.support_subset_preimage_comap` / 引理 `Module.support_subset_preimage_comap`

English:
lemma Module.support_subset_preimage_comap
  given: [IsScalarTower R A M]
  proof: by
  intro x hx
  simp only [Set.mem_preimage, mem_support_iff', PrimeSpectrum.comap_asIdeal, Ideal.mem_comap,
    ne_eq, not_imp_not] at hx ⊢
  obtain ⟨m, hm⟩ := hx
  exact ⟨m, fun r e => hm _ (by simpa)⟩

中文:
引理 模.support_subset_preimage_comap
  条件: [标量塔 R A M]
  证明: by
  intro x hx
  simp only [Set.mem_preimage, mem_support_iff', PrimeSpectrum.comap_asIdeal, Ideal.mem_comap,
    ne_eq, not_imp_not] at hx ⊢
  obtain ⟨m, hm⟩ := hx
  exact ⟨m, fun r e => hm _ (by simpa)⟩

Depends on / 依赖: Ideal.mem_comap, PrimeSpectrum, PrimeSpectrum.comap_asIdeal, Set.mem_preimage, comap_asIdeal, mem_comap, mem_preimage, mem_support_iff, ne_eq, not_imp_not
-/
lemma Module.support_subset_preimage_comap [IsScalarTower R A M] :
    Module.support A M subseteq PrimeSpectrum.comap (algebraMap R A) ⁻¹' Module.support R M := by
  intro x hx
  simp only [Set.mem_preimage, mem_support_iff', PrimeSpectrum.comap_asIdeal, Ideal.mem_comap,
    ne_eq, not_imp_not] at hx ⊢
  obtain ⟨m, hm⟩ := hx
  exact ⟨m, fun r e => hm _ (by simpa)⟩
