/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.Support

/-!
# Smooth locus of an algebra

Most results in this file are proved for algebras of finite presentations.
Some of them are true for arbitrary algebras but the proof is substantially harder.

## Main results
- `Algebra.smoothLocus` : The set of primes that are smooth over the base.
- `Algebra.basicOpen_subset_smoothLocus_iff` :
  `D(f)` is contained in the smooth locus if and only if `A_f` is smooth over `R`.
- `Algebra.smoothLocus_eq_univ_iff` :
  The smooth locus is the whole spectrum if and only if `A` is smooth over `R`.
- `Algebra.isOpen_smoothLocus` : The smooth locus is open.
-/

@[expose] public section

universe u

variable (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]

namespace Algebra

variable {A} in
/--
An `R`-algebra `A` is smooth at a prime `p` of `A` if `Aₚ` is formally smooth over `R`.

This does not imply `Aₚ` is smooth over `R` under the mathlib definition
even if `A` is finitely presented,
but it can be shown that this is equivalent to the stacks project definition that `A` is smooth
at `p` if and only if there exists `f ∉ p` such that `A_f` is smooth over `R`.
See `Algebra.basicOpen_subset_smoothLocus_iff_smooth` and `Algebra.isOpen_smoothLocus`.
-/
@[stacks 00TB]
/--
Definition of `IsSmoothAt` / `IsSmoothAt` 的定义

English:
abbreviation IsSmoothAt
  signature: (p : Ideal A) [p.IsPrime]
  body: Algebra.FormallySmooth R (Localization.AtPrime p)

中文:
缩写 IsSmoothAt
  签名: (p : 理想 A) [p.是素]
  定义体: Algebra.FormallySmooth R (Localization.AtPrime p)

Depends on / 依赖: Algebra, Algebra.FormallySmooth, AtPrime, FormallySmooth, Localization, Localization.AtPrime
-/
abbrev IsSmoothAt (p : Ideal A) [p.IsPrime] : Prop :=
  Algebra.FormallySmooth R (Localization.AtPrime p)

/--
Definition of `smoothLocus` / `smoothLocus` 的定义

English:
definition smoothLocus
  signature: : Set (PrimeSpectrum A)
  body: { p | IsSmoothAt R p.asIdeal }

中文:
定义 smoothLocus
  签名: : 集合 (素谱 A)
  定义体: { p | IsSmoothAt R p.asIdeal }

Depends on / 依赖: IsSmoothAt, asIdeal, p.asIdeal
-/
def smoothLocus : Set (PrimeSpectrum A) := { p | IsSmoothAt R p.asIdeal }

variable {R A}

attribute [local instance] Module.finitePresentation_of_projective in
/--
lemma `smoothLocus_eq_compl_support_inter` / 引理 `smoothLocus_eq_compl_support_inter`

English:
lemma smoothLocus_eq_compl_support_inter
  given: [EssFiniteType R A]
  proof: by
  ext p
  simp only [Set.mem_inter_iff, Set.mem_compl_iff, Module.notMem_support_iff,
    Module.mem_freeLocus]
  refine (Algebra.formallySmooth_iff _ _).trans (and_comm.trans ?_)
  congr! 1
  · have := IsLocalizedModule.iso p.asIdeal.primeCompl
      (H1Cotangent.map R R A (Localization.AtPrime p.asIdeal))
    exact this.subsingleton_congr.symm
  · trans Module.Free (Localization.AtPrime p.asIdeal) Ω[Localization.AtPrime p.asIdeal⁄R]
    · have : EssFiniteType A (Localization.AtPrime p.asIdeal) :=
        .of_isLocalization _ p.asIdeal.primeCompl
      have : EssFiniteType R (Localization.AtPrime p.asIdeal) := .comp _ A _
      exact ⟨fun _ => Module.free_of_flat_of_isLocalRing, fun _ => inferInstance⟩
    · have := IsLocalizedModule.iso p.asIdeal.primeCompl
        (KaehlerDifferential.map R R A (Localization.AtPrime p.asIdeal))
      have := this.extendScalarsOfIsLocalization
        p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal)
      exact ⟨fun H => H.of_equiv' this.symm, fun H => H.of_equiv' this⟩

中文:
引理 smoothLocus_eq_compl_support_inter
  条件: [EssFiniteType R A]
  证明: by
  ext p
  simp only [Set.mem_inter_iff, Set.mem_compl_iff, Module.notMem_support_iff,
    Module.mem_freeLocus]
  refine (Algebra.formallySmooth_iff _ _).trans (and_comm.trans ?_)
  congr! 1
  · have := IsLocalizedModule.iso p.asIdeal.primeCompl
      (H1Cotangent.map R R A (Localization.AtPrime p.asIdeal))
    exact this.subsingleton_congr.symm
  · trans Module.Free (Localization.AtPrime p.asIdeal) Ω[Localization.AtPrime p.asIdeal⁄R]
    · have : EssFiniteType A (Localization.AtPrime p.asIdeal) :=
        .of_isLocalization _ p.asIdeal.primeCompl
      have : EssFiniteType R (Localization.AtPrime p.asIdeal) := .comp _ A _
      exact ⟨fun _ => Module.free_of_flat_of_isLocalRing, fun _ => inferInstance⟩
    · have := IsLocalizedModule.iso p.asIdeal.primeCompl
        (KaehlerDifferential.map R R A (Localization.AtPrime p.asIdeal))
      have := this.extendScalarsOfIsLocalization
        p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal)
      exact ⟨fun H => H.of_equiv' this.symm, fun H => H.of_equiv' this⟩

Depends on / 依赖: Algebra, Algebra.formallySmooth_iff, AtPrime, EssFiniteType, H1Cotangent, H1Cotangent.map, IsLocalizedModule, IsLocalizedModule.iso, Localization, Localization.AtPrime, Module, Module.Free, Module.mem_freeLocus, Module.notMem_support_iff, Set.mem_compl_iff, Set.mem_inter_iff, and_comm, and_comm.trans, asIdeal, formallySmooth_iff
-/
lemma smoothLocus_eq_compl_support_inter [EssFiniteType R A] :
    smoothLocus R A = (Module.support A (H1Cotangent R A))ᶜ inter Module.freeLocus A Ω[A⁄R] := by
  ext p
  simp only [Set.mem_inter_iff, Set.mem_compl_iff, Module.notMem_support_iff,
    Module.mem_freeLocus]
  refine (Algebra.formallySmooth_iff _ _).trans (and_comm.trans ?_)
  congr! 1
  · have := IsLocalizedModule.iso p.asIdeal.primeCompl
      (H1Cotangent.map R R A (Localization.AtPrime p.asIdeal))
    exact this.subsingleton_congr.symm
  · trans Module.Free (Localization.AtPrime p.asIdeal) Ω[Localization.AtPrime p.asIdeal⁄R]
    · have : EssFiniteType A (Localization.AtPrime p.asIdeal) :=
        .of_isLocalization _ p.asIdeal.primeCompl
      have : EssFiniteType R (Localization.AtPrime p.asIdeal) := .comp _ A _
      exact ⟨fun _ => Module.free_of_flat_of_isLocalRing, fun _ => inferInstance⟩
    · have := IsLocalizedModule.iso p.asIdeal.primeCompl
        (KaehlerDifferential.map R R A (Localization.AtPrime p.asIdeal))
      have := this.extendScalarsOfIsLocalization
        p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal)
      exact ⟨fun H => H.of_equiv' this.symm, fun H => H.of_equiv' this⟩

/--
lemma `basicOpen_subset_smoothLocus_iff` / 引理 `basicOpen_subset_smoothLocus_iff`

English:
lemma basicOpen_subset_smoothLocus_iff
  given: [FinitePresentation R A] {f : A}
  proof: by
  rw [smoothLocus_eq_compl_support_inter]; rw [Set.subset_inter_iff]; rw [Set.subset_compl_comm]; rw [PrimeSpectrum.basicOpen_eq_zeroLocus_compl]; rw [compl_compl]; rw [← LocalizedModule.subsingleton_iff_support_subset]; rw [Algebra.formallySmooth_iff]; rw [iff_comm]; rw [and_comm]
  congr! 1
  · have := IsLocalizedModule.iso (.powers f) (H1Cotangent.map R R A (Localization.Away f))
    rw [this.subsingleton_congr]
  · rw [← PrimeSpectrum.basicOpen_eq_zeroLocus_compl, Module.basicOpen_subset_freeLocus_iff]
    have := IsLocalizedModule.iso (.powers f)
        (KaehlerDifferential.map R R A (Localization.Away f))
    have := this.extendScalarsOfIsLocalization (.powers f) (Localization.Away f)
    exact ⟨fun _ => .of_equiv this.symm, fun _ => .of_equiv this⟩

中文:
引理 basicOpen_subset_smoothLocus_iff
  条件: [有限呈现 R A] {f : A}
  证明: by
  rw [smoothLocus_eq_compl_support_inter]; rw [Set.subset_inter_iff]; rw [Set.subset_compl_comm]; rw [PrimeSpectrum.basicOpen_eq_zeroLocus_compl]; rw [compl_compl]; rw [← LocalizedModule.subsingleton_iff_support_subset]; rw [Algebra.formallySmooth_iff]; rw [iff_comm]; rw [and_comm]
  congr! 1
  · have := IsLocalizedModule.iso (.powers f) (H1Cotangent.map R R A (Localization.Away f))
    rw [this.subsingleton_congr]
  · rw [← PrimeSpectrum.basicOpen_eq_zeroLocus_compl, Module.basicOpen_subset_freeLocus_iff]
    have := IsLocalizedModule.iso (.powers f)
        (KaehlerDifferential.map R R A (Localization.Away f))
    have := this.extendScalarsOfIsLocalization (.powers f) (Localization.Away f)
    exact ⟨fun _ => .of_equiv this.symm, fun _ => .of_equiv this⟩

Depends on / 依赖: Algebra, Algebra.formallySmooth_iff, H1Cotangent, H1Cotangent.map, IsLocalizedModule, IsLocalizedModule.iso, Localization, Localization.Away, LocalizedModule, LocalizedModule.subsingleton_iff_support_subset, Module, Module.basicOpen_subset_freeLocus_if, PrimeSpectrum, PrimeSpectrum.basicOpen_eq_zeroLocus_compl, Set.subset_compl_comm, Set.subset_inter_iff, and_comm, basicOpen_eq_zeroLocus_compl, basicOpen_subset_freeLocus_if, compl_compl
-/
lemma basicOpen_subset_smoothLocus_iff [FinitePresentation R A] {f : A} :
    ↑(PrimeSpectrum.basicOpen f) subseteq smoothLocus R A ↔
      Algebra.FormallySmooth R (Localization.Away f) := by
  rw [smoothLocus_eq_compl_support_inter]; rw [Set.subset_inter_iff]; rw [Set.subset_compl_comm]; rw [PrimeSpectrum.basicOpen_eq_zeroLocus_compl]; rw [compl_compl]; rw [← LocalizedModule.subsingleton_iff_support_subset]; rw [Algebra.formallySmooth_iff]; rw [iff_comm]; rw [and_comm]
  congr! 1
  · have := IsLocalizedModule.iso (.powers f) (H1Cotangent.map R R A (Localization.Away f))
    rw [this.subsingleton_congr]
  · rw [← PrimeSpectrum.basicOpen_eq_zeroLocus_compl, Module.basicOpen_subset_freeLocus_iff]
    have := IsLocalizedModule.iso (.powers f)
        (KaehlerDifferential.map R R A (Localization.Away f))
    have := this.extendScalarsOfIsLocalization (.powers f) (Localization.Away f)
    exact ⟨fun _ => .of_equiv this.symm, fun _ => .of_equiv this⟩

/--
lemma `basicOpen_subset_smoothLocus_iff_smooth` / 引理 `basicOpen_subset_smoothLocus_iff_smooth`

English:
lemma basicOpen_subset_smoothLocus_iff_smooth
  given: [FinitePresentation R A] {f : A}
  proof: by
  have : FinitePresentation A (Localization.Away f) := IsLocalization.Away.finitePresentation f
  rw [basicOpen_subset_smoothLocus_iff]
  exact ⟨fun H => ⟨H, .trans _ A _⟩, fun H => H.1⟩

中文:
引理 basicOpen_subset_smoothLocus_iff_smooth
  条件: [有限呈现 R A] {f : A}
  证明: by
  have : FinitePresentation A (Localization.Away f) := IsLocalization.Away.finitePresentation f
  rw [basicOpen_subset_smoothLocus_iff]
  exact ⟨fun H => ⟨H, .trans _ A _⟩, fun H => H.1⟩

Depends on / 依赖: FinitePresentation, IsLocalization, IsLocalization.Away.finitePresentation, Localization, Localization.Away, basicOpen_subset_smoothLocus_iff, finitePresentation
-/
lemma basicOpen_subset_smoothLocus_iff_smooth [FinitePresentation R A] {f : A} :
    ↑(PrimeSpectrum.basicOpen f) subseteq smoothLocus R A ↔
      Algebra.Smooth R (Localization.Away f) := by
  have : FinitePresentation A (Localization.Away f) := IsLocalization.Away.finitePresentation f
  rw [basicOpen_subset_smoothLocus_iff]
  exact ⟨fun H => ⟨H, .trans _ A _⟩, fun H => H.1⟩

/--
lemma `smoothLocus_eq_univ_iff` / 引理 `smoothLocus_eq_univ_iff`

English:
lemma smoothLocus_eq_univ_iff
  given: [FinitePresentation R A]
  proof: by
  have := IsLocalization.atUnits A (.powers 1) (S := Localization.Away (1 : A)) (by simp)
  rw [Algebra.FormallySmooth.iff_of_equiv (this.restrictScalars R)]; rw [← basicOpen_subset_smoothLocus_iff]
  simp

中文:
引理 smoothLocus_eq_univ_iff
  条件: [有限呈现 R A]
  证明: by
  have := IsLocalization.atUnits A (.powers 1) (S := Localization.Away (1 : A)) (by simp)
  rw [Algebra.FormallySmooth.iff_of_equiv (this.restrictScalars R)]; rw [← basicOpen_subset_smoothLocus_iff]
  simp

Depends on / 依赖: Algebra, Algebra.FormallySmooth.iff_of_equiv, FormallySmooth, IsLocalization, IsLocalization.atUnits, Localization, Localization.Away, atUnits, basicOpen_subset_smoothLocus_iff, iff_of_equiv, powers, restrictScalars, this.restrictScalars
-/
lemma smoothLocus_eq_univ_iff [FinitePresentation R A] :
    smoothLocus R A = Set.univ ↔ Algebra.FormallySmooth R A := by
  have := IsLocalization.atUnits A (.powers 1) (S := Localization.Away (1 : A)) (by simp)
  rw [Algebra.FormallySmooth.iff_of_equiv (this.restrictScalars R)]; rw [← basicOpen_subset_smoothLocus_iff]
  simp

/--
lemma `smoothLocus_eq_univ` / 引理 `smoothLocus_eq_univ`

English:
lemma smoothLocus_eq_univ
  given: [Smooth R A]
  statement: smoothLocus R A = Set.univ
  proof: by
  rw [smoothLocus_eq_univ_iff]
  infer_instance

中文:
引理 smoothLocus_eq_univ
  条件: [光滑 R A]
  结论: smoothLocus R A = 集合.univ
  证明: by
  rw [smoothLocus_eq_univ_iff]
  infer_instance

Depends on / 依赖: infer_instance, smoothLocus_eq_univ_iff
-/
lemma smoothLocus_eq_univ [Smooth R A] : smoothLocus R A = Set.univ := by
  rw [smoothLocus_eq_univ_iff]
  infer_instance

/--
lemma `smoothLocus_comap_of_isLocalization` / 引理 `smoothLocus_comap_of_isLocalization`

English:
lemma smoothLocus_comap_of_isLocalization
  statement: {Af : Type*} [CommRing Af] [Algebra A Af] [Algebra R Af]
  proof: by
  ext p
  let q := PrimeSpectrum.comap (algebraMap A Af) p
  have : IsLocalization.AtPrime (Localization.AtPrime p.asIdeal) q.asIdeal :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization (.powers f) _ p.asIdeal
  refine Algebra.FormallySmooth.iff_of_equiv ?_
  exact (IsLocalization.algEquiv q.asIdeal.primeCompl _ _).restrictScalars R

中文:
引理 smoothLocus_comap_of_isLocalization
  结论: {Af : 类型} [交换环 Af] [代数 A Af] [代数 R Af]
  证明: by
  ext p
  let q := PrimeSpectrum.comap (algebraMap A Af) p
  have : IsLocalization.AtPrime (Localization.AtPrime p.asIdeal) q.asIdeal :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization (.powers f) _ p.asIdeal
  refine Algebra.FormallySmooth.iff_of_equiv ?_
  exact (IsLocalization.algEquiv q.asIdeal.primeCompl _ _).restrictScalars R

Depends on / 依赖: Algebra, Algebra.FormallySmooth.iff_of_equiv, AtPrime, FormallySmooth, IsLocalization, IsLocalization.AtPrime, IsLocalization.algEquiv, IsLocalization.isLocalization_isLocalization_atPrime_isLocalization, Localization, Localization.AtPrime, PrimeSpectrum, PrimeSpectrum.comap, algEquiv, algebraMap, asIdeal, iff_of_equiv, isLocalization_isLocalization_atPrime_isLocalization, p.asIdeal, powers, primeCompl
-/
lemma smoothLocus_comap_of_isLocalization {Af : Type*} [CommRing Af] [Algebra A Af] [Algebra R Af]
    [IsScalarTower R A Af] (f : A) [IsLocalization.Away f Af] :
    PrimeSpectrum.comap (algebraMap A Af) ⁻¹' smoothLocus R A = smoothLocus R Af := by
  ext p
  let q := PrimeSpectrum.comap (algebraMap A Af) p
  have : IsLocalization.AtPrime (Localization.AtPrime p.asIdeal) q.asIdeal :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization (.powers f) _ p.asIdeal
  refine Algebra.FormallySmooth.iff_of_equiv ?_
  exact (IsLocalization.algEquiv q.asIdeal.primeCompl _ _).restrictScalars R

-- Note that this does not follow directly from `smoothLocus_eq_compl_support_inter` because
-- `H¹(L_{S/R})` is not necessarily finitely generated.
open PrimeSpectrum in
/--
lemma `isOpen_smoothLocus` / 引理 `isOpen_smoothLocus`

English:
lemma isOpen_smoothLocus
  given: [FinitePresentation R A]
  statement: IsOpen (smoothLocus R A)
  proof: by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩, hxf, hf⟩ :=
    isBasis_basic_opens.exists_subset_of_mem_open
    (smoothLocus_eq_compl_support_inter.le hx).2 Module.isOpen_freeLocus
  rw [Module.basicOpen_subset_freeLocus_iff] at hf
  let Af := Localization.Away f
  have : Algebra.FinitePresentation A (Localization.Away f) :=
    IsLocalization.Away.finitePresentation f
  have : Algebra.FinitePresentation R (Localization.Away f) :=
    .trans _ A _
  have : IsOpen (smoothLocus R Af) := by
    have := IsLocalizedModule.iso (.powers f)
      (KaehlerDifferential.map R R A (Localization.Away f))
    have := this.extendScalarsOfIsLocalization (.powers f) (Localization.Away f)
    have := Module.Projective.of_equiv this
    rw [smoothLocus_eq_compl_support_inter]; rw [Module.support_eq_zeroLocus]
    exact (isClosed_zeroLocus _).isOpen_compl.inter Module.isOpen_freeLocus
  rw [← smoothLocus_comap_of_isLocalization f] at this
  replace this := (PrimeSpectrum.localization_away_isOpenEmbedding Af f).isOpenMap _ this
  rw [Set.image_preimage_eq_inter_range]; rw [localization_away_comap_range Af f] at this
  exact ⟨_, Set.inter_subset_left, this, hx, hxf⟩

中文:
引理 isOpen_smoothLocus
  条件: [有限呈现 R A]
  结论: 是开集 (smoothLocus R A)
  证明: by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩, hxf, hf⟩ :=
    isBasis_basic_opens.exists_subset_of_mem_open
    (smoothLocus_eq_compl_support_inter.le hx).2 Module.isOpen_freeLocus
  rw [Module.basicOpen_subset_freeLocus_iff] at hf
  let Af := Localization.Away f
  have : Algebra.FinitePresentation A (Localization.Away f) :=
    IsLocalization.Away.finitePresentation f
  have : Algebra.FinitePresentation R (Localization.Away f) :=
    .trans _ A _
  have : IsOpen (smoothLocus R Af) := by
    have := IsLocalizedModule.iso (.powers f)
      (KaehlerDifferential.map R R A (Localization.Away f))
    have := this.extendScalarsOfIsLocalization (.powers f) (Localization.Away f)
    have := Module.Projective.of_equiv this
    rw [smoothLocus_eq_compl_support_inter]; rw [Module.support_eq_zeroLocus]
    exact (isClosed_zeroLocus _).isOpen_compl.inter Module.isOpen_freeLocus
  rw [← smoothLocus_comap_of_isLocalization f] at this
  replace this := (PrimeSpectrum.localization_away_isOpenEmbedding Af f).isOpenMap _ this
  rw [Set.image_preimage_eq_inter_range]; rw [localization_away_comap_range Af f] at this
  exact ⟨_, Set.inter_subset_left, this, hx, hxf⟩

Depends on / 依赖: Algebra, Algebra.FinitePresentation, FinitePresentation, IsLocalization, IsLocalization.Away.finitePresentation, IsOpen, Localization, Localization.Away, Module, Module.basicOpen_subset_freeLocus_iff, Module.isOpen_freeLocus, basicOpen_subset_freeLocus_iff, exists_subset_of_mem_open, finitePresentation, isBasis_basic_opens, isBasis_basic_opens.exists_subset_of_mem_open, isOpen_freeLocus, isOpen_iff_forall_mem_open, smoothLocus, smoothLocus_eq_compl_support_inter
-/
lemma isOpen_smoothLocus [FinitePresentation R A] : IsOpen (smoothLocus R A) := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩, hxf, hf⟩ :=
    isBasis_basic_opens.exists_subset_of_mem_open
    (smoothLocus_eq_compl_support_inter.le hx).2 Module.isOpen_freeLocus
  rw [Module.basicOpen_subset_freeLocus_iff] at hf
  let Af := Localization.Away f
  have : Algebra.FinitePresentation A (Localization.Away f) :=
    IsLocalization.Away.finitePresentation f
  have : Algebra.FinitePresentation R (Localization.Away f) :=
    .trans _ A _
  have : IsOpen (smoothLocus R Af) := by
    have := IsLocalizedModule.iso (.powers f)
      (KaehlerDifferential.map R R A (Localization.Away f))
    have := this.extendScalarsOfIsLocalization (.powers f) (Localization.Away f)
    have := Module.Projective.of_equiv this
    rw [smoothLocus_eq_compl_support_inter]; rw [Module.support_eq_zeroLocus]
    exact (isClosed_zeroLocus _).isOpen_compl.inter Module.isOpen_freeLocus
  rw [← smoothLocus_comap_of_isLocalization f] at this
  replace this := (PrimeSpectrum.localization_away_isOpenEmbedding Af f).isOpenMap _ this
  rw [Set.image_preimage_eq_inter_range]; rw [localization_away_comap_range Af f] at this
  exact ⟨_, Set.inter_subset_left, this, hx, hxf⟩

variable (R) in
open PrimeSpectrum in
/--
lemma `IsSmoothAt.exists_notMem_smooth` / 引理 `IsSmoothAt.exists_notMem_smooth`

English:
lemma IsSmoothAt.exists_notMem_smooth
  statement: [FinitePresentation R A] (p : Ideal A) [p.IsPrime]
  proof: by
  obtain ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩, hxf, hf⟩ :=
    isBasis_basic_opens.exists_subset_of_mem_open ‹⟨p, ‹_›⟩ in smoothLocus R A› isOpen_smoothLocus
  refine ⟨f, by simpa using hxf, ⟨?_, inferInstance⟩⟩
  rwa [basicOpen_subset_smoothLocus_iff] at hf

中文:
引理 IsSmoothAt.存在_notMem_smooth
  结论: [有限呈现 R A] (p : 理想 A) [p.是素]
  证明: by
  obtain ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩, hxf, hf⟩ :=
    isBasis_basic_opens.exists_subset_of_mem_open ‹⟨p, ‹_›⟩ in smoothLocus R A› isOpen_smoothLocus
  refine ⟨f, by simpa using hxf, ⟨?_, inferInstance⟩⟩
  rwa [basicOpen_subset_smoothLocus_iff] at hf

Depends on / 依赖: basicOpen_subset_smoothLocus_iff, exists_subset_of_mem_open, isBasis_basic_opens, isBasis_basic_opens.exists_subset_of_mem_open, isOpen_smoothLocus, smoothLocus
-/
lemma IsSmoothAt.exists_notMem_smooth [FinitePresentation R A] (p : Ideal A) [p.IsPrime]
    [IsSmoothAt R p] :
    exists f ∉ p, Smooth R (Localization.Away f) := by
  obtain ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩, hxf, hf⟩ :=
    isBasis_basic_opens.exists_subset_of_mem_open ‹⟨p, ‹_›⟩ in smoothLocus R A› isOpen_smoothLocus
  refine ⟨f, by simpa using hxf, ⟨?_, inferInstance⟩⟩
  rwa [basicOpen_subset_smoothLocus_iff] at hf

end Algebra
