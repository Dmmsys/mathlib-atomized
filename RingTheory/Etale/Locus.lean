/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Smooth.Locus
public import Mathlib.RingTheory.Unramified.Locus

/-!
# Etale locus of an algebra

## Main results
Let `A` be a `R`-algebra.
- `Algebra.etaleLocus` : The set of primes of `A` where it is étale over `R`.
- `Algebra.basicOpen_subset_etaleLocus_iff` :
  `D(f)` is contained in the etale locus if and only if `A_f` is formally etale over `R`.
- `Algebra.etaleLocus_eq_univ_iff` :
  The etale locus is the whole spectrum if and only if `A` is formally etale over `R`.
- `Algebra.isOpen_etaleLocus` :
  If `A` is of finite type over `R`, then the etale locus is open.
-/

@[expose] public section

namespace Algebra

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra A B]
    [Algebra R B] [IsScalarTower R A B]

variable (R) in
/--
Definition of `IsEtaleAt` / `IsEtaleAt` 的定义

English:
abbreviation IsEtaleAt
  signature: (q : Ideal A) [q.IsPrime]
  body: FormallyEtale R (Localization.AtPrime q)

中文:
缩写 IsEtaleAt
  签名: (q : 理想 A) [q.是素]
  定义体: FormallyEtale R (Localization.AtPrime q)

Depends on / 依赖: AtPrime, FormallyEtale, Localization, Localization.AtPrime
-/
abbrev IsEtaleAt (q : Ideal A) [q.IsPrime] : Prop :=
  FormallyEtale R (Localization.AtPrime q)

variable (R A) in
/--
Definition of `etaleLocus` / `etaleLocus` 的定义

English:
definition etaleLocus
  signature: : Set (PrimeSpectrum A)
  body: { p | IsEtaleAt R p.asIdeal }

@[simp]

中文:
定义 etaleLocus
  签名: : 集合 (素谱 A)
  定义体: { p | IsEtaleAt R p.asIdeal }

@[simp]

Depends on / 依赖: IsEtaleAt, asIdeal, p.asIdeal
-/
def etaleLocus : Set (PrimeSpectrum A) :=
  { p | IsEtaleAt R p.asIdeal }

@[simp]
/--
lemma `mem_etaleLocus_iff` / 引理 `mem_etaleLocus_iff`

English:
lemma mem_etaleLocus_iff
  given: {p : PrimeSpectrum A}
  statement: p in etaleLocus R A ↔ IsEtaleAt R p.asIdeal
  proof: .rfl

中文:
引理 mem_etaleLocus_iff
  条件: {p : 素谱 A}
  结论: p in etaleLocus R A ↔ IsEtaleAt R p.asIdeal
  证明: .rfl
-/
lemma mem_etaleLocus_iff {p : PrimeSpectrum A} : p in etaleLocus R A ↔ IsEtaleAt R p.asIdeal := .rfl

/--
lemma `IsEtaleAt.comp` / 引理 `IsEtaleAt.comp`

English:
lemma IsEtaleAt.comp
  proof: by
  let := Localization.AtPrime.algebraOfLiesOver p P
  have : FormallyEtale (Localization.AtPrime p) (Localization.AtPrime P) :=
    .localization_base p.primeCompl
  exact FormallyEtale.comp R (Localization.AtPrime p) _

中文:
引理 IsEtaleAt.comp
  证明: by
  let := Localization.AtPrime.algebraOfLiesOver p P
  have : FormallyEtale (Localization.AtPrime p) (Localization.AtPrime P) :=
    .localization_base p.primeCompl
  exact FormallyEtale.comp R (Localization.AtPrime p) _

Depends on / 依赖: AtPrime, FormallyEtale, FormallyEtale.comp, Localization, Localization.AtPrime, Localization.AtPrime.algebraOfLiesOver, algebraOfLiesOver, localization_base, p.primeCompl, primeCompl
-/
lemma IsEtaleAt.comp
    (p : Ideal A) (P : Ideal B) [P.LiesOver p] [p.IsPrime] [P.IsPrime]
    [IsEtaleAt R p] [IsEtaleAt A P] : IsEtaleAt R P := by
  let := Localization.AtPrime.algebraOfLiesOver p P
  have : FormallyEtale (Localization.AtPrime p) (Localization.AtPrime P) :=
    .localization_base p.primeCompl
  exact FormallyEtale.comp R (Localization.AtPrime p) _

/--
lemma `etaleLocus_eq_unramfiedLocus_inter_smoothLocus` / 引理 `etaleLocus_eq_unramfiedLocus_inter_smoothLocus`

English:
lemma etaleLocus_eq_unramfiedLocus_inter_smoothLocus
  proof: Set.ext fun _ => FormallyEtale.iff_formallyUnramified_and_formallySmooth

中文:
引理 etaleLocus_eq_unramfiedLocus_inter_smoothLocus
  证明: Set.ext fun _ => FormallyEtale.iff_formallyUnramified_and_formallySmooth

Depends on / 依赖: FormallyEtale, FormallyEtale.iff_formallyUnramified_and_formallySmooth, Set.ext, iff_formallyUnramified_and_formallySmooth
-/
lemma etaleLocus_eq_unramfiedLocus_inter_smoothLocus :
    etaleLocus R A = unramifiedLocus R A inter smoothLocus R A :=
  Set.ext fun _ => FormallyEtale.iff_formallyUnramified_and_formallySmooth

/--
lemma `etaleLocus_eq_compl_support` / 引理 `etaleLocus_eq_compl_support`

English:
lemma etaleLocus_eq_compl_support
  proof: by
  ext p
  simp only [Set.mem_inter_iff, Set.mem_compl_iff, Module.notMem_support_iff]
  have h₁ := IsLocalizedModule.iso p.asIdeal.primeCompl
    (KaehlerDifferential.map R R A (Localization.AtPrime p.asIdeal))
  have h₂ := IsLocalizedModule.iso p.asIdeal.primeCompl
    (H1Cotangent.map R R A (Lo

中文:
引理 etaleLocus_eq_compl_support
  证明: by
  ext p
  simp only [Set.mem_inter_iff, Set.mem_compl_iff, Module.notMem_support_iff]
  have h₁ := IsLocalizedModule.iso p.asIdeal.primeCompl
    (KaehlerDifferential.map R R A (Localization.AtPrime p.asIdeal))
  have h₂ := IsLocalizedModule.iso p.asIdeal.primeCompl
    (H1Cotangent.map R R A (Lo

Depends on / 依赖: Algebra, Algebra.formallyEtale_iff, AtPrime, H1Cotangent, H1Cotangent.map, IsLocalizedModule, IsLocalizedModule.iso, KaehlerDifferential, KaehlerDifferential.map, Localization, Localization.AtPrime, Module, Module.notMem_support_iff, Set.mem_compl_iff, Set.mem_inter_iff, and_congr, asIdeal, formallyEtale_iff, mem_compl_iff, mem_inter_iff
-/
lemma etaleLocus_eq_compl_support :
    etaleLocus R A = (Module.support A Ω[A⁄R])ᶜ inter (Module.support A (H1Cotangent R A))ᶜ := by
  ext p
  simp only [Set.mem_inter_iff, Set.mem_compl_iff, Module.notMem_support_iff]
  have h₁ := IsLocalizedModule.iso p.asIdeal.primeCompl
    (KaehlerDifferential.map R R A (Localization.AtPrime p.asIdeal))
  have h₂ := IsLocalizedModule.iso p.asIdeal.primeCompl
    (H1Cotangent.map R R A (Localization.AtPrime p.asIdeal))
  exact (Algebra.formallyEtale_iff _ _).trans
    (and_congr h₁.subsingleton_congr.symm h₂.subsingleton_congr.symm)

/--
lemma `basicOpen_subset_etaleLocus_iff` / 引理 `basicOpen_subset_etaleLocus_iff`

English:
lemma basicOpen_subset_etaleLocus_iff
  given: {f : A}
  proof: by
  rw [etaleLocus_eq_compl_support]; rw [Set.subset_inter_iff]; rw [Set.subset_compl_comm]; rw [PrimeSpectrum.basicOpen_eq_zeroLocus_compl]; rw [compl_compl]; rw [Set.subset_compl_comm]; rw [compl_compl]; rw [← LocalizedModule.subsingleton_iff_support_subset]; rw [← LocalizedModule.subsingleton_if

中文:
引理 basicOpen_subset_etaleLocus_iff
  条件: {f : A}
  证明: by
  rw [etaleLocus_eq_compl_support]; rw [Set.subset_inter_iff]; rw [Set.subset_compl_comm]; rw [PrimeSpectrum.basicOpen_eq_zeroLocus_compl]; rw [compl_compl]; rw [Set.subset_compl_comm]; rw [compl_compl]; rw [← LocalizedModule.subsingleton_iff_support_subset]; rw [← LocalizedModule.subsingleton_if

Depends on / 依赖: IsLocalizedModule, IsLocalizedModule.iso, KaehlerDifferential, KaehlerDifferential.map, Localization, Localization.Away, LocalizedModule, LocalizedModule.subsingleton_iff_support_subset, PrimeSpectrum, PrimeSpectrum.basicOpen_eq_zeroLocus_compl, Set.subset_compl_comm, Set.subset_inter_iff, and_congr, basicOpen_eq_zeroLocus_compl, compl_compl, etaleLocus_eq_compl_support, formallyEtale_iff, powers, subset_compl_comm, subset_inter_iff
-/
lemma basicOpen_subset_etaleLocus_iff {f : A} :
    ↑(PrimeSpectrum.basicOpen f) subseteq etaleLocus R A ↔
      Algebra.FormallyEtale R (Localization.Away f) := by
  rw [etaleLocus_eq_compl_support]; rw [Set.subset_inter_iff]; rw [Set.subset_compl_comm]; rw [PrimeSpectrum.basicOpen_eq_zeroLocus_compl]; rw [compl_compl]; rw [Set.subset_compl_comm]; rw [compl_compl]; rw [← LocalizedModule.subsingleton_iff_support_subset]; rw [← LocalizedModule.subsingleton_iff_support_subset]; rw [formallyEtale_iff]
  exact and_congr (IsLocalizedModule.iso (.powers f)
    (KaehlerDifferential.map R R A (Localization.Away f))).subsingleton_congr
    (IsLocalizedModule.iso (.powers f)
      (H1Cotangent.map R R A (Localization.Away f))).subsingleton_congr

/--
lemma `etaleLocus_eq_univ_iff` / 引理 `etaleLocus_eq_univ_iff`

English:
lemma etaleLocus_eq_univ_iff
  proof: by
  rw [etaleLocus_eq_compl_support]; rw [← Set.compl_union]; rw [compl_eq_comm]; rw [Set.compl_univ]; rw [eq_comm]; rw [← Set.subset_empty_iff]; rw [Set.union_subset_iff]; rw [Set.subset_empty_iff]; rw [Set.subset_empty_iff]; rw [Module.support_eq_empty_iff]; rw [Module.support_eq_empty_iff]; rw [

中文:
引理 etaleLocus_eq_univ_iff
  证明: by
  rw [etaleLocus_eq_compl_support]; rw [← Set.compl_union]; rw [compl_eq_comm]; rw [Set.compl_univ]; rw [eq_comm]; rw [← Set.subset_empty_iff]; rw [Set.union_subset_iff]; rw [Set.subset_empty_iff]; rw [Set.subset_empty_iff]; rw [Module.support_eq_empty_iff]; rw [Module.support_eq_empty_iff]; rw [

Depends on / 依赖: Algebra, Algebra.formallyEtale_iff, Module, Module.support_eq_empty_iff, Set.compl_union, Set.compl_univ, Set.subset_empty_iff, Set.union_subset_iff, compl_eq_comm, compl_union, compl_univ, eq_comm, etaleLocus_eq_compl_support, formallyEtale_iff, subset_empty_iff, support_eq_empty_iff, union_subset_iff
-/
lemma etaleLocus_eq_univ_iff :
    etaleLocus R A = Set.univ ↔ Algebra.FormallyEtale R A := by
  rw [etaleLocus_eq_compl_support]; rw [← Set.compl_union]; rw [compl_eq_comm]; rw [Set.compl_univ]; rw [eq_comm]; rw [← Set.subset_empty_iff]; rw [Set.union_subset_iff]; rw [Set.subset_empty_iff]; rw [Set.subset_empty_iff]; rw [Module.support_eq_empty_iff]; rw [Module.support_eq_empty_iff]; rw [Algebra.formallyEtale_iff]

variable [FinitePresentation R A]

/--
lemma `isOpen_etaleLocus` / 引理 `isOpen_etaleLocus`

English:
lemma isOpen_etaleLocus
  statement: IsOpen (etaleLocus R A)
  proof: by
  rw [etaleLocus_eq_unramfiedLocus_inter_smoothLocus]
  exact isOpen_unramifiedLocus.inter isOpen_smoothLocus

中文:
引理 isOpen_etaleLocus
  结论: 是开集 (etaleLocus R A)
  证明: by
  rw [etaleLocus_eq_unramfiedLocus_inter_smoothLocus]
  exact isOpen_unramifiedLocus.inter isOpen_smoothLocus

Depends on / 依赖: etaleLocus_eq_unramfiedLocus_inter_smoothLocus, isOpen_smoothLocus, isOpen_unramifiedLocus, isOpen_unramifiedLocus.inter
-/
lemma isOpen_etaleLocus : IsOpen (etaleLocus R A) := by
  rw [etaleLocus_eq_unramfiedLocus_inter_smoothLocus]
  exact isOpen_unramifiedLocus.inter isOpen_smoothLocus

/--
lemma `basicOpen_subset_etaleLocus_iff_etale` / 引理 `basicOpen_subset_etaleLocus_iff_etale`

English:
lemma basicOpen_subset_etaleLocus_iff_etale
  given: {f : A}
  proof: by
  rw [basicOpen_subset_etaleLocus_iff]
  refine ⟨fun H => ⟨H, inferInstance⟩, fun _ => inferInstance⟩

中文:
引理 basicOpen_subset_etaleLocus_iff_etale
  条件: {f : A}
  证明: by
  rw [basicOpen_subset_etaleLocus_iff]
  refine ⟨fun H => ⟨H, inferInstance⟩, fun _ => inferInstance⟩

Depends on / 依赖: basicOpen_subset_etaleLocus_iff
-/
lemma basicOpen_subset_etaleLocus_iff_etale {f : A} :
    ↑(PrimeSpectrum.basicOpen f) subseteq etaleLocus R A ↔ Algebra.Etale R (Localization.Away f) := by
  rw [basicOpen_subset_etaleLocus_iff]
  refine ⟨fun H => ⟨H, inferInstance⟩, fun _ => inferInstance⟩

/--
lemma `etaleLocus_eq_univ_iff_etale` / 引理 `etaleLocus_eq_univ_iff_etale`

English:
lemma etaleLocus_eq_univ_iff_etale
  proof: by
  rw [etaleLocus_eq_univ_iff]
  refine ⟨fun H => ⟨H, inferInstance⟩, fun _ => inferInstance⟩

中文:
引理 etaleLocus_eq_univ_iff_etale
  证明: by
  rw [etaleLocus_eq_univ_iff]
  refine ⟨fun H => ⟨H, inferInstance⟩, fun _ => inferInstance⟩

Depends on / 依赖: etaleLocus_eq_univ_iff
-/
lemma etaleLocus_eq_univ_iff_etale :
    etaleLocus R A = Set.univ ↔ Algebra.Etale R A := by
  rw [etaleLocus_eq_univ_iff]
  refine ⟨fun H => ⟨H, inferInstance⟩, fun _ => inferInstance⟩

/--
lemma `exists_etale_of_isEtaleAt` / 引理 `exists_etale_of_isEtaleAt`

English:
lemma exists_etale_of_isEtaleAt
  proof: by
  obtain ⟨_, ⟨_, ⟨r, rfl⟩, rfl⟩, hpr, hr⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open
      (show ⟨P, ‹_›⟩ in etaleLocus R A by assumption) isOpen_etaleLocus
  exact ⟨r, hpr, ⟨basicOpen_subset_etaleLocus_iff.mp hr, .of_isLocalizationAway r⟩⟩

中文:
引理 存在_etale_of_isEtaleAt
  证明: by
  obtain ⟨_, ⟨_, ⟨r, rfl⟩, rfl⟩, hpr, hr⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open
      (show ⟨P, ‹_›⟩ in etaleLocus R A by assumption) isOpen_etaleLocus
  exact ⟨r, hpr, ⟨basicOpen_subset_etaleLocus_iff.mp hr, .of_isLocalizationAway r⟩⟩

Depends on / 依赖: PrimeSpectrum, PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open, basicOpen_subset_etaleLocus_iff, basicOpen_subset_etaleLocus_iff.mp, etaleLocus, exists_subset_of_mem_open, isBasis_basic_opens, isOpen_etaleLocus, of_isLocalizationAway
-/
lemma exists_etale_of_isEtaleAt
    (P : Ideal A) [P.IsPrime] [IsEtaleAt R P] :
    exists f ∉ P, Algebra.Etale R (Localization.Away f) := by
  obtain ⟨_, ⟨_, ⟨r, rfl⟩, rfl⟩, hpr, hr⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open
      (show ⟨P, ‹_›⟩ in etaleLocus R A by assumption) isOpen_etaleLocus
  exact ⟨r, hpr, ⟨basicOpen_subset_etaleLocus_iff.mp hr, .of_isLocalizationAway r⟩⟩

end Algebra
