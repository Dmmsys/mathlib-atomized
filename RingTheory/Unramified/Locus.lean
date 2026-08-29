/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Support

import Mathlib.RingTheory.Localization.InvSubmonoid

/-!
# Unramified locus of an algebra

## Main results
- `Algebra.unramifiedLocus` : The set of primes that is unramified over the base.
- `Algebra.basicOpen_subset_unramifiedLocus_iff` :
  `D(f)` is contained in the unramified locus if and only if `A_f` is unramified over `R`.
- `Algebra.unramifiedLocus_eq_univ_iff` :
  The unramified locus is the whole spectrum if and only if `A` is unramified over `R`.
- `Algebra.isOpen_unramifiedLocus` :
  If `A` is (essentially) of finite type over `R`, then the unramified locus is open.
-/

@[expose] public section

universe u

namespace Algebra

section

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra A B]
    [Algebra R B] [IsScalarTower R A B]

variable (R) in
/--
Definition of `IsUnramifiedAt` / `IsUnramifiedAt` 的定义

English:
abbreviation IsUnramifiedAt
  signature: (q : Ideal A) [q.IsPrime]
  body: FormallyUnramified R (Localization.AtPrime q)

中文:
缩写 IsUnramifiedAt
  签名: (q : 理想 A) [q.是素]
  定义体: FormallyUnramified R (Localization.AtPrime q)

Depends on / 依赖: AtPrime, FormallyUnramified, Localization, Localization.AtPrime
-/
abbrev IsUnramifiedAt (q : Ideal A) [q.IsPrime] : Prop :=
  FormallyUnramified R (Localization.AtPrime q)

variable (R A) in
/--
Definition of `unramifiedLocus` / `unramifiedLocus` 的定义

English:
definition unramifiedLocus
  signature: : Set (PrimeSpectrum A)
  body: { p | IsUnramifiedAt R p.asIdeal }

中文:
定义 unramifiedLocus
  签名: : 集合 (素谱 A)
  定义体: { p | IsUnramifiedAt R p.asIdeal }

Depends on / 依赖: IsUnramifiedAt, asIdeal, p.asIdeal
-/
def unramifiedLocus : Set (PrimeSpectrum A) :=
  { p | IsUnramifiedAt R p.asIdeal }

/--
lemma `IsUnramifiedAt.comp` / 引理 `IsUnramifiedAt.comp`

English:
lemma IsUnramifiedAt.comp
  proof: by
  let := Localization.AtPrime.algebraOfLiesOver p P
  have : FormallyUnramified (Localization.AtPrime p) (Localization.AtPrime P) :=
    .of_restrictScalars A _ _
  exact FormallyUnramified.comp R (Localization.AtPrime p) _

中文:
引理 IsUnramifiedAt.comp
  证明: by
  let := Localization.AtPrime.algebraOfLiesOver p P
  have : FormallyUnramified (Localization.AtPrime p) (Localization.AtPrime P) :=
    .of_restrictScalars A _ _
  exact FormallyUnramified.comp R (Localization.AtPrime p) _

Depends on / 依赖: AtPrime, FormallyUnramified, FormallyUnramified.comp, Localization, Localization.AtPrime, Localization.AtPrime.algebraOfLiesOver, algebraOfLiesOver, of_restrictScalars
-/
lemma IsUnramifiedAt.comp
    (p : Ideal A) (P : Ideal B) [P.LiesOver p] [p.IsPrime] [P.IsPrime]
    [IsUnramifiedAt R p] [IsUnramifiedAt A P] : IsUnramifiedAt R P := by
  let := Localization.AtPrime.algebraOfLiesOver p P
  have : FormallyUnramified (Localization.AtPrime p) (Localization.AtPrime P) :=
    .of_restrictScalars A _ _
  exact FormallyUnramified.comp R (Localization.AtPrime p) _

variable (R) in
/--
lemma `IsUnramifiedAt.of_restrictScalars` / 引理 `IsUnramifiedAt.of_restrictScalars`

English:
lemma IsUnramifiedAt.of_restrictScalars
  statement: (P : Ideal B) [P.IsPrime]
  proof: FormallyUnramified.of_restrictScalars R _ _

中文:
引理 IsUnramifiedAt.of_restrictScalars
  结论: (P : 理想 B) [P.是素]
  证明: FormallyUnramified.of_restrictScalars R _ _

Depends on / 依赖: FormallyUnramified, FormallyUnramified.of_restrictScalars, of_restrictScalars
-/
lemma IsUnramifiedAt.of_restrictScalars (P : Ideal B) [P.IsPrime]
    [IsUnramifiedAt R P] : IsUnramifiedAt A P :=
  FormallyUnramified.of_restrictScalars R _ _

instance (p : Ideal R) [p.IsPrime] (q : Ideal A) [q.IsPrime] [q.LiesOver p] [IsUnramifiedAt R q]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
    [Localization.AtPrime.IsLiesOverAlgebra p q] :
    FormallyUnramified (Localization.AtPrime p) (Localization.AtPrime q) :=
  .of_restrictScalars R _ _

open _root_.TensorProduct in
/--
theorem `IsUnramifiedAt.residueField` / 定理 `IsUnramifiedAt.residueField`

English:
theorem IsUnramifiedAt.residueField
  proof: by
  let f₀ : Localization.AtPrime Q ->ₐ[R] Localization.AtPrime Q' :=
    Localization.localAlgHom Q Q' _ hQ'
  have hf₀ : Function.Surjective f₀ := by
    subst hQ'; exact P.surjectiveOnStalks_residueField.baseChange' _ _
  let f : P.Fiber (Localization.AtPrime Q) ->ₐ[P.ResidueField] Localization.AtPrime Q' :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _) f₀ fun _ _ => .all _ _
  have hf : Function.Surjective f := hf₀.forall.mpr fun x => ⟨1 otimesₜ x, by simp [f]⟩
  exact .of_surjective _ hf

中文:
定理 IsUnramifiedAt.residueField
  证明: by
  let f₀ : Localization.AtPrime Q ->ₐ[R] Localization.AtPrime Q' :=
    Localization.localAlgHom Q Q' _ hQ'
  have hf₀ : Function.Surjective f₀ := by
    subst hQ'; exact P.surjectiveOnStalks_residueField.baseChange' _ _
  let f : P.Fiber (Localization.AtPrime Q) ->ₐ[P.ResidueField] Localization.AtPrime Q' :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _) f₀ fun _ _ => .all _ _
  have hf : Function.Surjective f := hf₀.forall.mpr fun x => ⟨1 otimesₜ x, by simp [f]⟩
  exact .of_surjective _ hf

Depends on / 依赖: Algebra, Algebra.TensorProduct.lift, Algebra.ofId, AtPrime, Function, Function.Surjective, Localization, Localization.AtPrime, Localization.localAlgHom, P.Fiber, P.ResidueField, P.surjectiveOnStalks_residueField.baseChange, ResidueField, Surjective, TensorProduct, baseChange, forall.mpr, localAlgHom, of_surjective, surjectiveOnStalks_residueField
-/
theorem IsUnramifiedAt.residueField
    (P : Ideal R) [P.IsPrime] (Q : Ideal A) [Q.IsPrime]
    [Q.LiesOver P] [Algebra.IsUnramifiedAt R Q]
    (Q' : Ideal (P.Fiber A)) [Q'.IsPrime]
    (hQ' : Q = Q'.comap Algebra.TensorProduct.includeRight.toRingHom) :
    IsUnramifiedAt P.ResidueField Q' := by
  let f₀ : Localization.AtPrime Q ->ₐ[R] Localization.AtPrime Q' :=
    Localization.localAlgHom Q Q' _ hQ'
  have hf₀ : Function.Surjective f₀ := by
    subst hQ'; exact P.surjectiveOnStalks_residueField.baseChange' _ _
  let f : P.Fiber (Localization.AtPrime Q) ->ₐ[P.ResidueField] Localization.AtPrime Q' :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _) f₀ fun _ _ => .all _ _
  have hf : Function.Surjective f := hf₀.forall.mpr fun x => ⟨1 otimesₜ x, by simp [f]⟩
  exact .of_surjective _ hf

end

section IsUnramifiedIn

variable {R : Type*} [CommRing R]

/--
Definition of `IsUnramifiedIn` / `IsUnramifiedIn` 的定义

English:
definition IsUnramifiedIn
  signature: (A : Type*) [CommRing A] [Algebra R A] (𝔭 : Ideal R)
  body: forall (𝔓 : Ideal A) (_ : 𝔓.IsPrime), 𝔓.LiesOver 𝔭 -> Algebra.IsUnramifiedAt R 𝔓

中文:
定义 IsUnramifiedIn
  签名: (A : 类型) [交换环 A] [代数 R A] (𝔭 : 理想 R)
  定义体: forall (𝔓 : Ideal A) (_ : 𝔓.IsPrime), 𝔓.LiesOver 𝔭 -> Algebra.IsUnramifiedAt R 𝔓

Depends on / 依赖: Algebra, Algebra.IsUnramifiedAt, IsPrime, IsUnramifiedAt, LiesOver
-/
def IsUnramifiedIn (A : Type*) [CommRing A] [Algebra R A] (𝔭 : Ideal R) : Prop :=
  forall (𝔓 : Ideal A) (_ : 𝔓.IsPrime), 𝔓.LiesOver 𝔭 -> Algebra.IsUnramifiedAt R 𝔓

variable (A : Type*) [CommRing A] [Algebra R A]

/--
theorem `isUnramifiedIn_top` / 定理 `isUnramifiedIn_top`

English:
theorem isUnramifiedIn_top
  statement: IsUnramifiedIn A (⊤ : Ideal R)
  proof: fun P hP _ => (hP.ne_top ((Ideal.eq_top_iff_of_liesOver P (⊤ : Ideal R)).mpr rfl)).elim

中文:
定理 isUnramifiedIn_top
  结论: IsUnramifiedIn A (⊤ : 理想 R)
  证明: fun P hP _ => (hP.ne_top ((Ideal.eq_top_iff_of_liesOver P (⊤ : Ideal R)).mpr rfl)).elim

Depends on / 依赖: Ideal.eq_top_iff_of_liesOver, eq_top_iff_of_liesOver, hP.ne_top, ne_top
-/
theorem isUnramifiedIn_top : IsUnramifiedIn A (⊤ : Ideal R) :=
  fun P hP _ => (hP.ne_top ((Ideal.eq_top_iff_of_liesOver P (⊤ : Ideal R)).mpr rfl)).elim

end IsUnramifiedIn
section

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/--
lemma `unramifiedLocus_eq_compl_support` / 引理 `unramifiedLocus_eq_compl_support`

English:
lemma unramifiedLocus_eq_compl_support
  proof: by
  ext p
  simp only [Set.mem_compl_iff, Module.notMem_support_iff]
  have := IsLocalizedModule.iso p.asIdeal.primeCompl
    (KaehlerDifferential.map R R A (Localization.AtPrime p.asIdeal))
  exact (Algebra.formallyUnramified_iff _ _).trans this.subsingleton_congr.symm

中文:
引理 unramifiedLocus_eq_compl_support
  证明: by
  ext p
  simp only [Set.mem_compl_iff, Module.notMem_support_iff]
  have := IsLocalizedModule.iso p.asIdeal.primeCompl
    (KaehlerDifferential.map R R A (Localization.AtPrime p.asIdeal))
  exact (Algebra.formallyUnramified_iff _ _).trans this.subsingleton_congr.symm

Depends on / 依赖: Algebra, Algebra.formallyUnramified_iff, AtPrime, IsLocalizedModule, IsLocalizedModule.iso, KaehlerDifferential, KaehlerDifferential.map, Localization, Localization.AtPrime, Module, Module.notMem_support_iff, Set.mem_compl_iff, asIdeal, formallyUnramified_iff, mem_compl_iff, notMem_support_iff, p.asIdeal, p.asIdeal.primeCompl, primeCompl, subsingleton_congr
-/
lemma unramifiedLocus_eq_compl_support :
    unramifiedLocus R A = (Module.support A Ω[A⁄R])ᶜ := by
  ext p
  simp only [Set.mem_compl_iff, Module.notMem_support_iff]
  have := IsLocalizedModule.iso p.asIdeal.primeCompl
    (KaehlerDifferential.map R R A (Localization.AtPrime p.asIdeal))
  exact (Algebra.formallyUnramified_iff _ _).trans this.subsingleton_congr.symm

/--
lemma `basicOpen_subset_unramifiedLocus_iff` / 引理 `basicOpen_subset_unramifiedLocus_iff`

English:
lemma basicOpen_subset_unramifiedLocus_iff
  given: {f : A}
  proof: by
  rw [unramifiedLocus_eq_compl_support]; rw [Set.subset_compl_comm]; rw [PrimeSpectrum.basicOpen_eq_zeroLocus_compl]; rw [compl_compl]; rw [← LocalizedModule.subsingleton_iff_support_subset]; rw [Algebra.formallyUnramified_iff]
  exact (IsLocalizedModule.iso (.powers f)
    (KaehlerDifferential.map R R A (Localization.Away f))).subsingleton_congr

中文:
引理 basicOpen_subset_unramifiedLocus_iff
  条件: {f : A}
  证明: by
  rw [unramifiedLocus_eq_compl_support]; rw [Set.subset_compl_comm]; rw [PrimeSpectrum.basicOpen_eq_zeroLocus_compl]; rw [compl_compl]; rw [← LocalizedModule.subsingleton_iff_support_subset]; rw [Algebra.formallyUnramified_iff]
  exact (IsLocalizedModule.iso (.powers f)
    (KaehlerDifferential.map R R A (Localization.Away f))).subsingleton_congr

Depends on / 依赖: Algebra, Algebra.formallyUnramified_iff, IsLocalizedModule, IsLocalizedModule.iso, KaehlerDifferential, KaehlerDifferential.map, Localization, Localization.Away, LocalizedModule, LocalizedModule.subsingleton_iff_support_subset, PrimeSpectrum, PrimeSpectrum.basicOpen_eq_zeroLocus_compl, Set.subset_compl_comm, basicOpen_eq_zeroLocus_compl, compl_compl, formallyUnramified_iff, powers, subset_compl_comm, subsingleton_congr, subsingleton_iff_support_subset
-/
lemma basicOpen_subset_unramifiedLocus_iff {f : A} :
    ↑(PrimeSpectrum.basicOpen f) subseteq unramifiedLocus R A ↔
      Algebra.FormallyUnramified R (Localization.Away f) := by
  rw [unramifiedLocus_eq_compl_support]; rw [Set.subset_compl_comm]; rw [PrimeSpectrum.basicOpen_eq_zeroLocus_compl]; rw [compl_compl]; rw [← LocalizedModule.subsingleton_iff_support_subset]; rw [Algebra.formallyUnramified_iff]
  exact (IsLocalizedModule.iso (.powers f)
    (KaehlerDifferential.map R R A (Localization.Away f))).subsingleton_congr

/--
lemma `unramifiedLocus_eq_univ_iff` / 引理 `unramifiedLocus_eq_univ_iff`

English:
lemma unramifiedLocus_eq_univ_iff
  proof: by
  rw [unramifiedLocus_eq_compl_support]; rw [compl_eq_comm]; rw [Set.compl_univ]; rw [eq_comm]; rw [Module.support_eq_empty_iff]; rw [Algebra.formallyUnramified_iff]

中文:
引理 unramifiedLocus_eq_univ_iff
  证明: by
  rw [unramifiedLocus_eq_compl_support]; rw [compl_eq_comm]; rw [Set.compl_univ]; rw [eq_comm]; rw [Module.support_eq_empty_iff]; rw [Algebra.formallyUnramified_iff]

Depends on / 依赖: Algebra, Algebra.formallyUnramified_iff, Module, Module.support_eq_empty_iff, Set.compl_univ, compl_eq_comm, compl_univ, eq_comm, formallyUnramified_iff, support_eq_empty_iff, unramifiedLocus_eq_compl_support
-/
lemma unramifiedLocus_eq_univ_iff :
    unramifiedLocus R A = Set.univ ↔ Algebra.FormallyUnramified R A := by
  rw [unramifiedLocus_eq_compl_support]; rw [compl_eq_comm]; rw [Set.compl_univ]; rw [eq_comm]; rw [Module.support_eq_empty_iff]; rw [Algebra.formallyUnramified_iff]

/--
theorem `formallyUnramified_iff_forall` / 定理 `formallyUnramified_iff_forall`

English:
theorem formallyUnramified_iff_forall
  proof: unramifiedLocus_eq_univ_iff.symm.trans Set.eq_univ_iff_forall

中文:
定理 formallyUnramified_iff_对任意
  证明: unramifiedLocus_eq_univ_iff.symm.trans Set.eq_univ_iff_forall

Depends on / 依赖: Set.eq_univ_iff_forall, eq_univ_iff_forall, unramifiedLocus_eq_univ_iff, unramifiedLocus_eq_univ_iff.symm.trans
-/
theorem formallyUnramified_iff_forall :
    FormallyUnramified R A ↔ forall q : PrimeSpectrum A, IsUnramifiedAt R q.1 :=
  unramifiedLocus_eq_univ_iff.symm.trans Set.eq_univ_iff_forall

/--
theorem `unramified_iff_forall` / 定理 `unramified_iff_forall`

English:
theorem unramified_iff_forall
  given: [FiniteType R A]
  proof: .trans ⟨fun h => h.formallyUnramified, fun h => ⟨h, inferInstance⟩⟩ formallyUnramified_iff_forall

中文:
定理 unramified_iff_对任意
  条件: [有限型 R A]
  证明: .trans ⟨fun h => h.formallyUnramified, fun h => ⟨h, inferInstance⟩⟩ formallyUnramified_iff_forall

Depends on / 依赖: formallyUnramified, formallyUnramified_iff_forall, h.formallyUnramified
-/
theorem unramified_iff_forall [FiniteType R A] :
    Unramified R A ↔ forall q : PrimeSpectrum A, IsUnramifiedAt R q.1 :=
  .trans ⟨fun h => h.formallyUnramified, fun h => ⟨h, inferInstance⟩⟩ formallyUnramified_iff_forall

/--
lemma `isOpen_unramifiedLocus` / 引理 `isOpen_unramifiedLocus`

English:
lemma isOpen_unramifiedLocus
  given: [EssFiniteType R A]
  statement: IsOpen (unramifiedLocus R A)
  proof: by
  rw [unramifiedLocus_eq_compl_support]; rw [Module.support_eq_zeroLocus]
  exact (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl

中文:
引理 isOpen_unramifiedLocus
  条件: [EssFiniteType R A]
  结论: 是开集 (unramifiedLocus R A)
  证明: by
  rw [unramifiedLocus_eq_compl_support]; rw [Module.support_eq_zeroLocus]
  exact (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl

Depends on / 依赖: Module, Module.support_eq_zeroLocus, PrimeSpectrum, PrimeSpectrum.isClosed_zeroLocus, isClosed_zeroLocus, isOpen_compl, support_eq_zeroLocus, unramifiedLocus_eq_compl_support
-/
lemma isOpen_unramifiedLocus [EssFiniteType R A] : IsOpen (unramifiedLocus R A) := by
  rw [unramifiedLocus_eq_compl_support]; rw [Module.support_eq_zeroLocus]
  exact (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl

/--
lemma `exists_formallyUnramified_of_isUnramifiedAt` / 引理 `exists_formallyUnramified_of_isUnramifiedAt`

English:
lemma exists_formallyUnramified_of_isUnramifiedAt
  statement: [EssFiniteType R A] (p : Ideal A) [p.IsPrime]
  proof: by
  obtain ⟨_, ⟨_, ⟨r, rfl⟩, rfl⟩, hpr, hr⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open
      (show ⟨p, ‹_›⟩ in unramifiedLocus R A from ‹_›) isOpen_unramifiedLocus
  exact ⟨r, hpr, basicOpen_subset_unramifiedLocus_iff.mp hr⟩

中文:
引理 存在_formallyUnramified_of_isUnramifiedAt
  结论: [EssFiniteType R A] (p : 理想 A) [p.是素]
  证明: by
  obtain ⟨_, ⟨_, ⟨r, rfl⟩, rfl⟩, hpr, hr⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open
      (show ⟨p, ‹_›⟩ in unramifiedLocus R A from ‹_›) isOpen_unramifiedLocus
  exact ⟨r, hpr, basicOpen_subset_unramifiedLocus_iff.mp hr⟩

Depends on / 依赖: PrimeSpectrum, PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open, basicOpen_subset_unramifiedLocus_iff, basicOpen_subset_unramifiedLocus_iff.mp, exists_subset_of_mem_open, isBasis_basic_opens, isOpen_unramifiedLocus, unramifiedLocus
-/
lemma exists_formallyUnramified_of_isUnramifiedAt [EssFiniteType R A] (p : Ideal A) [p.IsPrime]
    [IsUnramifiedAt R p] : exists f ∉ p, Algebra.FormallyUnramified R (Localization.Away f) := by
  obtain ⟨_, ⟨_, ⟨r, rfl⟩, rfl⟩, hpr, hr⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open
      (show ⟨p, ‹_›⟩ in unramifiedLocus R A from ‹_›) isOpen_unramifiedLocus
  exact ⟨r, hpr, basicOpen_subset_unramifiedLocus_iff.mp hr⟩

/--
lemma `exists_unramified_of_isUnramifiedAt` / 引理 `exists_unramified_of_isUnramifiedAt`

English:
lemma exists_unramified_of_isUnramifiedAt
  statement: [Algebra.FiniteType R A] (p : Ideal A) [p.IsPrime]
  proof: by
  obtain ⟨f, hfp, H⟩ := exists_formallyUnramified_of_isUnramifiedAt (R := R) p
  exact ⟨f, hfp, ⟨H, .trans ‹_› (IsLocalization.finiteType_of_monoid_fg (.powers f) _)⟩⟩

中文:
引理 存在_unramified_of_isUnramifiedAt
  结论: [代数.有限型 R A] (p : 理想 A) [p.是素]
  证明: by
  obtain ⟨f, hfp, H⟩ := exists_formallyUnramified_of_isUnramifiedAt (R := R) p
  exact ⟨f, hfp, ⟨H, .trans ‹_› (IsLocalization.finiteType_of_monoid_fg (.powers f) _)⟩⟩

Depends on / 依赖: IsLocalization, IsLocalization.finiteType_of_monoid_fg, exists_formallyUnramified_of_isUnramifiedAt, finiteType_of_monoid_fg, powers
-/
lemma exists_unramified_of_isUnramifiedAt [Algebra.FiniteType R A] (p : Ideal A) [p.IsPrime]
    [IsUnramifiedAt R p] : exists f ∉ p, Algebra.Unramified R (Localization.Away f) := by
  obtain ⟨f, hfp, H⟩ := exists_formallyUnramified_of_isUnramifiedAt (R := R) p
  exact ⟨f, hfp, ⟨H, .trans ‹_› (IsLocalization.finiteType_of_monoid_fg (.powers f) _)⟩⟩

end

end Algebra
