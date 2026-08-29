/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.LocalProperties.Projective
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Localization.Free
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
public import Mathlib.RingTheory.Support

/-!

# The free locus of a module

## Main definitions and results

Let `M` be a finitely presented `R`-module.
- `Module.freeLocus`: The set of points `x` in `Spec R` such that `Mₓ` is free over `Rₓ`.
- `Module.freeLocus_eq_univ_iff`:
  The free locus is the whole `Spec R` if and only if `M` is projective.
- `Module.basicOpen_subset_freeLocus_iff`: `D(f)` is contained in the free locus if and only if
  `M_f` is projective over `R_f`.
- `Module.rankAtStalk`: The function `Spec R → ℕ` sending `x` to `rank_{Rₓ} Mₓ`.
- `Module.isLocallyConstant_rankAtStalk`:
  If `M` is flat over `R`, then `rankAtStalk` is locally constant.

-/

@[expose] public section

universe uR uM

variable (R : Type uR) (M : Type uM) [CommRing R] [AddCommGroup M] [Module R M]

namespace Module

open PrimeSpectrum TensorProduct

/--
Definition of `freeLocus` / `freeLocus` 的定义

English:
definition freeLocus
  signature: : Set (PrimeSpectrum R)
  body: { p | Module.Free (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M) }

中文:
定义 freeLocus
  签名: : 集合 (素谱 R)
  定义体: { p | Module.Free (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M) }

Depends on / 依赖: AtPrime, Localization, Localization.AtPrime, LocalizedModule, Module, Module.Free, asIdeal, p.asIdeal, p.asIdeal.primeCompl, primeCompl
-/
def freeLocus : Set (PrimeSpectrum R) :=
  { p | Module.Free (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M) }

variable {R M}

/--
lemma `mem_freeLocus` / 引理 `mem_freeLocus`

English:
lemma mem_freeLocus
  given: {p}
  statement: p in freeLocus R M ↔
  proof: Iff.rfl

中文:
引理 mem_freeLocus
  条件: {p}
  结论: p in freeLocus R M ↔
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma mem_freeLocus {p} : p in freeLocus R M ↔
    Module.Free (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M) :=
  Iff.rfl

attribute [local instance] RingHomInvPair.of_ringEquiv in
/--
lemma `mem_freeLocus_of_isLocalization` / 引理 `mem_freeLocus_of_isLocalization`

English:
lemma mem_freeLocus_of_isLocalization
  statement: (p : PrimeSpectrum R)
  proof: by
  set e := (IsLocalization.algEquiv p.asIdeal.primeCompl
      (Localization.AtPrime p.asIdeal) Rₚ).toRingEquiv
  apply Module.Free.iff_of_equiv (σ := e)
  refine { __ := IsLocalizedModule.iso p.asIdeal.primeCompl f, map_smul' := ?_ }
  intro r x
  obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_

中文:
引理 mem_freeLocus_of_isLocalization
  结论: (p : 素谱 R)
  证明: by
  set e := (IsLocalization.algEquiv p.asIdeal.primeCompl
      (Localization.AtPrime p.asIdeal) Rₚ).toRingEquiv
  apply Module.Free.iff_of_equiv (σ := e)
  refine { __ := IsLocalizedModule.iso p.asIdeal.primeCompl f, map_smul' := ?_ }
  intro r x
  obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_

Depends on / 依赖: AtPrime, IsLocalization, IsLocalization.algEquiv, IsLocalization.exists_mk, IsLocalizedModule, IsLocalizedModule.iso, IsLocalizedModule.map_units, Localization, Localization.AtPrime, Module, Module.End.isUnit_iff, Module.Free.iff_of_equiv, algEquiv, asIdeal, exists_mk, iff_of_equiv, isUnit_iff, map_smul, map_units, p.asIdeal
-/
lemma mem_freeLocus_of_isLocalization (p : PrimeSpectrum R)
    (Rₚ Mₚ) [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p.asIdeal]
    [AddCommGroup Mₚ] [Module R Mₚ] (f : M ->ₗ[R] Mₚ) [IsLocalizedModule p.asIdeal.primeCompl f]
    [Module Rₚ Mₚ] [IsScalarTower R Rₚ Mₚ] :
    p in freeLocus R M ↔ Module.Free Rₚ Mₚ := by
  set e := (IsLocalization.algEquiv p.asIdeal.primeCompl
      (Localization.AtPrime p.asIdeal) Rₚ).toRingEquiv
  apply Module.Free.iff_of_equiv (σ := e)
  refine { __ := IsLocalizedModule.iso p.asIdeal.primeCompl f, map_smul' := ?_ }
  intro r x
  obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq p.asIdeal.primeCompl r
  apply ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units f s)).1
  simp [e, ← map_smul, ← smul_assoc]

attribute [local instance] RingHomInvPair.of_ringEquiv in
/--
lemma `mem_freeLocus_iff_tensor` / 引理 `mem_freeLocus_iff_tensor`

English:
lemma mem_freeLocus_iff_tensor
  statement: (p : PrimeSpectrum R)
  proof: by
  exact mem_freeLocus_of_isLocalization p Rₚ (f := TensorProduct.mk R Rₚ M 1)

中文:
引理 mem_freeLocus_iff_tensor
  结论: (p : 素谱 R)
  证明: by
  exact mem_freeLocus_of_isLocalization p Rₚ (f := TensorProduct.mk R Rₚ M 1)

Depends on / 依赖: TensorProduct, TensorProduct.mk, mem_freeLocus_of_isLocalization
-/
lemma mem_freeLocus_iff_tensor (p : PrimeSpectrum R)
    (Rₚ) [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p.asIdeal] :
    p in freeLocus R M ↔ Module.Free Rₚ (Rₚ otimes[R] M) := by
  exact mem_freeLocus_of_isLocalization p Rₚ (f := TensorProduct.mk R Rₚ M 1)

/--
lemma `freeLocus_congr` / 引理 `freeLocus_congr`

English:
lemma freeLocus_congr
  given: {M'} [AddCommGroup M'] [Module R M'] (e : M ≃ₗ[R] M')
  proof: by
  ext p
  exact mem_freeLocus_of_isLocalization _ _ _
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M' ∘ₗ e.toLinearMap)

中文:
引理 freeLocus_congr
  条件: {M'} [加法交换群 M'] [模 R M'] (e : M ≃ₗ[R] M')
  证明: by
  ext p
  exact mem_freeLocus_of_isLocalization _ _ _
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M' ∘ₗ e.toLinearMap)

Depends on / 依赖: LocalizedModule, LocalizedModule.mkLinearMap, asIdeal, e.toLinearMap, mem_freeLocus_of_isLocalization, mkLinearMap, p.asIdeal.primeCompl, primeCompl, toLinearMap
-/
lemma freeLocus_congr {M'} [AddCommGroup M'] [Module R M'] (e : M ≃ₗ[R] M') :
    freeLocus R M = freeLocus R M' := by
  ext p
  exact mem_freeLocus_of_isLocalization _ _ _
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M' ∘ₗ e.toLinearMap)

set_option backward.isDefEq.respectTransparency false in
open TensorProduct in
/--
lemma `comap_freeLocus_le` / 引理 `comap_freeLocus_le`

English:
lemma comap_freeLocus_le
  given: {A} [CommRing A] [Algebra R A]
  proof: by
  intro p hp
  let Rₚ := Localization.AtPrime (comap (algebraMap R A) p).asIdeal
  let Aₚ := Localization.AtPrime p.asIdeal
  rw [Set.mem_preimage]; rw [mem_freeLocus_iff_tensor _ Rₚ] at hp
  rw [mem_freeLocus_iff_tensor _ Aₚ]
  let algebra : Algebra Rₚ Aₚ := (Localization.localRingHom
    (comap

中文:
引理 comap_freeLocus_le
  条件: {A} [交换环 A] [代数 R A]
  证明: by
  intro p hp
  let Rₚ := Localization.AtPrime (comap (algebraMap R A) p).asIdeal
  let Aₚ := Localization.AtPrime p.asIdeal
  rw [Set.mem_preimage]; rw [mem_freeLocus_iff_tensor _ Rₚ] at hp
  rw [mem_freeLocus_iff_tensor _ Aₚ]
  let algebra : Algebra Rₚ Aₚ := (Localization.localRingHom
    (comap

Depends on / 依赖: Algebra, AtPrime, IsScalarTower, IsScalarTower.of_algebraMap_eq, Localization, Localization.AtPrime, Localization.localRingHo, Localization.localRingHom, RingHom, RingHom.algebraMap_toAlgebra, Set.mem_preimage, algebra, algebraMap, algebraMap_toAlgebra, asIdeal, localRingHo, localRingHom, mem_freeLocus_iff_tensor, mem_preimage, of_algebraMap_eq
-/
lemma comap_freeLocus_le {A} [CommRing A] [Algebra R A] :
    comap (algebraMap R A) ⁻¹' freeLocus R M <= freeLocus A (A otimes[R] M) := by
  intro p hp
  let Rₚ := Localization.AtPrime (comap (algebraMap R A) p).asIdeal
  let Aₚ := Localization.AtPrime p.asIdeal
  rw [Set.mem_preimage]; rw [mem_freeLocus_iff_tensor _ Rₚ] at hp
  rw [mem_freeLocus_iff_tensor _ Aₚ]
  let algebra : Algebra Rₚ Aₚ := (Localization.localRingHom
    (comap (algebraMap R A) p).asIdeal p.asIdeal (algebraMap R A) rfl).toAlgebra
  have : IsScalarTower R Rₚ Aₚ := IsScalarTower.of_algebraMap_eq'
    (by simp [Rₚ, Aₚ, algebra, RingHom.algebraMap_toAlgebra, Localization.localRingHom,
        ← IsScalarTower.algebraMap_eq])
  let e := AlgebraTensorModule.cancelBaseChange R Rₚ Aₚ Aₚ M ≪≫ₗ
    (AlgebraTensorModule.cancelBaseChange R A Aₚ Aₚ M).symm
  exact .of_equiv e

/--
lemma `freeLocus_localization` / 引理 `freeLocus_localization`

English:
lemma freeLocus_localization
  given: (S : Submonoid R)
  proof: by
  ext p
  simp only [Set.mem_preimage]
  let p' := p.asIdeal.comap (algebraMap R _)
  have hp' : S <= p'.primeCompl := fun x hx H =>
    p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ H (IsLocalization.map_units _ ⟨x, hx⟩))
  let Rₚ := Localization.AtPrime p'
  let Mₚ := LocalizedModule p'.primeC

中文:
引理 freeLocus_localization
  条件: (S : 子幺半群 R)
  证明: by
  ext p
  simp only [Set.mem_preimage]
  let p' := p.asIdeal.comap (algebraMap R _)
  have hp' : S <= p'.primeCompl := fun x hx H =>
    p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ H (IsLocalization.map_units _ ⟨x, hx⟩))
  let Rₚ := Localization.AtPrime p'
  let Mₚ := LocalizedModule p'.primeC

Depends on / 依赖: Algebra, AtPrime, Ideal.eq_top_of_isUnit_mem, IsLocalization, IsLocalization.localizationAlgebraOfSubmonoidLe, IsLocalization.localization_isScalarTower_of_submonoid, IsLocalization.map_units, IsScalarTower, Localization, Localization.AtPrime, LocalizedModule, Set.mem_preimage, algebraMap, asIdeal, eq_top_of_isUnit_mem, isPrime, localizationAlgebraOfSubmonoidLe, localization_isScalarTower_of_submonoid, map_units, mem_preimage
-/
lemma freeLocus_localization (S : Submonoid R) :
    freeLocus (Localization S) (LocalizedModule S M) =
      comap (algebraMap R _) ⁻¹' freeLocus R M := by
  ext p
  simp only [Set.mem_preimage]
  let p' := p.asIdeal.comap (algebraMap R _)
  have hp' : S <= p'.primeCompl := fun x hx H =>
    p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ H (IsLocalization.map_units _ ⟨x, hx⟩))
  let Rₚ := Localization.AtPrime p'
  let Mₚ := LocalizedModule p'.primeCompl M
  let : Algebra (Localization S) Rₚ :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ S p'.primeCompl hp'
  have : IsScalarTower R (Localization S) Rₚ :=
    IsLocalization.localization_isScalarTower_of_submonoid_le ..
  have : IsLocalization.AtPrime Rₚ p.asIdeal := by
    have := IsLocalization.isLocalization_of_submonoid_le (Localization S) Rₚ _ _ hp'
    apply IsLocalization.isLocalization_of_is_exists_mul_mem _
      (Submonoid.map (algebraMap R (Localization S)) p'.primeCompl)
    · rintro _ ⟨x, hx, rfl⟩; exact hx
    · rintro ⟨x, hx⟩
      obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq S x
      refine ⟨algebraMap _ _ s.1, x, fun H => hx ?_, by simp⟩
      rw [IsLocalization.mk'_eq_mul_mk'_one]
      exact Ideal.mul_mem_right _ _ H
  let : Module (Localization S) Mₚ := Module.compHom Mₚ (algebraMap _ Rₚ)
  have : IsScalarTower R (Localization S) Mₚ :=
    ⟨fun r r' m => show algebraMap _ Rₚ (r • r') • m = _ by
      simp [p', Rₚ, Mₚ, Algebra.smul_def, ← IsScalarTower.algebraMap_apply, mul_smul]; rfl⟩
  have : IsScalarTower (Localization S) Rₚ Mₚ :=
    ⟨fun r r' m => show _ = algebraMap _ Rₚ r • r' • m by rw [← mul_smul, ← Algebra.smul_def]⟩
  let l := (IsLocalizedModule.liftOfLE _ _ hp' (LocalizedModule.mkLinearMap S M)
    (LocalizedModule.mkLinearMap p'.primeCompl M)).extendScalarsOfIsLocalization S
    (Localization S)
  have : IsLocalizedModule p.asIdeal.primeCompl l := by
    have : IsLocalizedModule p'.primeCompl (l.restrictScalars R) :=
      inferInstanceAs (IsLocalizedModule p'.primeCompl
        (IsLocalizedModule.liftOfLE _ _ hp' (LocalizedModule.mkLinearMap S M)
        (LocalizedModule.mkLinearMap p'.primeCompl M)))
    have : IsLocalizedModule (Algebra.algebraMapSubmonoid (Localization S) p'.primeCompl) l :=
      IsLocalizedModule.of_restrictScalars p'.primeCompl ..
    apply IsLocalizedModule.of_exists_mul_mem
      (Algebra.algebraMapSubmonoid (Localization S) p'.primeCompl)
    · rintro _ ⟨x, hx, rfl⟩; exact hx
    · rintro ⟨x, hx⟩
      obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq S x
      refine ⟨algebraMap _ _ s.1, x, fun H => hx ?_, by simp⟩
      rw [IsLocalization.mk'_eq_mul_mk'_one]
      exact Ideal.mul_mem_right _ _ H
  rw [mem_freeLocus_of_isLocalization (R := Localization S) p Rₚ Mₚ l]
  rfl

/--
lemma `freeLocus_eq_univ_iff` / 引理 `freeLocus_eq_univ_iff`

English:
lemma freeLocus_eq_univ_iff
  given: [Module.FinitePresentation R M]
  proof: by
  simp_rw [Set.eq_univ_iff_forall, mem_freeLocus]
  exact ⟨fun H => Module.projective_of_localization_maximal fun I hI =>
    have := H ⟨I, hI.isPrime⟩; .of_free, fun H x => Module.free_of_flat_of_isLocalRing⟩

中文:
引理 freeLocus_eq_univ_iff
  条件: [模.有限呈现 R M]
  证明: by
  simp_rw [Set.eq_univ_iff_forall, mem_freeLocus]
  exact ⟨fun H => Module.projective_of_localization_maximal fun I hI =>
    have := H ⟨I, hI.isPrime⟩; .of_free, fun H x => Module.free_of_flat_of_isLocalRing⟩

Depends on / 依赖: Module, Module.free_of_flat_of_isLocalRing, Module.projective_of_localization_maximal, Set.eq_univ_iff_forall, eq_univ_iff_forall, free_of_flat_of_isLocalRing, hI.isPrime, isPrime, mem_freeLocus, of_free, projective_of_localization_maximal, simp_rw
-/
lemma freeLocus_eq_univ_iff [Module.FinitePresentation R M] :
    freeLocus R M = Set.univ ↔ Module.Projective R M := by
  simp_rw [Set.eq_univ_iff_forall, mem_freeLocus]
  exact ⟨fun H => Module.projective_of_localization_maximal fun I hI =>
    have := H ⟨I, hI.isPrime⟩; .of_free, fun H x => Module.free_of_flat_of_isLocalRing⟩

/--
lemma `freeLocus_eq_univ` / 引理 `freeLocus_eq_univ`

English:
lemma freeLocus_eq_univ
  given: [Module.Finite R M] [Module.Flat R M]
  proof: by
  simp_rw [Set.eq_univ_iff_forall, mem_freeLocus]
  exact fun x => Module.free_of_flat_of_isLocalRing

中文:
引理 freeLocus_eq_univ
  条件: [模.有限 R M] [模.平坦 R M]
  证明: by
  simp_rw [Set.eq_univ_iff_forall, mem_freeLocus]
  exact fun x => Module.free_of_flat_of_isLocalRing

Depends on / 依赖: Module, Module.free_of_flat_of_isLocalRing, Set.eq_univ_iff_forall, eq_univ_iff_forall, free_of_flat_of_isLocalRing, mem_freeLocus, simp_rw
-/
lemma freeLocus_eq_univ [Module.Finite R M] [Module.Flat R M] :
    freeLocus R M = Set.univ := by
  simp_rw [Set.eq_univ_iff_forall, mem_freeLocus]
  exact fun x => Module.free_of_flat_of_isLocalRing

/--
lemma `basicOpen_subset_freeLocus_iff` / 引理 `basicOpen_subset_freeLocus_iff`

English:
lemma basicOpen_subset_freeLocus_iff
  given: [Module.FinitePresentation R M] {f : R}
  proof: by
  rw [← freeLocus_eq_univ_iff]; rw [freeLocus_localization]; rw [Set.preimage_eq_univ_iff]; rw [localization_away_comap_range _ f]

中文:
引理 basicOpen_subset_freeLocus_iff
  条件: [模.有限呈现 R M] {f : R}
  证明: by
  rw [← freeLocus_eq_univ_iff]; rw [freeLocus_localization]; rw [Set.preimage_eq_univ_iff]; rw [localization_away_comap_range _ f]

Depends on / 依赖: Set.preimage_eq_univ_iff, freeLocus_eq_univ_iff, freeLocus_localization, localization_away_comap_range, preimage_eq_univ_iff
-/
lemma basicOpen_subset_freeLocus_iff [Module.FinitePresentation R M] {f : R} :
    (basicOpen f : Set (PrimeSpectrum R)) subseteq freeLocus R M ↔
      Module.Projective (Localization.Away f) (LocalizedModule.Away f M) := by
  rw [← freeLocus_eq_univ_iff]; rw [freeLocus_localization]; rw [Set.preimage_eq_univ_iff]; rw [localization_away_comap_range _ f]

/--
lemma `isOpen_freeLocus` / 引理 `isOpen_freeLocus`

English:
lemma isOpen_freeLocus
  given: [Module.FinitePresentation R M]
  proof: by
  refine isOpen_iff_forall_mem_open.mpr fun x hx => ?_
  have : Module.Free _ _ := hx
  obtain ⟨r, hr, hr', _⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    x.asIdeal.primeCompl (LocalizedModule.mkLinearMap x.asIdeal.primeCompl M)
    (Localization.AtPrime x.asIdeal)
  exact

中文:
引理 isOpen_freeLocus
  条件: [模.有限呈现 R M]
  证明: by
  refine isOpen_iff_forall_mem_open.mpr fun x hx => ?_
  have : Module.Free _ _ := hx
  obtain ⟨r, hr, hr', _⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    x.asIdeal.primeCompl (LocalizedModule.mkLinearMap x.asIdeal.primeCompl M)
    (Localization.AtPrime x.asIdeal)
  exact

Depends on / 依赖: AtPrime, FinitePresentation, Localization, Localization.AtPrime, LocalizedModule, LocalizedModule.mkLinearMap, Module, Module.FinitePresentation.exists_free_localizedModule_powers, Module.Free, asIdeal, basicOpen, basicOpen_subset_freeLocus_iff, basicOpen_subset_freeLocus_iff.mpr, exists_free_localizedModule_powers, isOpen_iff_forall_mem_open, isOpen_iff_forall_mem_open.mpr, mkLinearMap, primeCompl, x.asIdeal, x.asIdeal.primeCompl
-/
lemma isOpen_freeLocus [Module.FinitePresentation R M] :
    IsOpen (freeLocus R M) := by
  refine isOpen_iff_forall_mem_open.mpr fun x hx => ?_
  have : Module.Free _ _ := hx
  obtain ⟨r, hr, hr', _⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    x.asIdeal.primeCompl (LocalizedModule.mkLinearMap x.asIdeal.primeCompl M)
    (Localization.AtPrime x.asIdeal)
  exact ⟨basicOpen r, basicOpen_subset_freeLocus_iff.mpr inferInstance, (basicOpen r).2, hr⟩

variable (M) in
/-- The rank of `M` at the stalk of `p` is the rank of `Mₚ` as a `Rₚ`-module. -/
noncomputable
/--
Definition of `rankAtStalk` / `rankAtStalk` 的定义

English:
definition rankAtStalk
  signature: (p : PrimeSpectrum R)
  body: Module.finrank (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M)

中文:
定义 rankAtStalk
  签名: (p : 素谱 R)
  定义体: Module.finrank (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M)

Depends on / 依赖: AtPrime, Localization, Localization.AtPrime, LocalizedModule, Module, Module.finrank, asIdeal, finrank, p.asIdeal, p.asIdeal.primeCompl, primeCompl
-/
def rankAtStalk (p : PrimeSpectrum R) : Nat :=
  Module.finrank (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M)

/--
lemma `isLocallyConstant_rankAtStalk_freeLocus` / 引理 `isLocallyConstant_rankAtStalk_freeLocus`

English:
lemma isLocallyConstant_rankAtStalk_freeLocus
  given: [Module.FinitePresentation R M]
  proof: by
  refine (IsLocallyConstant.iff_exists_open _).mpr fun ⟨x, hx⟩ => ?_
  have : Module.Free _ _ := hx
  obtain ⟨f, hf, hf', hf''⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    x.asIdeal.primeCompl (LocalizedModule.mkLinearMap x.asIdeal.primeCompl M)
    (Localization.AtPrime x

中文:
引理 isLocallyConstant_rankAtStalk_freeLocus
  条件: [模.有限呈现 R M]
  证明: by
  refine (IsLocallyConstant.iff_exists_open _).mpr fun ⟨x, hx⟩ => ?_
  have : Module.Free _ _ := hx
  obtain ⟨f, hf, hf', hf''⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    x.asIdeal.primeCompl (LocalizedModule.mkLinearMap x.asIdeal.primeCompl M)
    (Localization.AtPrime x

Depends on / 依赖: Algebra, Algebra.algebraMapSubmonoid, AtPrime, FinitePresentation, IsLocallyConstant, IsLocallyConstant.iff_exists_open, Localization, Localization.AtPrime, LocalizedModule, LocalizedModule.mkLinearMap, Module, Module.FinitePresentation.exists_free_localizedModule_powers, Module.Free, Subtype, Subtype.val, algebraMapSubmonoid, asIdeal, basicOpen, continuous_subtype_val, exists_free_localizedModule_powers
-/
lemma isLocallyConstant_rankAtStalk_freeLocus [Module.FinitePresentation R M] :
    IsLocallyConstant (fun x : freeLocus R M => rankAtStalk M x.1) := by
  refine (IsLocallyConstant.iff_exists_open _).mpr fun ⟨x, hx⟩ => ?_
  have : Module.Free _ _ := hx
  obtain ⟨f, hf, hf', hf''⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    x.asIdeal.primeCompl (LocalizedModule.mkLinearMap x.asIdeal.primeCompl M)
    (Localization.AtPrime x.asIdeal)
  refine ⟨Subtype.val ⁻¹' basicOpen f, (basicOpen f).2.preimage continuous_subtype_val, hf, ?_⟩
  rintro ⟨p, hp''⟩ hp
  let p' := Algebra.algebraMapSubmonoid (Localization (.powers f)) p.asIdeal.primeCompl
  have hp' : Submonoid.powers f <= p.asIdeal.primeCompl := by
    simpa [Submonoid.powers_le, Ideal.primeCompl]
  let Rₚ := Localization.AtPrime p.asIdeal
  let Mₚ := LocalizedModule p.asIdeal.primeCompl M
  let : Algebra (Localization.Away f) Rₚ :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (.powers f) p.asIdeal.primeCompl hp'
  have : IsScalarTower R (Localization.Away f) Rₚ :=
    IsLocalization.localization_isScalarTower_of_submonoid_le ..
  let : Module (Localization.Away f) Mₚ := Module.compHom Mₚ (algebraMap _ Rₚ)
  have : IsScalarTower R (Localization.Away f) Mₚ :=
    ⟨fun r r' m => show algebraMap _ Rₚ (r • r') • m = _ by
      simp [Rₚ, Mₚ, Algebra.smul_def, ← IsScalarTower.algebraMap_apply, mul_smul]; rfl⟩
  have : IsScalarTower (Localization.Away f) Rₚ Mₚ :=
    ⟨fun r r' m => show _ = algebraMap _ Rₚ r • r' • m by rw [← mul_smul, ← Algebra.smul_def]⟩
  let l := (IsLocalizedModule.liftOfLE _ _ hp' (LocalizedModule.mkLinearMap (.powers f) M)
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)).extendScalarsOfIsLocalization (.powers f)
    (Localization.Away f)
  have : IsLocalization p' Rₚ :=
    IsLocalization.isLocalization_of_submonoid_le (Localization.Away f) Rₚ _ _ hp'
  have : IsLocalizedModule p.asIdeal.primeCompl (l.restrictScalars R) :=
    inferInstanceAs (IsLocalizedModule p.asIdeal.primeCompl
    ((IsLocalizedModule.liftOfLE _ _ hp' (LocalizedModule.mkLinearMap (.powers f) M)
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M))))
  have : IsLocalizedModule (Algebra.algebraMapSubmonoid _ p.asIdeal.primeCompl) l :=
      IsLocalizedModule.of_restrictScalars p.asIdeal.primeCompl ..
  have := Module.finrank_of_isLocalizedModule_of_free Rₚ p' l
  simp [Rₚ, rankAtStalk, this, hf'']

/--
lemma `isLocallyConstant_rankAtStalk` / 引理 `isLocallyConstant_rankAtStalk`

English:
lemma isLocallyConstant_rankAtStalk
  given: [Module.FinitePresentation R M] [Module.Flat R M]
  proof: by
  let e : freeLocus R M ≃ₜ PrimeSpectrum R :=
    (Homeomorph.setCongr freeLocus_eq_univ).trans (Homeomorph.Set.univ (PrimeSpectrum R))
  convert! isLocallyConstant_rankAtStalk_freeLocus.comp_continuous e.symm.continuous

@[simp]

中文:
引理 isLocallyConstant_rankAtStalk
  条件: [模.有限呈现 R M] [模.平坦 R M]
  证明: by
  let e : freeLocus R M ≃ₜ PrimeSpectrum R :=
    (Homeomorph.setCongr freeLocus_eq_univ).trans (Homeomorph.Set.univ (PrimeSpectrum R))
  convert! isLocallyConstant_rankAtStalk_freeLocus.comp_continuous e.symm.continuous

@[simp]

Depends on / 依赖: Homeomorph, Homeomorph.Set.univ, Homeomorph.setCongr, PrimeSpectrum, comp_continuous, continuous, convert, e.symm.continuous, freeLocus, freeLocus_eq_univ, isLocallyConstant_rankAtStalk_freeLocus, isLocallyConstant_rankAtStalk_freeLocus.comp_continuous, setCongr
-/
lemma isLocallyConstant_rankAtStalk [Module.FinitePresentation R M] [Module.Flat R M] :
    IsLocallyConstant (rankAtStalk (R := R) M) := by
  let e : freeLocus R M ≃ₜ PrimeSpectrum R :=
    (Homeomorph.setCongr freeLocus_eq_univ).trans (Homeomorph.Set.univ (PrimeSpectrum R))
  convert! isLocallyConstant_rankAtStalk_freeLocus.comp_continuous e.symm.continuous

@[simp]
/--
lemma `rankAtStalk_eq_zero_of_subsingleton` / 引理 `rankAtStalk_eq_zero_of_subsingleton`

English:
lemma rankAtStalk_eq_zero_of_subsingleton
  given: [Subsingleton M]
  proof: by
  ext p
  exact Module.finrank_zero_of_subsingleton

中文:
引理 rankAtStalk_eq_zero_of_subsingleton
  条件: [子单例 M]
  证明: by
  ext p
  exact Module.finrank_zero_of_subsingleton

Depends on / 依赖: Module, Module.finrank_zero_of_subsingleton, finrank_zero_of_subsingleton
-/
lemma rankAtStalk_eq_zero_of_subsingleton [Subsingleton M] :
    rankAtStalk (R := R) M = 0 := by
  ext p
  exact Module.finrank_zero_of_subsingleton

/--
lemma `nontrivial_of_rankAtStalk_pos` / 引理 `nontrivial_of_rankAtStalk_pos`

English:
lemma nontrivial_of_rankAtStalk_pos
  given: (h : 0 < rankAtStalk (R := R) M)
  proof: by
  by_contra! hn
  simp at h

中文:
引理 nontrivial_of_rankAtStalk_pos
  条件: (h : 0 < rankAtStalk (R := R) M)
  证明: by
  by_contra! hn
  simp at h
-/
lemma nontrivial_of_rankAtStalk_pos (h : 0 < rankAtStalk (R := R) M) :
    Nontrivial M := by
  by_contra! hn
  simp at h

/--
lemma `rankAtStalk_eq_of_equiv` / 引理 `rankAtStalk_eq_of_equiv`

English:
lemma rankAtStalk_eq_of_equiv
  given: {N : Type*} [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N)
  proof: by
  ext p
  exact IsLocalizedModule.mapEquiv p.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)
.finrank_eq (LocalizedModule.mkLinearMap p.asIdeal.primeCompl N) _ e

中文:
引理 rankAtStalk_eq_of_equiv
  条件: {N : 类型} [加法交换群 N] [模 R N] (e : M ≃ₗ[R] N)
  证明: by
  ext p
  exact IsLocalizedModule.mapEquiv p.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)
.finrank_eq (LocalizedModule.mkLinearMap p.asIdeal.primeCompl N) _ e

Depends on / 依赖: IsLocalizedModule, IsLocalizedModule.mapEquiv, LocalizedModule, LocalizedModule.mkLinearMap, asIdeal, finrank_eq, mapEquiv, mkLinearMap, p.asIdeal.primeCompl, primeCompl, rankAtStalk
-/
lemma rankAtStalk_eq_of_equiv {N : Type*} [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) :
    rankAtStalk (R := R) M = rankAtStalk N := by
  ext p
  exact IsLocalizedModule.mapEquiv p.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)
.finrank_eq (LocalizedModule.mkLinearMap p.asIdeal.primeCompl N) _ e

/-- If `M` is `R`-free, its rank at stalks is constant and agrees with the `R`-rank of `M`. -/
@[simp]
/--
lemma `rankAtStalk_eq_finrank_of_free` / 引理 `rankAtStalk_eq_finrank_of_free`

English:
lemma rankAtStalk_eq_finrank_of_free
  given: [Module.Free R M]
  proof: by
  ext p
  simp [rankAtStalk, finrank_of_isLocalizedModule_of_free _ p.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)]

中文:
引理 rankAtStalk_eq_finrank_of_free
  条件: [模.自由 R M]
  证明: by
  ext p
  simp [rankAtStalk, finrank_of_isLocalizedModule_of_free _ p.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)]

Depends on / 依赖: LocalizedModule, LocalizedModule.mkLinearMap, Module, Module.finrank, asIdeal, finrank, finrank_of_isLocalizedModule_of_free, mkLinearMap, p.asIdeal.primeCompl, primeCompl, rankAtStalk
-/
lemma rankAtStalk_eq_finrank_of_free [Module.Free R M] :
    rankAtStalk (R := R) M = Module.finrank R M := by
  ext p
  simp [rankAtStalk, finrank_of_isLocalizedModule_of_free _ p.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)]

/--
lemma `rankAtStalk_self` / 引理 `rankAtStalk_self`

English:
lemma rankAtStalk_self
  given: [Nontrivial R]
  statement: rankAtStalk (R := R) R = 1
  proof: by
  simp

中文:
引理 rankAtStalk_self
  条件: [非平凡 R]
  结论: rankAtStalk (R := R) R = 1
  证明: by
  simp
-/
lemma rankAtStalk_self [Nontrivial R] : rankAtStalk (R := R) R = 1 := by
  simp

open LocalizedModule Localization

/--
lemma `rankAtStalk_pi` / 引理 `rankAtStalk_pi`

English:
lemma rankAtStalk_pi
  statement: {ι : Type*} [Finite ι] (M : ι -> Type*)
  proof: by
  cases nonempty_fintype ι
  let f : (Π i, M i) ->ₗ[R] Π i, LocalizedModule p.asIdeal.primeCompl (M i) :=
    .pi (fun i => mkLinearMap p.asIdeal.primeCompl (M i) ∘ₗ LinearMap.proj i)
  let e : LocalizedModule p.asIdeal.primeCompl (Π i, M i) ≃ₗ[Localization.AtPrime p.asIdeal]
      Π i, Localized

中文:
引理 rankAtStalk_pi
  结论: {ι : 类型} [有限 ι] (M : ι -> 类型)
  证明: by
  cases nonempty_fintype ι
  let f : (Π i, M i) ->ₗ[R] Π i, LocalizedModule p.asIdeal.primeCompl (M i) :=
    .pi (fun i => mkLinearMap p.asIdeal.primeCompl (M i) ∘ₗ LinearMap.proj i)
  let e : LocalizedModule p.asIdeal.primeCompl (Π i, M i) ≃ₗ[Localization.AtPrime p.asIdeal]
      Π i, Localized

Depends on / 依赖: AtPrime, IsLocalizedModule, IsLocalizedModule.linearEquiv, LinearMap, LinearMap.proj, Localization, Localization.AtPrime, LocalizedModule, asIdeal, extendScalarsOfIsLocalization, linearEquiv, mkLinearMap, nonempty_fintype, p.asIdeal, p.asIdeal.primeCompl, primeCompl
-/
lemma rankAtStalk_pi {ι : Type*} [Finite ι] (M : ι -> Type*)
    [forall i, AddCommGroup (M i)] [forall i, Module R (M i)] [forall i, Module.Flat R (M i)]
    [forall i, Module.Finite R (M i)] (p : PrimeSpectrum R) :
    rankAtStalk (Π i, M i) p = ∑ᶠ i, rankAtStalk (M i) p := by
  cases nonempty_fintype ι
  let f : (Π i, M i) ->ₗ[R] Π i, LocalizedModule p.asIdeal.primeCompl (M i) :=
    .pi (fun i => mkLinearMap p.asIdeal.primeCompl (M i) ∘ₗ LinearMap.proj i)
  let e : LocalizedModule p.asIdeal.primeCompl (Π i, M i) ≃ₗ[Localization.AtPrime p.asIdeal]
      Π i, LocalizedModule p.asIdeal.primeCompl (M i) :=
    IsLocalizedModule.linearEquiv p.asIdeal.primeCompl
.extendScalarsOfIsLocalization p.asIdeal.primeCompl _ (mkLinearMap _ _) f
  have (i : ι) : Free (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl (M i)) :=
    free_of_flat_of_isLocalRing
  simp_rw [rankAtStalk, e.finrank_eq, Module.finrank_pi_fintype, finsum_eq_sum_of_fintype]

/--
lemma `rankAtStalk_eq_finrank_tensorProduct` / 引理 `rankAtStalk_eq_finrank_tensorProduct`

English:
lemma rankAtStalk_eq_finrank_tensorProduct
  given: (p : PrimeSpectrum R)
  proof: by
  let e : LocalizedModule p.asIdeal.primeCompl M ≃ₗ[Localization.AtPrime p.asIdeal]
      Localization.AtPrime p.asIdeal otimes[R] M :=
    LocalizedModule.equivTensorProduct p.asIdeal.primeCompl M
  rw [rankAtStalk]; rw [e.finrank_eq]

中文:
引理 rankAtStalk_eq_finrank_tensorProduct
  条件: (p : 素谱 R)
  证明: by
  let e : LocalizedModule p.asIdeal.primeCompl M ≃ₗ[Localization.AtPrime p.asIdeal]
      Localization.AtPrime p.asIdeal otimes[R] M :=
    LocalizedModule.equivTensorProduct p.asIdeal.primeCompl M
  rw [rankAtStalk]; rw [e.finrank_eq]

Depends on / 依赖: AtPrime, Localization, Localization.AtPrime, LocalizedModule, LocalizedModule.equivTensorProduct, asIdeal, e.finrank_eq, equivTensorProduct, finrank_eq, otimes, p.asIdeal, p.asIdeal.primeCompl, primeCompl, rankAtStalk
-/
lemma rankAtStalk_eq_finrank_tensorProduct (p : PrimeSpectrum R) :
    rankAtStalk M p =
      finrank (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal otimes[R] M) := by
  let e : LocalizedModule p.asIdeal.primeCompl M ≃ₗ[Localization.AtPrime p.asIdeal]
      Localization.AtPrime p.asIdeal otimes[R] M :=
    LocalizedModule.equivTensorProduct p.asIdeal.primeCompl M
  rw [rankAtStalk]; rw [e.finrank_eq]

variable [Flat R M] [Module.Finite R M]

attribute [local instance] free_of_flat_of_isLocalRing

/--
lemma `rankAtStalk_eq_zero_iff_notMem_support` / 引理 `rankAtStalk_eq_zero_iff_notMem_support`

English:
lemma rankAtStalk_eq_zero_iff_notMem_support
  given: (p : PrimeSpectrum R)
  proof: by
  rw [notMem_support_iff]
  refine ⟨fun h => ?_, fun h => Module.finrank_zero_of_subsingleton⟩
  apply subsingleton_of_rank_zero (R := Localization.AtPrime p.asIdeal)
  dsimp [rankAtStalk] at h
  simp [← finrank_eq_rank, h]

中文:
引理 rankAtStalk_eq_zero_iff_notMem_support
  条件: (p : 素谱 R)
  证明: by
  rw [notMem_support_iff]
  refine ⟨fun h => ?_, fun h => Module.finrank_zero_of_subsingleton⟩
  apply subsingleton_of_rank_zero (R := Localization.AtPrime p.asIdeal)
  dsimp [rankAtStalk] at h
  simp [← finrank_eq_rank, h]

Depends on / 依赖: AtPrime, Localization, Localization.AtPrime, Module, Module.finrank_zero_of_subsingleton, asIdeal, finrank_eq_rank, finrank_zero_of_subsingleton, notMem_support_iff, p.asIdeal, rankAtStalk, subsingleton_of_rank_zero
-/
lemma rankAtStalk_eq_zero_iff_notMem_support (p : PrimeSpectrum R) :
    rankAtStalk M p = 0 ↔ p ∉ support R M := by
  rw [notMem_support_iff]
  refine ⟨fun h => ?_, fun h => Module.finrank_zero_of_subsingleton⟩
  apply subsingleton_of_rank_zero (R := Localization.AtPrime p.asIdeal)
  dsimp [rankAtStalk] at h
  simp [← finrank_eq_rank, h]

/--
lemma `rankAtStalk_pos_iff_mem_support` / 引理 `rankAtStalk_pos_iff_mem_support`

English:
lemma rankAtStalk_pos_iff_mem_support
  given: (p : PrimeSpectrum R)
  proof: Nat.pos_iff_ne_zero.trans (rankAtStalk_eq_zero_iff_notMem_support _).not_left

中文:
引理 rankAtStalk_pos_iff_mem_support
  条件: (p : 素谱 R)
  证明: Nat.pos_iff_ne_zero.trans (rankAtStalk_eq_zero_iff_notMem_support _).not_left

Depends on / 依赖: Nat.pos_iff_ne_zero.trans, not_left, pos_iff_ne_zero, rankAtStalk_eq_zero_iff_notMem_support
-/
lemma rankAtStalk_pos_iff_mem_support (p : PrimeSpectrum R) :
    0 < rankAtStalk M p ↔ p in support R M :=
  Nat.pos_iff_ne_zero.trans (rankAtStalk_eq_zero_iff_notMem_support _).not_left

/--
lemma `rankAtStalk_eq_zero_iff_subsingleton` / 引理 `rankAtStalk_eq_zero_iff_subsingleton`

English:
lemma rankAtStalk_eq_zero_iff_subsingleton
  proof: by
  refine ⟨fun h => ?_, fun _ => rankAtStalk_eq_zero_of_subsingleton⟩
  simp_rw [← support_eq_empty_iff (R := R), Set.eq_empty_iff_forall_notMem]
  intro p
  rw [← rankAtStalk_eq_zero_iff_notMem_support]; rw [h]; rw [Pi.zero_apply]

中文:
引理 rankAtStalk_eq_zero_iff_subsingleton
  证明: by
  refine ⟨fun h => ?_, fun _ => rankAtStalk_eq_zero_of_subsingleton⟩
  simp_rw [← support_eq_empty_iff (R := R), Set.eq_empty_iff_forall_notMem]
  intro p
  rw [← rankAtStalk_eq_zero_iff_notMem_support]; rw [h]; rw [Pi.zero_apply]

Depends on / 依赖: Pi.zero_apply, Set.eq_empty_iff_forall_notMem, Subsingleton, eq_empty_iff_forall_notMem, rankAtStalk_eq_zero_iff_notMem_support, rankAtStalk_eq_zero_of_subsingleton, simp_rw, support_eq_empty_iff, zero_apply
-/
lemma rankAtStalk_eq_zero_iff_subsingleton :
    rankAtStalk (R := R) M = 0 ↔ Subsingleton M := by
  refine ⟨fun h => ?_, fun _ => rankAtStalk_eq_zero_of_subsingleton⟩
  simp_rw [← support_eq_empty_iff (R := R), Set.eq_empty_iff_forall_notMem]
  intro p
  rw [← rankAtStalk_eq_zero_iff_notMem_support]; rw [h]; rw [Pi.zero_apply]

variable (M) in
/--
lemma `rankAtStalk_prod` / 引理 `rankAtStalk_prod`

English:
lemma rankAtStalk_prod
  statement: (N : Type*) [AddCommGroup N] [Module R N]
  proof: by
  ext p
  let e : LocalizedModule p.asIdeal.primeCompl (M × N) ≃ₗ[Localization.AtPrime p.asIdeal]
      LocalizedModule p.asIdeal.primeCompl M × LocalizedModule p.asIdeal.primeCompl N :=
    IsLocalizedModule.linearEquiv p.asIdeal.primeCompl (mkLinearMap _ _)
.extendScalarsOfIsLocalization (.prod

中文:
引理 rankAtStalk_prod
  结论: (N : 类型) [加法交换群 N] [模 R N]
  证明: by
  ext p
  let e : LocalizedModule p.asIdeal.primeCompl (M × N) ≃ₗ[Localization.AtPrime p.asIdeal]
      LocalizedModule p.asIdeal.primeCompl M × LocalizedModule p.asIdeal.primeCompl N :=
    IsLocalizedModule.linearEquiv p.asIdeal.primeCompl (mkLinearMap _ _)
.extendScalarsOfIsLocalization (.prod

Depends on / 依赖: AtPrime, IsLocalizedModule, IsLocalizedModule.linearEquiv, Localization, Localization.AtPrime, LocalizedModule, asIdeal, e.finrank_eq, extendScalarsOfIsLocalization, finrank_eq, linearEquiv, mkLinearMap, p.asIdeal, p.asIdeal.primeCompl, primeCompl, prodMap, rankAtStalk
-/
lemma rankAtStalk_prod (N : Type*) [AddCommGroup N] [Module R N]
    [Module.Flat R N] [Module.Finite R N] :
    rankAtStalk (R := R) (M × N) = rankAtStalk M + rankAtStalk N := by
  ext p
  let e : LocalizedModule p.asIdeal.primeCompl (M × N) ≃ₗ[Localization.AtPrime p.asIdeal]
      LocalizedModule p.asIdeal.primeCompl M × LocalizedModule p.asIdeal.primeCompl N :=
    IsLocalizedModule.linearEquiv p.asIdeal.primeCompl (mkLinearMap _ _)
.extendScalarsOfIsLocalization (.prodMap (mkLinearMap _ M) (mkLinearMap _ N))
      p.asIdeal.primeCompl _
  simp [rankAtStalk, e.finrank_eq]

/--
lemma `rankAtStalk_baseChange` / 引理 `rankAtStalk_baseChange`

English:
lemma rankAtStalk_baseChange
  given: {S : Type*} [CommRing S] [Algebra R S] (p : PrimeSpectrum S)
  proof: by
  let q : PrimeSpectrum R := p.comap (algebraMap R S)
  let := Localization.AtPrime.algebraOfLiesOver q.asIdeal p.asIdeal
  let e : LocalizedModule p.asIdeal.primeCompl (S otimes[R] M) ≃ₗ[Localization.AtPrime p.asIdeal]
      Localization.AtPrime p.asIdeal otimes[Localization.AtPrime q.asIdeal]
 

中文:
引理 rankAtStalk_baseChange
  条件: {S : 类型} [交换环 S] [代数 R S] (p : 素谱 S)
  证明: by
  let q : PrimeSpectrum R := p.comap (algebraMap R S)
  let := Localization.AtPrime.algebraOfLiesOver q.asIdeal p.asIdeal
  let e : LocalizedModule p.asIdeal.primeCompl (S otimes[R] M) ≃ₗ[Localization.AtPrime p.asIdeal]
      Localization.AtPrime p.asIdeal otimes[Localization.AtPrime q.asIdeal]
 

Depends on / 依赖: AlgebraTensorMod, AlgebraTensorModule, AlgebraTensorModule.cancelBaseChange, AtPrime, Localization, Localization.AtPrime, Localization.AtPrime.algebraOfLiesOver, LocalizedModule, LocalizedModule.equivTensorProduct, PrimeSpectrum, algebraMap, algebraOfLiesOver, asIdeal, cancelBaseChange, equivTensorProduct, otimes, p.asIdeal, p.asIdeal.primeCompl, p.comap, primeCompl
-/
lemma rankAtStalk_baseChange {S : Type*} [CommRing S] [Algebra R S] (p : PrimeSpectrum S) :
    rankAtStalk (S otimes[R] M) p = rankAtStalk M (p.comap (algebraMap R S)) := by
  let q : PrimeSpectrum R := p.comap (algebraMap R S)
  let := Localization.AtPrime.algebraOfLiesOver q.asIdeal p.asIdeal
  let e : LocalizedModule p.asIdeal.primeCompl (S otimes[R] M) ≃ₗ[Localization.AtPrime p.asIdeal]
      Localization.AtPrime p.asIdeal otimes[Localization.AtPrime q.asIdeal]
        LocalizedModule q.asIdeal.primeCompl M :=
    LocalizedModule.equivTensorProduct _ _ ≪≫ₗ
      (AlgebraTensorModule.cancelBaseChange R S _ _ M) ≪≫ₗ
      (AlgebraTensorModule.cancelBaseChange R _ _ _ M).symm ≪≫ₗ
      (AlgebraTensorModule.congr (LinearEquiv.refl _ _)
        (LocalizedModule.equivTensorProduct _ M).symm)
  rw [rankAtStalk]; rw [e.finrank_eq]
  apply Module.finrank_baseChange

/--
lemma `rankAtStalk_isBaseChange` / 引理 `rankAtStalk_isBaseChange`

English:
lemma rankAtStalk_isBaseChange
  statement: {S Mₛ : Type*} [CommRing S] [Algebra R S] [AddCommGroup Mₛ]
  proof: by
  simp [rankAtStalk_eq_of_equiv hf.equiv.symm, rankAtStalk_baseChange]

中文:
引理 rankAtStalk_isBaseChange
  结论: {S Mₛ : 类型} [交换环 S] [代数 R S] [加法交换群 Mₛ]
  证明: by
  simp [rankAtStalk_eq_of_equiv hf.equiv.symm, rankAtStalk_baseChange]

Depends on / 依赖: hf.equiv.symm, rankAtStalk_baseChange, rankAtStalk_eq_of_equiv
-/
lemma rankAtStalk_isBaseChange {S Mₛ : Type*} [CommRing S] [Algebra R S] [AddCommGroup Mₛ]
    [Module R Mₛ] [Module S Mₛ] [IsScalarTower R S Mₛ] {f : M ->ₗ[R] Mₛ} (hf : IsBaseChange S f)
    (p : PrimeSpectrum S) : rankAtStalk Mₛ p = rankAtStalk M (p.comap (algebraMap R S)) := by
  simp [rankAtStalk_eq_of_equiv hf.equiv.symm, rankAtStalk_baseChange]

variable (M) in
/--
lemma `rankAtStalk_eq_of_le_of_finite_of_flat` / 引理 `rankAtStalk_eq_of_le_of_finite_of_flat`

English:
lemma rankAtStalk_eq_of_le_of_finite_of_flat
  given: {p q : PrimeSpectrum R} (hpq : p <= q)
  proof: by
  let S := Localization.AtPrime q.asIdeal
  obtain ⟨P, rfl⟩ : p in Set.range (PrimeSpectrum.comap (algebraMap R S)) := by
    rw [PrimeSpectrum.localization_comap_range S q.asIdeal.primeCompl]
    exact disjoint_compl_left_iff.mpr hpq
  rw [← rankAtStalk_isBaseChange (LocalizedModule.isBaseChange

中文:
引理 rankAtStalk_eq_of_le_of_finite_of_flat
  条件: {p q : 素谱 R} (hpq : p <= q)
  证明: by
  let S := Localization.AtPrime q.asIdeal
  obtain ⟨P, rfl⟩ : p in Set.range (PrimeSpectrum.comap (algebraMap R S)) := by
    rw [PrimeSpectrum.localization_comap_range S q.asIdeal.primeCompl]
    exact disjoint_compl_left_iff.mpr hpq
  rw [← rankAtStalk_isBaseChange (LocalizedModule.isBaseChange

Depends on / 依赖: AtPrime, Localization, Localization.AtPrime, LocalizedModule, LocalizedModule.isBaseChange, PrimeSpectrum, PrimeSpectrum.comap, PrimeSpectrum.localization_comap_range, Set.range, algebraMap, asIdeal, disjoint_compl_left_iff, disjoint_compl_left_iff.mpr, isBaseChange, localization_comap_range, primeCompl, q.asIdeal, q.asIdeal.primeCompl, rankAtStalk, rankAtStalk_eq_finrank_of_free
-/
lemma rankAtStalk_eq_of_le_of_finite_of_flat {p q : PrimeSpectrum R} (hpq : p <= q) :
    rankAtStalk M p = rankAtStalk M q := by
  let S := Localization.AtPrime q.asIdeal
  obtain ⟨P, rfl⟩ : p in Set.range (PrimeSpectrum.comap (algebraMap R S)) := by
    rw [PrimeSpectrum.localization_comap_range S q.asIdeal.primeCompl]
    exact disjoint_compl_left_iff.mpr hpq
  rw [← rankAtStalk_isBaseChange (LocalizedModule.isBaseChange q.asIdeal.primeCompl M)]; rw [rankAtStalk_eq_finrank_of_free]
  simp [rankAtStalk]

variable (M) in
/--
lemma `rankAtStalk_eq_of_le_of_finite_of_flat'` / 引理 `rankAtStalk_eq_of_le_of_finite_of_flat'`

English:
lemma rankAtStalk_eq_of_le_of_finite_of_flat'
  statement: {p q : Ideal R} [hp : p.IsPrime] [hq : q.IsPrime]
  proof: rankAtStalk_eq_of_le_of_finite_of_flat M hpq

中文:
引理 rankAtStalk_eq_of_le_of_finite_of_flat'
  结论: {p q : 理想 R} [hp : p.是素] [hq : q.是素]
  证明: rankAtStalk_eq_of_le_of_finite_of_flat M hpq

Depends on / 依赖: rankAtStalk_eq_of_le_of_finite_of_flat
-/
lemma rankAtStalk_eq_of_le_of_finite_of_flat' {p q : Ideal R} [hp : p.IsPrime] [hq : q.IsPrime]
    (hpq : p <= q) : rankAtStalk M ⟨p, hp⟩ = rankAtStalk M ⟨q, hq⟩ :=
  rankAtStalk_eq_of_le_of_finite_of_flat M hpq

/--
lemma `rankAtStalk_tensorProduct` / 引理 `rankAtStalk_tensorProduct`

English:
lemma rankAtStalk_tensorProduct
  statement: (N : Type*) [AddCommGroup N] [Module R N] [Module.Finite R N]
  proof: by
  ext p
  let e : Localization.AtPrime p.asIdeal otimes[R] (M otimes[R] N) ≃ₗ[Localization.AtPrime p.asIdeal]
      (Localization.AtPrime p.asIdeal otimes[R] M) otimes[Localization.AtPrime p.asIdeal]
        (Localization.AtPrime p.asIdeal otimes[R] N) :=
    (AlgebraTensorModule.assoc _ _ _ _ _ 

中文:
引理 rankAtStalk_tensorProduct
  结论: (N : 类型) [加法交换群 N] [模 R N] [模.有限 R N]
  证明: by
  ext p
  let e : Localization.AtPrime p.asIdeal otimes[R] (M otimes[R] N) ≃ₗ[Localization.AtPrime p.asIdeal]
      (Localization.AtPrime p.asIdeal otimes[R] M) otimes[Localization.AtPrime p.asIdeal]
        (Localization.AtPrime p.asIdeal otimes[R] N) :=
    (AlgebraTensorModule.assoc _ _ _ _ _ 

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.assoc, AlgebraTensorModule.cancelBaseChange, AtPrime, Localization, Localization.AtPrime, asIdeal, cancelBaseChange, e.finrank_eq, finrank_eq, finrank_tensorProduct, otimes, p.asIdeal, rankAtS, rankAtStalk_eq_finrank_tensorProduct
-/
lemma rankAtStalk_tensorProduct (N : Type*) [AddCommGroup N] [Module R N] [Module.Finite R N]
    [Module.Flat R N] : rankAtStalk (M otimes[R] N) = rankAtStalk M * rankAtStalk (R := R) N := by
  ext p
  let e : Localization.AtPrime p.asIdeal otimes[R] (M otimes[R] N) ≃ₗ[Localization.AtPrime p.asIdeal]
      (Localization.AtPrime p.asIdeal otimes[R] M) otimes[Localization.AtPrime p.asIdeal]
        (Localization.AtPrime p.asIdeal otimes[R] N) :=
    (AlgebraTensorModule.assoc _ _ _ _ _ _).symm ≪≫ₗ
      (AlgebraTensorModule.cancelBaseChange _ _ _ _ _).symm
  rw [rankAtStalk_eq_finrank_tensorProduct]; rw [e.finrank_eq]; rw [finrank_tensorProduct]; rw [← rankAtStalk_eq_finrank_tensorProduct]; rw [← rankAtStalk_eq_finrank_tensorProduct]; rw [Pi.mul_apply]

/--
lemma `rankAtStalk_tensorProduct_of_isScalarTower` / 引理 `rankAtStalk_tensorProduct_of_isScalarTower`

English:
lemma rankAtStalk_tensorProduct_of_isScalarTower
  statement: {S : Type*} [CommRing S] [Algebra R S]
  proof: by
  simp [rankAtStalk_eq_of_equiv (AlgebraTensorModule.cancelBaseChange R S S N M).symm,
    rankAtStalk_tensorProduct, rankAtStalk_baseChange]

中文:
引理 rankAtStalk_tensorProduct_of_isScalarTower
  结论: {S : 类型} [交换环 S] [代数 R S]
  证明: by
  simp [rankAtStalk_eq_of_equiv (AlgebraTensorModule.cancelBaseChange R S S N M).symm,
    rankAtStalk_tensorProduct, rankAtStalk_baseChange]

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.cancelBaseChange, cancelBaseChange, rankAtStalk_baseChange, rankAtStalk_eq_of_equiv, rankAtStalk_tensorProduct
-/
lemma rankAtStalk_tensorProduct_of_isScalarTower {S : Type*} [CommRing S] [Algebra R S]
    (N : Type*) [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    [Module.Finite S N] [Module.Flat S N] (p : PrimeSpectrum S) :
    rankAtStalk (N otimes[R] M) p = rankAtStalk N p * rankAtStalk M (p.comap (algebraMap R S)) := by
  simp [rankAtStalk_eq_of_equiv (AlgebraTensorModule.cancelBaseChange R S S N M).symm,
    rankAtStalk_tensorProduct, rankAtStalk_baseChange]

/--
lemma `rankAtStalk_eq` / 引理 `rankAtStalk_eq`

English:
lemma rankAtStalk_eq
  given: (p : PrimeSpectrum R)
  proof: by
  let k := p.asIdeal.ResidueField
  let e : k otimes[Localization.AtPrime p.asIdeal] (Localization.AtPrime p.asIdeal otimes[R] M) ≃ₗ[k]
      k otimes[R] M :=
    AlgebraTensorModule.cancelBaseChange _ _ _ _ _
  rw [← e.finrank_eq]; rw [finrank_baseChange]; rw [rankAtStalk_eq_finrank_tensorProduc

中文:
引理 rankAtStalk_eq
  条件: (p : 素谱 R)
  证明: by
  let k := p.asIdeal.ResidueField
  let e : k otimes[Localization.AtPrime p.asIdeal] (Localization.AtPrime p.asIdeal otimes[R] M) ≃ₗ[k]
      k otimes[R] M :=
    AlgebraTensorModule.cancelBaseChange _ _ _ _ _
  rw [← e.finrank_eq]; rw [finrank_baseChange]; rw [rankAtStalk_eq_finrank_tensorProduc

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.cancelBaseChange, AtPrime, Localization, Localization.AtPrime, ResidueField, asIdeal, cancelBaseChange, e.finrank_eq, finrank_baseChange, finrank_eq, otimes, p.asIdeal, p.asIdeal.ResidueField, rankAtStalk_eq_finrank_tensorProduct
-/
lemma rankAtStalk_eq (p : PrimeSpectrum R) :
    rankAtStalk M p = finrank p.asIdeal.ResidueField (p.asIdeal.Fiber M) := by
  let k := p.asIdeal.ResidueField
  let e : k otimes[Localization.AtPrime p.asIdeal] (Localization.AtPrime p.asIdeal otimes[R] M) ≃ₗ[k]
      k otimes[R] M :=
    AlgebraTensorModule.cancelBaseChange _ _ _ _ _
  rw [← e.finrank_eq]; rw [finrank_baseChange]; rw [rankAtStalk_eq_finrank_tensorProduct]

/--
lemma `_root_.Ideal.finrank_fiber_eq_rankAtStalk` / 引理 `_root_.Ideal.finrank_fiber_eq_rankAtStalk`

English:
lemma _root_.Ideal.finrank_fiber_eq_rankAtStalk
  given: (p : Ideal R) [hp : p.IsPrime]
  proof: (rankAtStalk_eq ⟨p, hp⟩).symm

中文:
引理 _root_.理想.finrank_fiber_eq_rankAtStalk
  条件: (p : 理想 R) [hp : p.是素]
  证明: (rankAtStalk_eq ⟨p, hp⟩).symm

Depends on / 依赖: rankAtStalk_eq
-/
lemma _root_.Ideal.finrank_fiber_eq_rankAtStalk (p : Ideal R) [hp : p.IsPrime] :
    finrank p.ResidueField (p.Fiber M) = rankAtStalk M ⟨p, hp⟩ :=
  (rankAtStalk_eq ⟨p, hp⟩).symm

/--
lemma `_root_.Ideal.finrank_fiber_eq_finrank` / 引理 `_root_.Ideal.finrank_fiber_eq_finrank`

English:
lemma _root_.Ideal.finrank_fiber_eq_finrank
  given: [IsDomain R] (p : Ideal R) [p.IsPrime]
  proof: by
  let K := FractionRing R
  let Rp := Localization.AtPrime p
  let Mp := LocalizedModule.AtPrime p M
  rw [p.finrank_fiber_eq_rankAtStalk]; rw [rankAtStalk]; rw [← (isBaseChange Rp Mp K).finrank_eq]; rw [(((LocalizedModule.equivTensorProduct p.primeCompl M).baseChange Rp K Mp _)).finrank_eq]; rw 

中文:
引理 _root_.理想.finrank_fiber_eq_finrank
  条件: [是整环 R] (p : 理想 R) [p.是素]
  证明: by
  let K := FractionRing R
  let Rp := Localization.AtPrime p
  let Mp := LocalizedModule.AtPrime p M
  rw [p.finrank_fiber_eq_rankAtStalk]; rw [rankAtStalk]; rw [← (isBaseChange Rp Mp K).finrank_eq]; rw [(((LocalizedModule.equivTensorProduct p.primeCompl M).baseChange Rp K Mp _)).finrank_eq]; rw 

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.cancelBaseChange, AtPrime, FractionRing, Localization, Localization.AtPrime, LocalizedModule, LocalizedModule.AtPrime, LocalizedModule.equivTensorProduct, baseChange, cancelBaseChange, equivTensorProduct, finrank_eq, finrank_fiber_eq_rankAtStalk, isBaseChange, p.finrank_fiber_eq_rankAtStalk, p.primeCompl, primeCompl, rankAtStalk
-/
lemma _root_.Ideal.finrank_fiber_eq_finrank [IsDomain R] (p : Ideal R) [p.IsPrime] :
    finrank p.ResidueField (p.Fiber M) = finrank R M := by
  let K := FractionRing R
  let Rp := Localization.AtPrime p
  let Mp := LocalizedModule.AtPrime p M
  rw [p.finrank_fiber_eq_rankAtStalk]; rw [rankAtStalk]; rw [← (isBaseChange Rp Mp K).finrank_eq]; rw [(((LocalizedModule.equivTensorProduct p.primeCompl M).baseChange Rp K Mp _)).finrank_eq]; rw [(AlgebraTensorModule.cancelBaseChange R Rp K K M).finrank_eq]; rw [(isBaseChange R M K).finrank_eq]

end Module
