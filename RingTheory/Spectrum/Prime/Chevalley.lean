/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.Spectrum.Prime.ChevalleyComplexity

/-!
# Chevalley's theorem

In this file we provide the usual (algebraic) version of Chevalley's theorem.
For the proof see `Mathlib/RingTheory/Spectrum/Prime/ChevalleyComplexity.lean`.
-/

public section

variable {R S : Type*} [CommRing R] [CommRing S]

open Function Localization MvPolynomial Polynomial TensorProduct PrimeSpectrum Topology
open scoped Pointwise

namespace PrimeSpectrum

/--
lemma `isConstructible_comap_C` / 引理 `isConstructible_comap_C`

English:
lemma isConstructible_comap_C
  proof: by
  obtain ⟨S, rfl⟩ := exists_constructibleSetData_iff.mpr hs
  obtain ⟨T, hT, -⟩ := ChevalleyThm.chevalley_polynomialC _ Submodule.mem_top S (by simp)
  rw [hT]
  exact T.isConstructible_toSet

中文:
引理 isConstructible_comap_C
  证明: by
  obtain ⟨S, rfl⟩ := exists_constructibleSetData_iff.mpr hs
  obtain ⟨T, hT, -⟩ := ChevalleyThm.chevalley_polynomialC _ Submodule.mem_top S (by simp)
  rw [hT]
  exact T.isConstructible_toSet

Depends on / 依赖: ChevalleyThm, ChevalleyThm.chevalley_polynomialC, Submodule, Submodule.mem_top, T.isConstructible_toSet, chevalley_polynomialC, exists_constructibleSetData_iff, exists_constructibleSetData_iff.mpr, isConstructible_toSet, mem_top
-/
lemma isConstructible_comap_C
    {s : Set (PrimeSpectrum (Polynomial R))} (hs : IsConstructible s) :
    IsConstructible (comap Polynomial.C '' s) := by
  obtain ⟨S, rfl⟩ := exists_constructibleSetData_iff.mpr hs
  obtain ⟨T, hT, -⟩ := ChevalleyThm.chevalley_polynomialC _ Submodule.mem_top S (by simp)
  rw [hT]
  exact T.isConstructible_toSet

/--
lemma `isConstructible_comap_image` / 引理 `isConstructible_comap_image`

English:
lemma isConstructible_comap_image
  proof: by
  refine hf.polynomial_induction
    (fun _ _ _ _ f => forall s, IsConstructible s -> IsConstructible (comap f '' s))
    (fun _ _ _ _ f => forall s, IsConstructible s -> IsConstructible (comap f '' s))
    (fun _ _ _ => isConstructible_comap_C) ?_ ?_ f s hs
  · intro R _ S _ f hf hf' s hs
    re

中文:
引理 isConstructible_comap_image
  证明: by
  refine hf.polynomial_induction
    (fun _ _ _ _ f => forall s, IsConstructible s -> IsConstructible (comap f '' s))
    (fun _ _ _ _ f => forall s, IsConstructible s -> IsConstructible (comap f '' s))
    (fun _ _ _ => isConstructible_comap_C) ?_ ?_ f s hs
  · intro R _ S _ f hf hf' s hs
    re

Depends on / 依赖: IsConstructible, hf.polynomial_induction, hs.image_of_isClosedEmbedding, image_of_isClosedEmbedding, isClosedEmbedding_comap_of_surjective, isConstructible_comap_C, isRetrocompact_zeroLocus_compl_of_fg, polynomial_induction, range_comap_of_surjective
-/
lemma isConstructible_comap_image
    {f : R ->+* S} (hf : f.FinitePresentation)
    {s : Set (PrimeSpectrum S)} (hs : IsConstructible s) :
    IsConstructible (comap f '' s) := by
  refine hf.polynomial_induction
    (fun _ _ _ _ f => forall s, IsConstructible s -> IsConstructible (comap f '' s))
    (fun _ _ _ _ f => forall s, IsConstructible s -> IsConstructible (comap f '' s))
    (fun _ _ _ => isConstructible_comap_C) ?_ ?_ f s hs
  · intro R _ S _ f hf hf' s hs
    refine hs.image_of_isClosedEmbedding (isClosedEmbedding_comap_of_surjective _ f hf) ?_
    rw [range_comap_of_surjective _ f hf]
    exact isRetrocompact_zeroLocus_compl_of_fg hf'
  · intro R _ S _ T _ f g H₁ H₂ s hs
    simp only [comap_comp, Set.image_comp]
    exact H₁ _ (H₂ _ hs)

/--
lemma `isConstructible_range_comap` / 引理 `isConstructible_range_comap`

English:
lemma isConstructible_range_comap
  given: {f : R ->+* S} (hf : f.FinitePresentation)
  proof: Set.image_univ ▸ isConstructible_comap_image hf .univ

@[stacks 00I1]

中文:
引理 isConstructible_range_comap
  条件: {f : R ->+* S} (hf : f.有限呈现)
  证明: Set.image_univ ▸ isConstructible_comap_image hf .univ

@[stacks 00I1]

Depends on / 依赖: Set.image_univ, image_univ, isConstructible_comap_image
-/
lemma isConstructible_range_comap {f : R ->+* S} (hf : f.FinitePresentation) :
    IsConstructible (Set.range <| comap f) :=
  Set.image_univ ▸ isConstructible_comap_image hf .univ

@[stacks 00I1]
/--
lemma `isOpenMap_comap_of_hasGoingDown_of_finitePresentation` / 引理 `isOpenMap_comap_of_hasGoingDown_of_finitePresentation`

English:
lemma isOpenMap_comap_of_hasGoingDown_of_finitePresentation
  proof: by
  rw [isBasis_basic_opens.isOpenMap_iff]
  rintro _ ⟨_, ⟨f, rfl⟩, rfl⟩
  exact isOpen_of_stableUnderGeneralization_of_isConstructible
    ((basicOpen f).2.stableUnderGeneralization.image
      (Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap.mp ‹_›))
    (isConstructible_comap_image (

中文:
引理 isOpenMap_comap_of_hasGoingDown_of_finitePresentation
  证明: by
  rw [isBasis_basic_opens.isOpenMap_iff]
  rintro _ ⟨_, ⟨f, rfl⟩, rfl⟩
  exact isOpen_of_stableUnderGeneralization_of_isConstructible
    ((basicOpen f).2.stableUnderGeneralization.image
      (Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap.mp ‹_›))
    (isConstructible_comap_image (

Depends on / 依赖: Algebra, Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap.mp, HasGoingDown, RingHom, RingHom.finitePresentation_algebraMap.mpr, basicOpen, finitePresentation_algebraMap, iff_generalizingMap_primeSpectrumComap, isBasis_basic_opens, isBasis_basic_opens.isOpenMap_iff, isConstructible_basicOpen, isConstructible_comap_image, isOpenMap_iff, isOpen_of_stableUnderGeneralization_of_isConstructible, stableUnderGeneralization, stableUnderGeneralization.image
-/
lemma isOpenMap_comap_of_hasGoingDown_of_finitePresentation
    [Algebra R S] [Algebra.HasGoingDown R S] [Algebra.FinitePresentation R S] :
    IsOpenMap (comap (algebraMap R S)) := by
  rw [isBasis_basic_opens.isOpenMap_iff]
  rintro _ ⟨_, ⟨f, rfl⟩, rfl⟩
  exact isOpen_of_stableUnderGeneralization_of_isConstructible
    ((basicOpen f).2.stableUnderGeneralization.image
      (Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap.mp ‹_›))
    (isConstructible_comap_image (RingHom.finitePresentation_algebraMap.mpr ‹_›)
      isConstructible_basicOpen)

open TensorProduct in
@[stacks 037G]
/--
theorem `isOpenMap_comap_algebraMap_tensorProduct_of_field` / 定理 `isOpenMap_comap_algebraMap_tensorProduct_of_field`

English:
theorem isOpenMap_comap_algebraMap_tensorProduct_of_field
  proof: by
  intro U hU
  wlog hU' : exists f, U = SetLike.coe (basicOpen f) generalizing U
  · rw [eq_biUnion_of_isOpen hU, Set.image_iUnion₂]
    exact isOpen_iUnion fun _ => isOpen_iUnion fun _ => this _ (basicOpen _).isOpen ⟨_, rfl⟩
  obtain ⟨f, rfl⟩ := hU'
  obtain ⟨B', hB, f, rfl⟩ := exists_fg_and_mem

中文:
定理 isOpenMap_comap_algebraMap_tensorProduct_of_field
  证明: by
  intro U hU
  wlog hU' : exists f, U = SetLike.coe (basicOpen f) generalizing U
  · rw [eq_biUnion_of_isOpen hU, Set.image_iUnion₂]
    exact isOpen_iUnion fun _ => isOpen_iUnion fun _ => this _ (basicOpen _).isOpen ⟨_, rfl⟩
  obtain ⟨f, rfl⟩ := hU'
  obtain ⟨B', hB, f, rfl⟩ := exists_fg_and_mem

Depends on / 依赖: Algebra, Algebra.FinitePresentation, Algebra.FinitePresentation.of_finiteType.mp, FinitePresentation, Set.image_iUnion, SetLike, SetLike.coe, basicOpen, convert, eq_biUnion_of_isOpen, exists_fg_and_mem_baseChange, fg_top, fg_top.mpr, generalizing, isOpen, isOpenMap_comap_of_hasGoingDown_of_finitePresentation, isOpen_iUnion, of_finiteType, otimes
-/
theorem isOpenMap_comap_algebraMap_tensorProduct_of_field
    {K A B : Type*} [Field K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B] :
    IsOpenMap (PrimeSpectrum.comap (algebraMap A (A otimes[K] B))) := by
  intro U hU
  wlog hU' : exists f, U = SetLike.coe (basicOpen f) generalizing U
  · rw [eq_biUnion_of_isOpen hU, Set.image_iUnion₂]
    exact isOpen_iUnion fun _ => isOpen_iUnion fun _ => this _ (basicOpen _).isOpen ⟨_, rfl⟩
  obtain ⟨f, rfl⟩ := hU'
  obtain ⟨B', hB, f, rfl⟩ := exists_fg_and_mem_baseChange f
  have : Algebra.FinitePresentation K B' :=
    Algebra.FinitePresentation.of_finiteType.mp ⟨B'.fg_top.mpr hB⟩
  convert!
    isOpenMap_comap_of_hasGoingDown_of_finitePresentation (R := A) (S := A otimes[K] B') _
      (basicOpen f).isOpen using 1
  ext x
  rw [PrimeSpectrum.mem_image_comap_basicOpen]; rw [PrimeSpectrum.mem_image_comap_basicOpen]; rw [not_iff_not]
  let ψ := Algebra.TensorProduct.map
    (Algebra.TensorProduct.map (.id A A) B'.val) (.id A x.asIdeal.ResidueField)
  have hψeq : ψ = (Algebra.TensorProduct.comm _ _ _ |>.toAlgHom.comp <|
.symm.toAlgHom.comp Algebra.TensorProduct.cancelBaseChange K A A _ B
.comp Algebra.TensorProduct.map (.id _ _) B'.val
.toAlgHom.comp Algebra.TensorProduct.cancelBaseChange K A A _ B'
    (Algebra.TensorProduct.comm _ _ _).toAlgHom) := by ext; simp [ψ]
  have hψ : Function.Injective ψ := by
    rw [hψeq]
    dsimp
    simp_rw [EmbeddingLike.comp_injective, ← Function.comp_assoc, EquivLike.injective_comp]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
  rw [← IsNilpotent.map_iff hψ]
  rfl

end PrimeSpectrum
