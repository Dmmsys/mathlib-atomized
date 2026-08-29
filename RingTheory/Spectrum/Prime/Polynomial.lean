/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.LinearAlgebra.Eigenspace.Zero
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!

# Prime spectrum of (multivariate) polynomials

Also see `AlgebraicGeometry/AffineSpace` for the affine space over arbitrary schemes.

## Main results
- `isNilpotent_tensor_residueField_iff`:
  If `A` is a finite free `R`-algebra, then `f : A` is nilpotent on `κ(𝔭) ⊗ A` for some
  prime `𝔭 ◃ R` if and only if every non-leading coefficient of `charpoly(f)` is in `𝔭`.
- `Polynomial.exists_image_comap_of_monic`:
  If `g : R[X]` is monic, the image of `Z(g) ∩ D(f) : Spec R[X]` in `Spec R` is compact open.
- `Polynomial.isOpenMap_comap_C`: The structure map `Spec R[X] → Spec R` is an open map.
- `MvPolynomial.isOpenMap_comap_C`:
  The structure map `Spec (MvPolynomial σ R) → Spec R` is an open map.

-/

public section

open Polynomial TensorProduct PrimeSpectrum

variable {R M A} [CommRing R] [AddCommGroup M] [Module R M] [CommRing A] [Algebra R A]

/--
lemma `isNilpotent_tensor_residueField_iff` / 引理 `isNilpotent_tensor_residueField_iff`

English:
lemma isNilpotent_tensor_residueField_iff
  proof: by
  cases subsingleton_or_nontrivial R
  · have := (algebraMap R (A otimes[R] I.ResidueField)).codomain_trivial
    simp [Subsingleton.elim I ⊤, Subsingleton.elim (f otimesₜ[R] (1 : I.ResidueField)) 0]
  have : Module.finrank I.ResidueField (I.ResidueField otimes[R] A) = Module.finrank R A := by
  

中文:
引理 isNilpotent_tensor_residueField_iff
  证明: by
  cases subsingleton_or_nontrivial R
  · have := (algebraMap R (A otimes[R] I.ResidueField)).codomain_trivial
    simp [Subsingleton.elim I ⊤, Subsingleton.elim (f otimesₜ[R] (1 : I.ResidueField)) 0]
  have : Module.finrank I.ResidueField (I.ResidueField otimes[R] A) = Module.finrank R A := by
  

Depends on / 依赖: Algebra, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.comm, I.ResidueField, IsNilpotent, IsNilpotent.map_iff, Module, Module.finrank, Module.finrank_self, Module.finrank_tensorProduct, ResidueField, Subsingleton, Subsingleton.elim, TensorProduct, algebraMap, algebraMap_apply, codomain_trivial, finrank, finrank_self, finrank_tensorProduct
-/
lemma isNilpotent_tensor_residueField_iff
    [Module.Free R A] [Module.Finite R A] (f : A) (I : Ideal R) [I.IsPrime] :
    IsNilpotent (algebraMap A (A otimes[R] I.ResidueField) f) ↔
      forall i < Module.finrank R A, (Algebra.lmul R A f).charpoly.coeff i in I := by
  cases subsingleton_or_nontrivial R
  · have := (algebraMap R (A otimes[R] I.ResidueField)).codomain_trivial
    simp [Subsingleton.elim I ⊤, Subsingleton.elim (f otimesₜ[R] (1 : I.ResidueField)) 0]
  have : Module.finrank I.ResidueField (I.ResidueField otimes[R] A) = Module.finrank R A := by
    rw [Module.finrank_tensorProduct]; rw [Module.finrank_self]; rw [one_mul]
  rw [← IsNilpotent.map_iff (Algebra.TensorProduct.comm R A I.ResidueField).injective]
  simp only [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    Algebra.coe_lmul_eq_mul, Algebra.TensorProduct.comm_tmul]
  rw [← IsNilpotent.map_iff (Algebra.lmul_injective (R := I.ResidueField))]; rw [LinearMap.isNilpotent_iff_charpoly]; rw [← Algebra.baseChange_lmul]; rw [LinearMap.charpoly_baseChange]; rw [this]
  simp_rw [← ((LinearMap.mul R A) f).charpoly_natDegree]
  constructor
  · intro e i hi
    replace e := congr(($e).coeff i)
    simpa only [Algebra.coe_lmul_eq_mul, coeff_map, coeff_X_pow, hi.ne, ↓reduceIte,
      ← RingHom.mem_ker, Ideal.ker_algebraMap_residueField] using e
  · intro H
    ext i
    obtain (hi | hi) := eq_or_ne i ((LinearMap.mul R A) f).charpoly.natDegree
    · simp only [Algebra.coe_lmul_eq_mul, hi, coeff_map, coeff_X_pow, ↓reduceIte]
      rw [← Polynomial.leadingCoeff]; rw [((LinearMap.mul R A) f).charpoly_monic]; rw [map_one]
    obtain (hi | hi) := lt_or_gt_of_ne hi
    · simpa [hi.ne, ← RingHom.mem_ker, Ideal.ker_algebraMap_residueField] using H i hi
    · simp [hi.ne', coeff_eq_zero_of_natDegree_lt hi]

namespace PrimeSpectrum

set_option backward.isDefEq.respectTransparency false in
/--
lemma `mem_image_comap_zeroLocus_sdiff` / 引理 `mem_image_comap_zeroLocus_sdiff`

English:
lemma mem_image_comap_zeroLocus_sdiff
  given: (f : A) (s : Set A) (x)
  proof: by
  constructor
  · rintro ⟨q, ⟨hqg, hqf⟩, rfl⟩ H
    simp only [mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe] at hqg hqf
    have hs : Ideal.span s <= RingHom.ker (algebraMap A q.asIdeal.ResidueField) := by
      rwa [Ideal.span_le, Ideal.ker_algebraMap_residueField]
    let F : (A ⧸ I

中文:
引理 mem_image_comap_zeroLocus_sdiff
  条件: (f : A) (s : Set A) (x)
  证明: by
  constructor
  · rintro ⟨q, ⟨hqg, hqf⟩, rfl⟩ H
    simp only [mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe] at hqg hqf
    have hs : Ideal.span s <= RingHom.ker (algebraMap A q.asIdeal.ResidueField) := by
      rwa [Ideal.span_le, Ideal.ker_algebraMap_residueField]
    let F : (A ⧸ I

Depends on / 依赖: Algebra, Algebra.TensorProduct.lift, Algebra.ofId, Ideal.Quotient.lift, Ideal.ResidueField.map, Ideal.ker_algebraMap_residueField, Ideal.span, Ideal.span_le, Quotient, ResidueField, RingHom, RingHom.ker, Set.singleton_subset_iff, SetLike, SetLike.mem_coe, TensorProduct, algebraMap, asIdeal, ker_algebraMap_residueField, mem_coe
-/
lemma mem_image_comap_zeroLocus_sdiff (f : A) (s : Set A) (x) :
    x in comap (algebraMap R A) '' (zeroLocus s \ zeroLocus {f}) ↔
      ¬ IsNilpotent (algebraMap A ((A ⧸ Ideal.span s) otimes[R] x.asIdeal.ResidueField) f) := by
  constructor
  · rintro ⟨q, ⟨hqg, hqf⟩, rfl⟩ H
    simp only [mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe] at hqg hqf
    have hs : Ideal.span s <= RingHom.ker (algebraMap A q.asIdeal.ResidueField) := by
      rwa [Ideal.span_le, Ideal.ker_algebraMap_residueField]
    let F : (A ⧸ Ideal.span s) otimes[R] (q.asIdeal.comap (algebraMap R A)).ResidueField ->ₐ[A]
        q.asIdeal.ResidueField :=
      Algebra.TensorProduct.lift
        (Ideal.Quotient.liftₐ (Ideal.span s) (Algebra.ofId A _) hs)
        (Ideal.ResidueField.mapₐ _ _ (Algebra.ofId _ _) rfl)
        fun _ _ => .all _ _
    have := H.map F
    rw [AlgHom.commutes]; rw [isNilpotent_iff_eq_zero]; rw [← RingHom.mem_ker]; rw [Ideal.ker_algebraMap_residueField] at this
    exact hqf this
  · intro H
    rw [← mem_nilradical]; rw [nilradical_eq_sInf]; rw [Ideal.mem_sInf] at H
    simp only [Set.mem_ofPred_eq, Algebra.TensorProduct.algebraMap_apply,
      Ideal.Quotient.algebraMap_eq, not_forall] at H
    obtain ⟨q, hq, hfq⟩ := H
    have : forall a in s, Ideal.Quotient.mk (Ideal.span s) a otimesₜ[R] 1 in q := fun a ha => by
      simp [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ha)]
    refine ⟨comap (algebraMap A _) ⟨q, hq⟩, ⟨by simpa [Set.subset_def], by simpa⟩, ?_⟩
    rw [← comap_comp_apply]; rw [← IsScalarTower.algebraMap_eq]; rw [← Algebra.TensorProduct.includeRight.comp_algebraMap]; rw [comap_comp_apply]; rw [Subsingleton.elim (α := PrimeSpectrum x.asIdeal.ResidueField) (comap _ _) ⊥]
    ext a
    exact congr(a in $(Ideal.ker_algebraMap_residueField _))

/--
lemma `mem_image_comap_basicOpen` / 引理 `mem_image_comap_basicOpen`

English:
lemma mem_image_comap_basicOpen
  given: (f : A) (x)
  proof: by
  have e : A otimes[R] x.asIdeal.ResidueField ≃ₐ[A]
      (A ⧸ (Ideal.span ∅ : Ideal A)) otimes[R] x.asIdeal.ResidueField := by
    refine Algebra.TensorProduct.congr ?f AlgEquiv.refl
    rw [Ideal.span_empty]
    exact { __ := (RingEquiv.quotientBot A).symm, __ := Algebra.ofId _ _ }
  rw [← IsNi

中文:
引理 mem_image_comap_basicOpen
  条件: (f : A) (x)
  证明: by
  have e : A otimes[R] x.asIdeal.ResidueField ≃ₐ[A]
      (A ⧸ (Ideal.span ∅ : Ideal A)) otimes[R] x.asIdeal.ResidueField := by
    refine Algebra.TensorProduct.congr ?f AlgEquiv.refl
    rw [Ideal.span_empty]
    exact { __ := (RingEquiv.quotientBot A).symm, __ := Algebra.ofId _ _ }
  rw [← IsNi

Depends on / 依赖: AlgEquiv, AlgEquiv.commutes, AlgEquiv.refl, Algebra, Algebra.TensorProduct.congr, Algebra.ofId, Ideal.span, Ideal.span_empty, IsNilpotent, IsNilpotent.map_iff, ResidueField, RingEquiv, RingEquiv.quotientBot, Set.compl_eq_univ_sdiff, TensorProduct, asIdeal, basicOpen_eq_zeroLocus_compl, commutes, compl_eq_univ_sdiff, e.injective
-/
lemma mem_image_comap_basicOpen (f : A) (x) :
    x in comap (algebraMap R A) '' basicOpen f ↔
      ¬ IsNilpotent (algebraMap A (A otimes[R] x.asIdeal.ResidueField) f) := by
  have e : A otimes[R] x.asIdeal.ResidueField ≃ₐ[A]
      (A ⧸ (Ideal.span ∅ : Ideal A)) otimes[R] x.asIdeal.ResidueField := by
    refine Algebra.TensorProduct.congr ?f AlgEquiv.refl
    rw [Ideal.span_empty]
    exact { __ := (RingEquiv.quotientBot A).symm, __ := Algebra.ofId _ _ }
  rw [← IsNilpotent.map_iff e.injective]; rw [AlgEquiv.commutes]; rw [← mem_image_comap_zeroLocus_sdiff f ∅ x]; rw [zeroLocus_empty]; rw [← Set.compl_eq_univ_sdiff]; rw [basicOpen_eq_zeroLocus_compl]

/--
lemma `exists_image_comap_of_finite_of_free` / 引理 `exists_image_comap_of_finite_of_free`

English:
lemma exists_image_comap_of_finite_of_free
  statement: (f : A) (s : Set A)
  proof: by
  classical
  use (Finset.range (Module.finrank R (A ⧸ Ideal.span s))).image
    (Algebra.lmul R (A ⧸ Ideal.span s) (Ideal.Quotient.mk _ f)).charpoly.coeff
  ext x
  rw [mem_image_comap_zeroLocus_sdiff]; rw [IsScalarTower.algebraMap_apply A (A ⧸ Ideal.span s)]; rw [isNilpotent_tensor_residueField

中文:
引理 exists_image_comap_of_finite_of_free
  结论: (f : A) (s : Set A)
  证明: by
  classical
  use (Finset.range (Module.finrank R (A ⧸ Ideal.span s))).image
    (Algebra.lmul R (A ⧸ Ideal.span s) (Ideal.Quotient.mk _ f)).charpoly.coeff
  ext x
  rw [mem_image_comap_zeroLocus_sdiff]; rw [IsScalarTower.algebraMap_apply A (A ⧸ Ideal.span s)]; rw [isNilpotent_tensor_residueField

Depends on / 依赖: Algebra, Algebra.lmul, Finset, Finset.range, Ideal.Quotient.mk, Ideal.span, IsScalarTower, IsScalarTower.algebraMap_apply, Module, Module.finrank, Quotient, Set.subset_def, algebraMap_apply, charpoly, charpoly.coeff, classical, finrank, isNilpotent_tensor_residueField_iff, mem_image_comap_zeroLocus_sdiff, subset_def
-/
lemma exists_image_comap_of_finite_of_free (f : A) (s : Set A)
    [Module.Finite R (A ⧸ Ideal.span s)] [Module.Free R (A ⧸ Ideal.span s)] :
    exists t : Finset R, comap (algebraMap R A) '' (zeroLocus s \ zeroLocus {f}) = (zeroLocus t)ᶜ := by
  classical
  use (Finset.range (Module.finrank R (A ⧸ Ideal.span s))).image
    (Algebra.lmul R (A ⧸ Ideal.span s) (Ideal.Quotient.mk _ f)).charpoly.coeff
  ext x
  rw [mem_image_comap_zeroLocus_sdiff]; rw [IsScalarTower.algebraMap_apply A (A ⧸ Ideal.span s)]; rw [isNilpotent_tensor_residueField_iff]
  simp [Set.subset_def]

end PrimeSpectrum

namespace Polynomial

/--
lemma `mem_image_comap_C_basicOpen` / 引理 `mem_image_comap_C_basicOpen`

English:
lemma mem_image_comap_C_basicOpen
  given: (f : R[X]) (x : PrimeSpectrum R)
  proof: by
  trans f.map (algebraMap R x.asIdeal.ResidueField) != 0
  · refine (mem_image_comap_basicOpen _ _).trans (not_iff_not.mpr ?_)
    let e : R[X] otimes[R] x.asIdeal.ResidueField ≃ₐ[R] x.asIdeal.ResidueField[X] :=
      (Algebra.TensorProduct.comm R _ _).trans (polyEquivTensor R x.asIdeal.ResidueFi

中文:
引理 mem_image_comap_C_basicOpen
  条件: (f : R[X]) (x : PrimeSpectrum R)
  证明: by
  trans f.map (algebraMap R x.asIdeal.ResidueField) != 0
  · refine (mem_image_comap_basicOpen _ _).trans (not_iff_not.mpr ?_)
    let e : R[X] otimes[R] x.asIdeal.ResidueField ≃ₐ[R] x.asIdeal.ResidueField[X] :=
      (Algebra.TensorProduct.comm R _ _).trans (polyEquivTensor R x.asIdeal.ResidueFi

Depends on / 依赖: Algebra, Algebra.TensorProduct.comm, IsNilpotent, IsNilpotent.map_iff, Polynomial, Polynomial.ext_iff, ResidueField, TensorProduct, algebraMap, asIdeal, e.injective, ext_iff, f.map, injective, isNilpotent_iff_eq_zero, map_iff, mem_image_comap_basicOpen, not_iff_not, not_iff_not.mpr, otimes
-/
lemma mem_image_comap_C_basicOpen (f : R[X]) (x : PrimeSpectrum R) :
    x in comap C '' basicOpen f ↔ exists i, f.coeff i ∉ x.asIdeal := by
  trans f.map (algebraMap R x.asIdeal.ResidueField) != 0
  · refine (mem_image_comap_basicOpen _ _).trans (not_iff_not.mpr ?_)
    let e : R[X] otimes[R] x.asIdeal.ResidueField ≃ₐ[R] x.asIdeal.ResidueField[X] :=
      (Algebra.TensorProduct.comm R _ _).trans (polyEquivTensor R x.asIdeal.ResidueField).symm
    rw [← IsNilpotent.map_iff e.injective]; rw [isNilpotent_iff_eq_zero]
    simp [e]
  · simp [Polynomial.ext_iff]

/--
lemma `image_comap_C_basicOpen` / 引理 `image_comap_C_basicOpen`

English:
lemma image_comap_C_basicOpen
  given: (f : R[X])
  proof: by
  ext p
  rw [mem_image_comap_C_basicOpen]
  simp [Set.range_subset_iff]

中文:
引理 image_comap_C_basicOpen
  条件: (f : R[X])
  证明: by
  ext p
  rw [mem_image_comap_C_basicOpen]
  simp [Set.range_subset_iff]

Depends on / 依赖: Set.range_subset_iff, mem_image_comap_C_basicOpen, range_subset_iff
-/
lemma image_comap_C_basicOpen (f : R[X]) :
    comap C '' basicOpen f = (zeroLocus (Set.range f.coeff))ᶜ := by
  ext p
  rw [mem_image_comap_C_basicOpen]
  simp [Set.range_subset_iff]

/--
lemma `isOpenMap_comap_C` / 引理 `isOpenMap_comap_C`

English:
lemma isOpenMap_comap_C
  statement: IsOpenMap (comap (R := R) C)
  proof: by
  intro U hU
  obtain ⟨S, hS, rfl⟩ := isTopologicalBasis_basic_opens.open_eq_sUnion hU
  rw [Set.image_sUnion]
  apply isOpen_sUnion
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨r, rfl⟩ := hS ht
  simp only [image_comap_C_basicOpen]
  exact (isClosed_zeroLocus _).isOpen_compl

中文:
引理 isOpenMap_comap_C
  结论: IsOpenMap (comap (R := R) C)
  证明: by
  intro U hU
  obtain ⟨S, hS, rfl⟩ := isTopologicalBasis_basic_opens.open_eq_sUnion hU
  rw [Set.image_sUnion]
  apply isOpen_sUnion
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨r, rfl⟩ := hS ht
  simp only [image_comap_C_basicOpen]
  exact (isClosed_zeroLocus _).isOpen_compl

Depends on / 依赖: Set.image_sUnion, image_comap_C_basicOpen, image_sUnion, isClosed_zeroLocus, isOpen_compl, isOpen_sUnion, isTopologicalBasis_basic_opens, isTopologicalBasis_basic_opens.open_eq_sUnion, open_eq_sUnion
-/
lemma isOpenMap_comap_C : IsOpenMap (comap (R := R) C) := by
  intro U hU
  obtain ⟨S, hS, rfl⟩ := isTopologicalBasis_basic_opens.open_eq_sUnion hU
  rw [Set.image_sUnion]
  apply isOpen_sUnion
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨r, rfl⟩ := hS ht
  simp only [image_comap_C_basicOpen]
  exact (isClosed_zeroLocus _).isOpen_compl

/--
lemma `comap_C_surjective` / 引理 `comap_C_surjective`

English:
lemma comap_C_surjective
  statement: Function.Surjective (comap (R := R) C)
  proof: by
  intro x
  refine ⟨comap (evalRingHom 0) x, ?_⟩
  rw [← comap_comp_apply]; rw [(show (evalRingHom 0).comp C = .id R by ext; simp)]; rw [comap_id]

中文:
引理 comap_C_surjective
  结论: Function.Surjective (comap (R := R) C)
  证明: by
  intro x
  refine ⟨comap (evalRingHom 0) x, ?_⟩
  rw [← comap_comp_apply]; rw [(show (evalRingHom 0).comp C = .id R by ext; simp)]; rw [comap_id]

Depends on / 依赖: comap_comp_apply, comap_id, evalRingHom
-/
lemma comap_C_surjective : Function.Surjective (comap (R := R) C) := by
  intro x
  refine ⟨comap (evalRingHom 0) x, ?_⟩
  rw [← comap_comp_apply]; rw [(show (evalRingHom 0).comp C = .id R by ext; simp)]; rw [comap_id]

/--
lemma `exists_image_comap_of_monic` / 引理 `exists_image_comap_of_monic`

English:
lemma exists_image_comap_of_monic
  given: (f g : R[X]) (hg : g.Monic)
  proof: by
  apply +allowSynthFailures exists_image_comap_of_finite_of_free
  · exact .of_basis (AdjoinRoot.powerBasis' hg).basis
  · exact .of_basis (AdjoinRoot.powerBasis' hg).basis

中文:
引理 exists_image_comap_of_monic
  条件: (f g : R[X]) (hg : g.Monic)
  证明: by
  apply +allowSynthFailures exists_image_comap_of_finite_of_free
  · exact .of_basis (AdjoinRoot.powerBasis' hg).basis
  · exact .of_basis (AdjoinRoot.powerBasis' hg).basis

Depends on / 依赖: AdjoinRoot, AdjoinRoot.powerBasis, allowSynthFailures, exists_image_comap_of_finite_of_free, of_basis, powerBasis
-/
lemma exists_image_comap_of_monic (f g : R[X]) (hg : g.Monic) :
    exists t : Finset R, comap C '' (zeroLocus {g} \ zeroLocus {f}) = (zeroLocus t)ᶜ := by
  apply +allowSynthFailures exists_image_comap_of_finite_of_free
  · exact .of_basis (AdjoinRoot.powerBasis' hg).basis
  · exact .of_basis (AdjoinRoot.powerBasis' hg).basis

/--
lemma `isCompact_image_comap_of_monic` / 引理 `isCompact_image_comap_of_monic`

English:
lemma isCompact_image_comap_of_monic
  given: (f g : R[X]) (hg : g.Monic)
  proof: by
  obtain ⟨t, ht⟩ := exists_image_comap_of_monic f g hg
  rw [ht]; rw [← (t : Set R).iUnion_of_singleton_coe]; rw [zeroLocus_iUnion]; rw [Set.compl_iInter]
  apply isCompact_iUnion
  exact fun _ => by simpa using isCompact_basicOpen _

中文:
引理 isCompact_image_comap_of_monic
  条件: (f g : R[X]) (hg : g.Monic)
  证明: by
  obtain ⟨t, ht⟩ := exists_image_comap_of_monic f g hg
  rw [ht]; rw [← (t : Set R).iUnion_of_singleton_coe]; rw [zeroLocus_iUnion]; rw [Set.compl_iInter]
  apply isCompact_iUnion
  exact fun _ => by simpa using isCompact_basicOpen _

Depends on / 依赖: Set.compl_iInter, compl_iInter, exists_image_comap_of_monic, iUnion_of_singleton_coe, isCompact_basicOpen, isCompact_iUnion, zeroLocus_iUnion
-/
lemma isCompact_image_comap_of_monic (f g : R[X]) (hg : g.Monic) :
    IsCompact (comap C '' (zeroLocus {g} \ zeroLocus {f})) := by
  obtain ⟨t, ht⟩ := exists_image_comap_of_monic f g hg
  rw [ht]; rw [← (t : Set R).iUnion_of_singleton_coe]; rw [zeroLocus_iUnion]; rw [Set.compl_iInter]
  apply isCompact_iUnion
  exact fun _ => by simpa using isCompact_basicOpen _

/--
lemma `isOpen_image_comap_of_monic` / 引理 `isOpen_image_comap_of_monic`

English:
lemma isOpen_image_comap_of_monic
  given: (f g : R[X]) (hg : g.Monic)
  proof: by
  obtain ⟨t, ht⟩ := exists_image_comap_of_monic f g hg
  rw [ht]
  exact (isClosed_zeroLocus (R := R) t).isOpen_compl

中文:
引理 isOpen_image_comap_of_monic
  条件: (f g : R[X]) (hg : g.Monic)
  证明: by
  obtain ⟨t, ht⟩ := exists_image_comap_of_monic f g hg
  rw [ht]
  exact (isClosed_zeroLocus (R := R) t).isOpen_compl

Depends on / 依赖: exists_image_comap_of_monic, isClosed_zeroLocus, isOpen_compl
-/
lemma isOpen_image_comap_of_monic (f g : R[X]) (hg : g.Monic) :
    IsOpen (comap C '' (zeroLocus {g} \ zeroLocus {f})) := by
  obtain ⟨t, ht⟩ := exists_image_comap_of_monic f g hg
  rw [ht]
  exact (isClosed_zeroLocus (R := R) t).isOpen_compl

end Polynomial

namespace MvPolynomial

variable {σ : Type*}

/--
lemma `mem_image_comap_C_basicOpen` / 引理 `mem_image_comap_C_basicOpen`

English:
lemma mem_image_comap_C_basicOpen
  given: (f : MvPolynomial σ R) (x : PrimeSpectrum R)
  proof: by
  trans f.map (algebraMap R x.asIdeal.ResidueField) != 0
  · refine (mem_image_comap_basicOpen _ _).trans (not_iff_not.mpr ?_)
    let e : x.asIdeal.ResidueField otimes[R] MvPolynomial σ R ≃ₐ[x.asIdeal.ResidueField]
        MvPolynomial σ x.asIdeal.ResidueField := scalarRTensorAlgEquiv
    rw [← 

中文:
引理 mem_image_comap_C_basicOpen
  条件: (f : MvPolynomial σ R) (x : PrimeSpectrum R)
  证明: by
  trans f.map (algebraMap R x.asIdeal.ResidueField) != 0
  · refine (mem_image_comap_basicOpen _ _).trans (not_iff_not.mpr ?_)
    let e : x.asIdeal.ResidueField otimes[R] MvPolynomial σ R ≃ₐ[x.asIdeal.ResidueField]
        MvPolynomial σ x.asIdeal.ResidueField := scalarRTensorAlgEquiv
    rw [← 

Depends on / 依赖: Algebra, Algebra.TensorProduct.comm, IsNilpotent, IsNilpotent.map_iff, MvPolynomial, ResidueField, TensorProduct, algebraMap, asIdeal, basicOpen, e.injective, e.toAlgHom.toRingHom.co, f.coeff, f.map, injective, isNilpotent_iff_eq_zero, map_iff, mem_image_comap_basicOpen, not_iff_not, not_iff_not.mpr
-/
lemma mem_image_comap_C_basicOpen (f : MvPolynomial σ R) (x : PrimeSpectrum R) :
    x in comap (C (σ := σ)) '' basicOpen f ↔ exists i, f.coeff i ∉ x.asIdeal := by
  trans f.map (algebraMap R x.asIdeal.ResidueField) != 0
  · refine (mem_image_comap_basicOpen _ _).trans (not_iff_not.mpr ?_)
    let e : x.asIdeal.ResidueField otimes[R] MvPolynomial σ R ≃ₐ[x.asIdeal.ResidueField]
        MvPolynomial σ x.asIdeal.ResidueField := scalarRTensorAlgEquiv
    rw [← IsNilpotent.map_iff (Algebra.TensorProduct.comm ..).injective]; rw [← IsNilpotent.map_iff e.injective]; rw [isNilpotent_iff_eq_zero]
    change (e.toAlgHom.toRingHom.comp (Algebra.TensorProduct.comm ..).toRingHom).comp
      (algebraMap _ _) f = 0 ↔ MvPolynomial.map _ f = 0
    congr!
    ext
    · simp [scalarRTensorAlgEquiv, e, Algebra.smul_def]
    · simp [e, scalarRTensorAlgEquiv, coeff, map, X, monomial]
  · simp [MvPolynomial.ext_iff, coeff_map]

/--
lemma `image_comap_C_basicOpen` / 引理 `image_comap_C_basicOpen`

English:
lemma image_comap_C_basicOpen
  given: (f : MvPolynomial σ R)
  proof: by
  ext p
  rw [mem_image_comap_C_basicOpen]
  simp [Set.range_subset_iff]

中文:
引理 image_comap_C_basicOpen
  条件: (f : MvPolynomial σ R)
  证明: by
  ext p
  rw [mem_image_comap_C_basicOpen]
  simp [Set.range_subset_iff]

Depends on / 依赖: Set.range, Set.range_subset_iff, basicOpen, f.coeff, mem_image_comap_C_basicOpen, range_subset_iff, zeroLocus
-/
lemma image_comap_C_basicOpen (f : MvPolynomial σ R) :
    comap (C (σ := σ)) '' basicOpen f = (zeroLocus (Set.range f.coeff))ᶜ := by
  ext p
  rw [mem_image_comap_C_basicOpen]
  simp [Set.range_subset_iff]

/--
lemma `isOpenMap_comap_C` / 引理 `isOpenMap_comap_C`

English:
lemma isOpenMap_comap_C
  statement: IsOpenMap (comap (R := R) (C (σ := σ)))
  proof: by
  intro U hU
  obtain ⟨S, hS, rfl⟩ := isTopologicalBasis_basic_opens.open_eq_sUnion hU
  rw [Set.image_sUnion]
  apply isOpen_sUnion
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨r, rfl⟩ := hS ht
  simp only [image_comap_C_basicOpen]
  exact (isClosed_zeroLocus _).isOpen_compl

中文:
引理 isOpenMap_comap_C
  结论: IsOpenMap (comap (R := R) (C (σ := σ)))
  证明: by
  intro U hU
  obtain ⟨S, hS, rfl⟩ := isTopologicalBasis_basic_opens.open_eq_sUnion hU
  rw [Set.image_sUnion]
  apply isOpen_sUnion
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨r, rfl⟩ := hS ht
  simp only [image_comap_C_basicOpen]
  exact (isClosed_zeroLocus _).isOpen_compl

Depends on / 依赖: Set.image_sUnion, image_comap_C_basicOpen, image_sUnion, isClosed_zeroLocus, isOpen_compl, isOpen_sUnion, isTopologicalBasis_basic_opens, isTopologicalBasis_basic_opens.open_eq_sUnion, open_eq_sUnion
-/
lemma isOpenMap_comap_C : IsOpenMap (comap (R := R) (C (σ := σ))) := by
  intro U hU
  obtain ⟨S, hS, rfl⟩ := isTopologicalBasis_basic_opens.open_eq_sUnion hU
  rw [Set.image_sUnion]
  apply isOpen_sUnion
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨r, rfl⟩ := hS ht
  simp only [image_comap_C_basicOpen]
  exact (isClosed_zeroLocus _).isOpen_compl

/--
lemma `comap_C_surjective` / 引理 `comap_C_surjective`

English:
lemma comap_C_surjective
  statement: Function.Surjective (comap (R := R) (C (σ := σ)))
  proof: by
  intro x
  refine ⟨comap (eval₂Hom (.id _) 0) x, ?_⟩
  rw [← comap_comp_apply]; rw [(show (eval₂Hom (.id _) 0).comp C = .id R by ext; simp)]; rw [comap_id]

中文:
引理 comap_C_surjective
  结论: Function.Surjective (comap (R := R) (C (σ := σ)))
  证明: by
  intro x
  refine ⟨comap (eval₂Hom (.id _) 0) x, ?_⟩
  rw [← comap_comp_apply]; rw [(show (eval₂Hom (.id _) 0).comp C = .id R by ext; simp)]; rw [comap_id]

Depends on / 依赖: comap_comp_apply, comap_id
-/
lemma comap_C_surjective : Function.Surjective (comap (R := R) (C (σ := σ))) := by
  intro x
  refine ⟨comap (eval₂Hom (.id _) 0) x, ?_⟩
  rw [← comap_comp_apply]; rw [(show (eval₂Hom (.id _) 0).comp C = .id R by ext; simp)]; rw [comap_id]

end MvPolynomial
