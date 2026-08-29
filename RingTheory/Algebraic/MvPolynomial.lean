/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.MvPolynomial.Supported
public import Mathlib.RingTheory.Adjoin.Polynomial.Basic
public import Mathlib.RingTheory.Algebraic.Basic

/-!
# Transcendental elements in `MvPolynomial`

This file lists some results on some elements in `MvPolynomial σ R` being transcendental
over the base ring `R` and subrings `MvPolynomial.supported` of `MvPolynomial σ R`.
-/

public section

universe u v w

open Polynomial

namespace MvPolynomial

variable {σ : Type*} (R : Type*) [CommRing R]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `transcendental_supported_polynomial_aeval_X` / 定理 `transcendental_supported_polynomial_aeval_X`

English:
theorem transcendental_supported_polynomial_aeval_X
  statement: {i : σ} {s : Set σ} (h : i ∉ s)
  proof: by
  classical
  rw [transcendental_iff_injective] at hf ⊢
  let g := MvPolynomial.mapAlgHom (R := R) (σ := s) (Polynomial.aeval (R := R) f)
  replace hf : Function.Injective g := MvPolynomial.map_injective _ hf
  let u := (Subalgebra.val _).comp
    ((optionEquivRight R s).symm |>.trans
.trans (ren

中文:
定理 transcendental_supported_polynomial_aeval_X
  结论: {i : σ} {s : 集合 σ} (h : i ∉ s)
  证明: by
  classical
  rw [transcendental_iff_injective] at hf ⊢
  let g := MvPolynomial.mapAlgHom (R := R) (σ := s) (Polynomial.aeval (R := R) f)
  replace hf : Function.Injective g := MvPolynomial.map_injective _ hf
  let u := (Subalgebra.val _).comp
    ((optionEquivRight R s).symm |>.trans
.trans (ren

Depends on / 依赖: Function, Function.Injective, Injective, MvPolynomial, MvPolynomial.mapAlgHom, MvPolynomial.map_injective, Polynomial, Polynomial.aeval, Set.subtypeInsertEquivOption, Subalgebra, Subalgebra.val, classical, mapAlgHom, map_injective, optionEquivLeft, optionEquivRight, renameEquiv, replace, subtypeInsertEquivOption, supportedEquivMvPolynomial
-/
theorem transcendental_supported_polynomial_aeval_X {i : σ} {s : Set σ} (h : i ∉ s)
    {f : R[X]} (hf : Transcendental R f) :
    Transcendental (supported R s) (Polynomial.aeval (X i : MvPolynomial σ R) f) := by
  classical
  rw [transcendental_iff_injective] at hf ⊢
  let g := MvPolynomial.mapAlgHom (R := R) (σ := s) (Polynomial.aeval (R := R) f)
  replace hf : Function.Injective g := MvPolynomial.map_injective _ hf
  let u := (Subalgebra.val _).comp
    ((optionEquivRight R s).symm |>.trans
.trans (renameEquiv R (Set.subtypeInsertEquivOption h).symm)
      (supportedEquivMvPolynomial _).symm).toAlgHom |>.comp
.comp g
    ((optionEquivLeft R s).symm.trans (optionEquivRight R s)).toAlgHom
  let v := ((Polynomial.aeval (R := supported R s)
    (Polynomial.aeval (X i : MvPolynomial σ R) f)).restrictScalars R).comp
      (Polynomial.mapAlgEquiv (supportedEquivMvPolynomial s).symm).toAlgHom
  replace hf : Function.Injective u := by
    simp only [AlgHom.coe_comp, Subalgebra.coe_val,
      AlgEquiv.coe_toAlgHom, AlgEquiv.coe_trans, Function.comp_assoc, u]
    apply Subtype.val_injective.comp
    simp only [EquivLike.comp_injective]
    apply hf.comp
    simp only [EquivLike.comp_injective, EquivLike.injective]
  have h1 : Polynomial.aeval (X i : MvPolynomial σ R) = ((Subalgebra.val _).comp
.comp (supportedEquivMvPolynomial _).symm.toAlgHom
      (Polynomial.aeval (X ⟨i, s.mem_insert i⟩ : MvPolynomial ↑(insert i s) R))) := by
    ext1; simp
  have h2 : u = v := by
    simp only [u, v, g]
    ext1
    · ext1
      simp [Set.subtypeInsertEquivOption, Subalgebra.algebraMap_eq, optionEquivLeft_symm_apply]
    · simp [Set.subtypeInsertEquivOption, h1, optionEquivLeft_symm_apply]
  simpa only [h2, v, AlgHom.coe_comp, AlgEquiv.coe_toAlgHom,
    EquivLike.injective_comp, AlgHom.coe_restrictScalars'] using hf

/--
theorem `transcendental_polynomial_aeval_X` / 定理 `transcendental_polynomial_aeval_X`

English:
theorem transcendental_polynomial_aeval_X
  given: (i : σ) {f : R[X]} (hf : Transcendental R f)
  proof: by
  have := transcendental_supported_polynomial_aeval_X R (Set.notMem_empty i) hf
  let g := (Algebra.botEquivOfInjective (MvPolynomial.C_injective σ R)).symm.trans
    (Subalgebra.equivOfEq _ _ supported_empty).symm
  rwa [Transcendental, ← isAlgebraic_ringHom_iff_of_comp_eq g (RingHom.id (MvPolyn

中文:
定理 transcendental_polynomial_aeval_X
  条件: (i : σ) {f : R[X]} (hf : 超越 R f)
  证明: by
  have := transcendental_supported_polynomial_aeval_X R (Set.notMem_empty i) hf
  let g := (Algebra.botEquivOfInjective (MvPolynomial.C_injective σ R)).symm.trans
    (Subalgebra.equivOfEq _ _ supported_empty).symm
  rwa [Transcendental, ← isAlgebraic_ringHom_iff_of_comp_eq g (RingHom.id (MvPolyn

Depends on / 依赖: Algebra, Algebra.botEquivOfInjective, C_injective, Function, Function.injective_id, MvPolynomial, MvPolynomial.C_injective, RingHom, RingHom.id, RingHom.id_apply, Set.notMem_empty, Subalgebra, Subalgebra.equivOfEq, Transcendental, botEquivOfInjective, equivOfEq, id_apply, injective_id, isAlgebraic_ringHom_iff_of_comp_eq, notMem_empty
-/
theorem transcendental_polynomial_aeval_X (i : σ) {f : R[X]} (hf : Transcendental R f) :
    Transcendental R (Polynomial.aeval (X i : MvPolynomial σ R) f) := by
  have := transcendental_supported_polynomial_aeval_X R (Set.notMem_empty i) hf
  let g := (Algebra.botEquivOfInjective (MvPolynomial.C_injective σ R)).symm.trans
    (Subalgebra.equivOfEq _ _ supported_empty).symm
  rwa [Transcendental, ← isAlgebraic_ringHom_iff_of_comp_eq g (RingHom.id (MvPolynomial σ R))
    Function.injective_id (by ext1; rfl), RingHom.id_apply, ← Transcendental]

/--
theorem `transcendental_polynomial_aeval_X_iff` / 定理 `transcendental_polynomial_aeval_X_iff`

English:
theorem transcendental_polynomial_aeval_X_iff
  given: (i : σ) {f : R[X]}
  proof: by
  refine ⟨?_, transcendental_polynomial_aeval_X R i⟩
  simp_rw [Transcendental, not_imp_not]
  exact fun h => h.algHom _

中文:
定理 transcendental_polynomial_aeval_X_iff
  条件: (i : σ) {f : R[X]}
  证明: by
  refine ⟨?_, transcendental_polynomial_aeval_X R i⟩
  simp_rw [Transcendental, not_imp_not]
  exact fun h => h.algHom _

Depends on / 依赖: Transcendental, algHom, h.algHom, not_imp_not, simp_rw, transcendental_polynomial_aeval_X
-/
theorem transcendental_polynomial_aeval_X_iff (i : σ) {f : R[X]} :
    Transcendental R (Polynomial.aeval (X i : MvPolynomial σ R) f) ↔ Transcendental R f := by
  refine ⟨?_, transcendental_polynomial_aeval_X R i⟩
  simp_rw [Transcendental, not_imp_not]
  exact fun h => h.algHom _

/--
theorem `transcendental_supported_polynomial_aeval_X_iff` / 定理 `transcendental_supported_polynomial_aeval_X_iff`

English:
theorem transcendental_supported_polynomial_aeval_X_iff
  proof: by
  refine ⟨fun h => ⟨?_, ?_⟩, fun ⟨h, hf⟩ => transcendental_supported_polynomial_aeval_X R h hf⟩
  · rw [Transcendental] at h
    contrapose h
    refine isAlgebraic_algebraMap (⟨Polynomial.aeval (X i) f, ?_⟩ : supported R s)
    exact Algebra.adjoin_mono (Set.singleton_subset_iff.2 (Set.mem_image

中文:
定理 transcendental_supported_polynomial_aeval_X_iff
  证明: by
  refine ⟨fun h => ⟨?_, ?_⟩, fun ⟨h, hf⟩ => transcendental_supported_polynomial_aeval_X R h hf⟩
  · rw [Transcendental] at h
    contrapose h
    refine isAlgebraic_algebraMap (⟨Polynomial.aeval (X i) f, ?_⟩ : supported R s)
    exact Algebra.adjoin_mono (Set.singleton_subset_iff.2 (Set.mem_image

Depends on / 依赖: Algebra, Algebra.adjoin_mono, C_injective, MvPolynomial, MvPolynomial.C_injective, MvPolynomial.algebraMap_, Polynomial, Polynomial.aeval, Polynomial.aeval_mem_adjoin_singleton, Set.mem_image_of_mem, Set.singleton_subset_iff, Transcendental, adjoin_mono, aeval_mem_adjoin_singleton, algebraMap_, contrapose, h.restrictScalars, isAlgebraic_algebraMap, mem_image_of_mem, restrictScalars
-/
theorem transcendental_supported_polynomial_aeval_X_iff
    [Nontrivial R] {i : σ} {s : Set σ} {f : R[X]} :
    Transcendental (supported R s) (Polynomial.aeval (X i : MvPolynomial σ R) f) ↔
    i ∉ s ∧ Transcendental R f := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun ⟨h, hf⟩ => transcendental_supported_polynomial_aeval_X R h hf⟩
  · rw [Transcendental] at h
    contrapose h
    refine isAlgebraic_algebraMap (⟨Polynomial.aeval (X i) f, ?_⟩ : supported R s)
    exact Algebra.adjoin_mono (Set.singleton_subset_iff.2 (Set.mem_image_of_mem _ h))
      (Polynomial.aeval_mem_adjoin_singleton _ _)
  · rw [← transcendental_polynomial_aeval_X_iff R i]
    refine h.restrictScalars fun _ _ heq => MvPolynomial.C_injective σ R ?_
    simp_rw [← MvPolynomial.algebraMap_eq]
    exact congr($(heq).1)

/--
theorem `transcendental_supported_X` / 定理 `transcendental_supported_X`

English:
theorem transcendental_supported_X
  given: {i : σ} {s : Set σ} (h : i ∉ s)
  proof: by
  simpa using transcendental_supported_polynomial_aeval_X R h (Polynomial.transcendental_X R)

中文:
定理 transcendental_supported_X
  条件: {i : σ} {s : 集合 σ} (h : i ∉ s)
  证明: by
  simpa using transcendental_supported_polynomial_aeval_X R h (Polynomial.transcendental_X R)

Depends on / 依赖: Polynomial, Polynomial.transcendental_X, transcendental_X, transcendental_supported_polynomial_aeval_X
-/
theorem transcendental_supported_X {i : σ} {s : Set σ} (h : i ∉ s) :
    Transcendental (supported R s) (X i : MvPolynomial σ R) := by
  simpa using transcendental_supported_polynomial_aeval_X R h (Polynomial.transcendental_X R)

/--
theorem `transcendental_X` / 定理 `transcendental_X`

English:
theorem transcendental_X
  given: (i : σ)
  statement: Transcendental R (X i : MvPolynomial σ R)
  proof: by
  simpa using transcendental_polynomial_aeval_X R i (Polynomial.transcendental_X R)

中文:
定理 transcendental_X
  条件: (i : σ)
  结论: 超越 R (X i : 多元多项式 σ R)
  证明: by
  simpa using transcendental_polynomial_aeval_X R i (Polynomial.transcendental_X R)

Depends on / 依赖: Polynomial, Polynomial.transcendental_X, transcendental_X, transcendental_polynomial_aeval_X
-/
theorem transcendental_X (i : σ) : Transcendental R (X i : MvPolynomial σ R) := by
  simpa using transcendental_polynomial_aeval_X R i (Polynomial.transcendental_X R)

/--
theorem `transcendental_supported_X_iff` / 定理 `transcendental_supported_X_iff`

English:
theorem transcendental_supported_X_iff
  given: [Nontrivial R] {i : σ} {s : Set σ}
  proof: by
  simpa [Polynomial.transcendental_X] using
    transcendental_supported_polynomial_aeval_X_iff R (i := i) (s := s) (f := Polynomial.X)

中文:
定理 transcendental_supported_X_iff
  条件: [非平凡 R] {i : σ} {s : 集合 σ}
  证明: by
  simpa [Polynomial.transcendental_X] using
    transcendental_supported_polynomial_aeval_X_iff R (i := i) (s := s) (f := Polynomial.X)

Depends on / 依赖: Polynomial, Polynomial.X, Polynomial.transcendental_X, transcendental_X, transcendental_supported_polynomial_aeval_X_iff
-/
theorem transcendental_supported_X_iff [Nontrivial R] {i : σ} {s : Set σ} :
    Transcendental (supported R s) (X i : MvPolynomial σ R) ↔ i ∉ s := by
  simpa [Polynomial.transcendental_X] using
    transcendental_supported_polynomial_aeval_X_iff R (i := i) (s := s) (f := Polynomial.X)

end MvPolynomial
