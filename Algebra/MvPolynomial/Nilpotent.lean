/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Polynomial.Nilpotent

/-!
# Nilpotents and units in multivariate polynomial rings

We prove that
- `MvPolynomial.isNilpotent_iff`:
  A multivariate polynomial is nilpotent iff all its coefficients are.
- `MvPolynomial.isUnit_iff`:
  A multivariate polynomial is invertible iff its constant term is invertible
  and its other coefficients are nilpotent.
-/

public section

namespace MvPolynomial

variable {σ R : Type*} [CommRing R] {P : MvPolynomial σ R}

-- Subsumed by `isNilpotent_iff` below.
/--
theorem `isNilpotent_iff_of_fintype` / 定理 `isNilpotent_iff_of_fintype`

English:
theorem isNilpotent_iff_of_fintype
  given: [Finite σ]
  proof: by
  classical
  -- Note: including `Fintype.ofFinite σ` in the entire context interferes with the `rw` below.
  refine have := Fintype.ofFinite σ; Fintype.induction_empty_option ?_ ?_ ?_ σ P
  · intro α β _ e h₁ P
    rw [← IsNilpotent.map_iff (rename_injective _ e.symm.injective)]; rw [h₁]; rw [(Finsupp.equivCongrLeft e).forall_congr_left]
    simp [Finsupp.equivMapDomain_eq_mapDomain, coeff_rename_mapDomain _ e.symm.injective]
  · simp [Unique.forall_iff, ← IsNilpotent.map_iff (isEmptyRingEquiv R PEmpty).injective,
      -isEmptyRingEquiv_apply, isEmptyRingEquiv_eq_coeff_zero]
  · intro α _ H P
    obtain ⟨P, rfl⟩ := (optionEquivLeft _ _).symm.surjective P
    simp [IsNilpotent.map_iff (optionEquivLeft _ _).symm.injective,
      Polynomial.isNilpotent_iff, H, Finsupp.optionEquiv.forall_congr_left,
      ← optionEquivLeft_coeff_some_coeff_none, Finsupp.coe_update]

中文:
定理 isNilpotent_iff_of_fintype
  条件: [有限 σ]
  证明: by
  classical
  -- Note: including `Fintype.ofFinite σ` in the entire context interferes with the `rw` below.
  refine have := Fintype.ofFinite σ; Fintype.induction_empty_option ?_ ?_ ?_ σ P
  · intro α β _ e h₁ P
    rw [← IsNilpotent.map_iff (rename_injective _ e.symm.injective)]; rw [h₁]; rw [(Finsupp.equivCongrLeft e).forall_congr_left]
    simp [Finsupp.equivMapDomain_eq_mapDomain, coeff_rename_mapDomain _ e.symm.injective]
  · simp [Unique.forall_iff, ← IsNilpotent.map_iff (isEmptyRingEquiv R PEmpty).injective,
      -isEmptyRingEquiv_apply, isEmptyRingEquiv_eq_coeff_zero]
  · intro α _ H P
    obtain ⟨P, rfl⟩ := (optionEquivLeft _ _).symm.surjective P
    simp [IsNilpotent.map_iff (optionEquivLeft _ _).symm.injective,
      Polynomial.isNilpotent_iff, H, Finsupp.optionEquiv.forall_congr_left,
      ← optionEquivLeft_coeff_some_coeff_none, Finsupp.coe_update]
-/
private theorem isNilpotent_iff_of_fintype [Finite σ] :
    IsNilpotent P ↔ forall i, IsNilpotent (P.coeff i) := by
  classical
  -- Note: including `Fintype.ofFinite σ` in the entire context interferes with the `rw` below.
  refine have := Fintype.ofFinite σ; Fintype.induction_empty_option ?_ ?_ ?_ σ P
  · intro α β _ e h₁ P
    rw [← IsNilpotent.map_iff (rename_injective _ e.symm.injective)]; rw [h₁]; rw [(Finsupp.equivCongrLeft e).forall_congr_left]
    simp [Finsupp.equivMapDomain_eq_mapDomain, coeff_rename_mapDomain _ e.symm.injective]
  · simp [Unique.forall_iff, ← IsNilpotent.map_iff (isEmptyRingEquiv R PEmpty).injective,
      -isEmptyRingEquiv_apply, isEmptyRingEquiv_eq_coeff_zero]
  · intro α _ H P
    obtain ⟨P, rfl⟩ := (optionEquivLeft _ _).symm.surjective P
    simp [IsNilpotent.map_iff (optionEquivLeft _ _).symm.injective,
      Polynomial.isNilpotent_iff, H, Finsupp.optionEquiv.forall_congr_left,
      ← optionEquivLeft_coeff_some_coeff_none, Finsupp.coe_update]

/--
theorem `isNilpotent_iff` / 定理 `isNilpotent_iff`

English:
theorem isNilpotent_iff
  statement: IsNilpotent P ↔ forall i, IsNilpotent (P.coeff i)
  proof: by
  obtain ⟨n, f, hf, P, rfl⟩ := P.exists_fin_rename
  rw [IsNilpotent.map_iff (rename_injective _ hf)]; rw [MvPolynomial.isNilpotent_iff_of_fintype]
  lift f to Fin n ↪ σ using hf
  refine ⟨fun H i => ?_, fun H i => by simpa using H (i.embDomain f)⟩
  by_cases H : i in Set.range (Finsupp.embDomain f)
  · aesop
  · rw [coeff_rename_eq_zero] <;> aesop (add simp Finsupp.embDomain_eq_mapDomain)

中文:
定理 isNilpotent_iff
  结论: 是幂零 P ↔ 对任意 i, 是幂零 (P.coeff i)
  证明: by
  obtain ⟨n, f, hf, P, rfl⟩ := P.exists_fin_rename
  rw [IsNilpotent.map_iff (rename_injective _ hf)]; rw [MvPolynomial.isNilpotent_iff_of_fintype]
  lift f to Fin n ↪ σ using hf
  refine ⟨fun H i => ?_, fun H i => by simpa using H (i.embDomain f)⟩
  by_cases H : i in Set.range (Finsupp.embDomain f)
  · aesop
  · rw [coeff_rename_eq_zero] <;> aesop (add simp Finsupp.embDomain_eq_mapDomain)

Depends on / 依赖: Finsupp, Finsupp.embDomain, Finsupp.embDomain_eq_mapDomain, IsNilpotent, IsNilpotent.map_iff, MvPolynomial, MvPolynomial.isNilpotent_iff_of_fintype, P.exists_fin_rename, Set.range, coeff_rename_eq_zero, embDomain, embDomain_eq_mapDomain, exists_fin_rename, i.embDomain, isNilpotent_iff_of_fintype, map_iff, rename_injective
-/
theorem isNilpotent_iff : IsNilpotent P ↔ forall i, IsNilpotent (P.coeff i) := by
  obtain ⟨n, f, hf, P, rfl⟩ := P.exists_fin_rename
  rw [IsNilpotent.map_iff (rename_injective _ hf)]; rw [MvPolynomial.isNilpotent_iff_of_fintype]
  lift f to Fin n ↪ σ using hf
  refine ⟨fun H i => ?_, fun H i => by simpa using H (i.embDomain f)⟩
  by_cases H : i in Set.range (Finsupp.embDomain f)
  · aesop
  · rw [coeff_rename_eq_zero] <;> aesop (add simp Finsupp.embDomain_eq_mapDomain)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsReduced
  signature: R] : IsReduced (MvPolynomial σ R)
  body: by
  simp [isReduced_iff, isNilpotent_iff, MvPolynomial.ext_iff]

中文:
实例 [是既约
  签名: R] : 是既约 (多元多项式 σ R)
  定义体: by
  simp [isReduced_iff, isNilpotent_iff, MvPolynomial.ext_iff]

Depends on / 依赖: MvPolynomial, MvPolynomial.ext_iff, ext_iff, isNilpotent_iff, isReduced_iff
-/
instance [IsReduced R] : IsReduced (MvPolynomial σ R) := by
  simp [isReduced_iff, isNilpotent_iff, MvPolynomial.ext_iff]

/--
theorem `isUnit_iff` / 定理 `isUnit_iff`

English:
theorem isUnit_iff
  statement: IsUnit P ↔ IsUnit (P.coeff 0) ∧ forall i != 0, IsNilpotent (P.coeff i)
  proof: by
  classical
  refine ⟨fun H => ⟨H.map constantCoeff, ?_⟩, fun ⟨h₁, h₂⟩ => ?_⟩
  · intro n hn
    obtain ⟨i, hi⟩ : exists i, n i != 0 := by simpa [Finsupp.ext_iff] using hn
    let e := (optionEquivLeft _ _).symm.trans (renameEquiv R (Equiv.optionSubtypeNe i))
    have H := (Polynomial.coeff_isUnit_isNilpotent_of_isUnit (H.map e.symm)).2 (n i) hi
    simp only [ne_eq, isNilpotent_iff] at H
    convert! ← H (n.equivMapDomain (Equiv.optionSubtypeNe i).symm).some
    refine (optionEquivLeft_coeff_some_coeff_none _ _ _ _).trans ?_
    simp [Finsupp.equivMapDomain_eq_mapDomain,
      coeff_rename_mapDomain _ (Equiv.optionSubtypeNe i).symm.injective]
  · have : IsNilpotent (P - C (P.coeff 0)) := by
      simp +contextual [isNilpotent_iff, apply_ite, eq_comm, h₂]
    simpa using this.isUnit_add_right_of_commute (h₁.map C) (.all _ _)

中文:
定理 isUnit_iff
  结论: 是单位 P ↔ 是单位 (P.coeff 0) ∧ 对任意 i != 0, 是幂零 (P.coeff i)
  证明: by
  classical
  refine ⟨fun H => ⟨H.map constantCoeff, ?_⟩, fun ⟨h₁, h₂⟩ => ?_⟩
  · intro n hn
    obtain ⟨i, hi⟩ : exists i, n i != 0 := by simpa [Finsupp.ext_iff] using hn
    let e := (optionEquivLeft _ _).symm.trans (renameEquiv R (Equiv.optionSubtypeNe i))
    have H := (Polynomial.coeff_isUnit_isNilpotent_of_isUnit (H.map e.symm)).2 (n i) hi
    simp only [ne_eq, isNilpotent_iff] at H
    convert! ← H (n.equivMapDomain (Equiv.optionSubtypeNe i).symm).some
    refine (optionEquivLeft_coeff_some_coeff_none _ _ _ _).trans ?_
    simp [Finsupp.equivMapDomain_eq_mapDomain,
      coeff_rename_mapDomain _ (Equiv.optionSubtypeNe i).symm.injective]
  · have : IsNilpotent (P - C (P.coeff 0)) := by
      simp +contextual [isNilpotent_iff, apply_ite, eq_comm, h₂]
    simpa using this.isUnit_add_right_of_commute (h₁.map C) (.all _ _)

Depends on / 依赖: Equiv.optionSubtypeNe, Finsupp, Finsupp.ext_iff, H.map, Polynomial, Polynomial.coeff_isUnit_isNilpotent_of_isUnit, classical, coeff_isUnit_isNilpotent_of_isUnit, constantCoeff, convert, e.symm, equivMapDomain, ext_iff, isNilpotent_iff, n.equivMapDomain, ne_eq, optionEquivLeft, optionEquivLeft_coeff_some_coeff_none, optionSubtypeNe, renameEquiv
-/
theorem isUnit_iff : IsUnit P ↔ IsUnit (P.coeff 0) ∧ forall i != 0, IsNilpotent (P.coeff i) := by
  classical
  refine ⟨fun H => ⟨H.map constantCoeff, ?_⟩, fun ⟨h₁, h₂⟩ => ?_⟩
  · intro n hn
    obtain ⟨i, hi⟩ : exists i, n i != 0 := by simpa [Finsupp.ext_iff] using hn
    let e := (optionEquivLeft _ _).symm.trans (renameEquiv R (Equiv.optionSubtypeNe i))
    have H := (Polynomial.coeff_isUnit_isNilpotent_of_isUnit (H.map e.symm)).2 (n i) hi
    simp only [ne_eq, isNilpotent_iff] at H
    convert! ← H (n.equivMapDomain (Equiv.optionSubtypeNe i).symm).some
    refine (optionEquivLeft_coeff_some_coeff_none _ _ _ _).trans ?_
    simp [Finsupp.equivMapDomain_eq_mapDomain,
      coeff_rename_mapDomain _ (Equiv.optionSubtypeNe i).symm.injective]
  · have : IsNilpotent (P - C (P.coeff 0)) := by
      simp +contextual [isNilpotent_iff, apply_ite, eq_comm, h₂]
    simpa using this.isUnit_add_right_of_commute (h₁.map C) (.all _ _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsLocalHom (C : _ ->+* MvPolynomial σ R)
  body: by simp +contextual [isUnit_iff]

中文:
实例 :
  签名: 是Local态射 (C : _ ->+* 多元多项式 σ R)
  定义体: by simp +contextual [isUnit_iff]

Depends on / 依赖: contextual, isUnit_iff
-/
instance : IsLocalHom (C : _ ->+* MvPolynomial σ R) where
  map_nonunit := by simp +contextual [isUnit_iff]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsLocalHom (algebraMap R (MvPolynomial σ R))
  body: inferInstanceAs (IsLocalHom C)

中文:
实例 :
  签名: 是Local态射 (algebraMap R (多元多项式 σ R))
  定义体: inferInstanceAs (IsLocalHom C)

Depends on / 依赖: IsLocalHom
-/
instance : IsLocalHom (algebraMap R (MvPolynomial σ R)) :=
  inferInstanceAs (IsLocalHom C)

/--
theorem `isUnit_iff_totalDegree_of_isReduced` / 定理 `isUnit_iff_totalDegree_of_isReduced`

English:
theorem isUnit_iff_totalDegree_of_isReduced
  given: [IsReduced R]
  proof: by
  convert! isUnit_iff (P := P)
  rw [totalDegree_eq_zero_iff]
  simp [not_imp_comm (a := _ = (0 : R)), Finsupp.ext_iff]

中文:
定理 isUnit_iff_totalDegree_of_isReduced
  条件: [是既约 R]
  证明: by
  convert! isUnit_iff (P := P)
  rw [totalDegree_eq_zero_iff]
  simp [not_imp_comm (a := _ = (0 : R)), Finsupp.ext_iff]

Depends on / 依赖: Finsupp, Finsupp.ext_iff, convert, ext_iff, isUnit_iff, not_imp_comm, totalDegree_eq_zero_iff
-/
theorem isUnit_iff_totalDegree_of_isReduced [IsReduced R] :
    IsUnit P ↔ IsUnit (P.coeff 0) ∧ P.totalDegree = 0 := by
  convert! isUnit_iff (P := P)
  rw [totalDegree_eq_zero_iff]
  simp [not_imp_comm (a := _ = (0 : R)), Finsupp.ext_iff]

/--
theorem `isUnit_iff_eq_C_of_isReduced` / 定理 `isUnit_iff_eq_C_of_isReduced`

English:
theorem isUnit_iff_eq_C_of_isReduced
  given: [IsReduced R]
  proof: by
  rw [isUnit_iff_totalDegree_of_isReduced]; rw [totalDegree_eq_zero_iff_eq_C]
  refine ⟨fun H => ⟨_, H⟩, ?_⟩
  rintro ⟨r, hr, rfl⟩
  simpa

中文:
定理 isUnit_iff_eq_C_of_isReduced
  条件: [是既约 R]
  证明: by
  rw [isUnit_iff_totalDegree_of_isReduced]; rw [totalDegree_eq_zero_iff_eq_C]
  refine ⟨fun H => ⟨_, H⟩, ?_⟩
  rintro ⟨r, hr, rfl⟩
  simpa

Depends on / 依赖: isUnit_iff_totalDegree_of_isReduced, totalDegree_eq_zero_iff_eq_C
-/
theorem isUnit_iff_eq_C_of_isReduced [IsReduced R] :
    IsUnit P ↔ exists r, IsUnit r ∧ P = C r := by
  rw [isUnit_iff_totalDegree_of_isReduced]; rw [totalDegree_eq_zero_iff_eq_C]
  refine ⟨fun H => ⟨_, H⟩, ?_⟩
  rintro ⟨r, hr, rfl⟩
  simpa

end MvPolynomial
