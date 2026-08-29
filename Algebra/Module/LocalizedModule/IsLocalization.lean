/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Jujian Zhang
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Module.LocalizedModule.Basic

/-!
# Equivalence between `IsLocalizedModule` and `IsLocalization`
-/

public section

section IsLocalizedModule

variable {R : Type*} [CommSemiring R] (S : Submonoid R)
variable {A Aₛ : Type*} [CommSemiring A] [Algebra R A]
variable [CommSemiring Aₛ] [Algebra A Aₛ] [Algebra R Aₛ] [IsScalarTower R A Aₛ]

variable {S} in
/--
theorem `isLocalizedModule_iff_isLocalization` / 定理 `isLocalizedModule_iff_isLocalization`

English:
theorem isLocalizedModule_iff_isLocalization
  proof: by
  rw [isLocalizedModule_iff]; rw [isLocalization_iff]
  refine and_congr ?_ (and_congr (forall_congr' fun _ => ?_) (forall₂_congr fun _ _ => ?_))
  · simp_rw [← (Algebra.lmul R Aₛ).commutes, Algebra.lmul_isUnit_iff, Subtype.forall,
      Algebra.algebraMapSubmonoid, ← SetLike.mem_coe, Submonoid.coe_map,
      Set.forall_mem_image, ← IsScalarTower.algebraMap_apply]
  · simp_rw [Prod.exists, Subtype.exists, Algebra.algebraMapSubmonoid]
    simp [← IsScalarTower.algebraMap_apply, Submonoid.mk_smul, Algebra.smul_def, mul_comm]
  · congr!; simp_rw [Subtype.exists, Algebra.algebraMapSubmonoid]; simp [Algebra.smul_def]

中文:
定理 isLocalizedModule_iff_isLocalization
  证明: by
  rw [isLocalizedModule_iff]; rw [isLocalization_iff]
  refine and_congr ?_ (and_congr (forall_congr' fun _ => ?_) (forall₂_congr fun _ _ => ?_))
  · simp_rw [← (Algebra.lmul R Aₛ).commutes, Algebra.lmul_isUnit_iff, Subtype.forall,
      Algebra.algebraMapSubmonoid, ← SetLike.mem_coe, Submonoid.coe_map,
      Set.forall_mem_image, ← IsScalarTower.algebraMap_apply]
  · simp_rw [Prod.exists, Subtype.exists, Algebra.algebraMapSubmonoid]
    simp [← IsScalarTower.algebraMap_apply, Submonoid.mk_smul, Algebra.smul_def, mul_comm]
  · congr!; simp_rw [Subtype.exists, Algebra.algebraMapSubmonoid]; simp [Algebra.smul_def]

Depends on / 依赖: Algebra, Algebra.algebraMapSubmonoid, Algebra.lmul, Algebra.lmul_isUnit_iff, Algebra.smul_def, IsScalarTower, IsScalarTower.algebraMap_apply, Prod.exists, Set.forall_mem_image, SetLike, SetLike.mem_coe, Submonoid, Submonoid.coe_map, Submonoid.mk_smul, Subtype, Subtype.exists, Subtype.forall, algebraMapSubmonoid, algebraMap_apply, and_congr
-/
theorem isLocalizedModule_iff_isLocalization :
    IsLocalizedModule S (IsScalarTower.toAlgHom R A Aₛ).toLinearMap ↔
      IsLocalization (Algebra.algebraMapSubmonoid A S) Aₛ := by
  rw [isLocalizedModule_iff]; rw [isLocalization_iff]
  refine and_congr ?_ (and_congr (forall_congr' fun _ => ?_) (forall₂_congr fun _ _ => ?_))
  · simp_rw [← (Algebra.lmul R Aₛ).commutes, Algebra.lmul_isUnit_iff, Subtype.forall,
      Algebra.algebraMapSubmonoid, ← SetLike.mem_coe, Submonoid.coe_map,
      Set.forall_mem_image, ← IsScalarTower.algebraMap_apply]
  · simp_rw [Prod.exists, Subtype.exists, Algebra.algebraMapSubmonoid]
    simp [← IsScalarTower.algebraMap_apply, Submonoid.mk_smul, Algebra.smul_def, mul_comm]
  · congr!; simp_rw [Subtype.exists, Algebra.algebraMapSubmonoid]; simp [Algebra.smul_def]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsLocalization
  signature: (Algebra.algebraMapSubmonoid A S) Aₛ] :
  body: isLocalizedModule_iff_isLocalization.mpr ‹_›

中文:
实例 [是Localization
  签名: (代数.algebraMapSubmonoid A S) Aₛ] :
  定义体: isLocalizedModule_iff_isLocalization.mpr ‹_›

Depends on / 依赖: isLocalizedModule_iff_isLocalization, isLocalizedModule_iff_isLocalization.mpr
-/
instance [IsLocalization (Algebra.algebraMapSubmonoid A S) Aₛ] :
    IsLocalizedModule S (IsScalarTower.toAlgHom R A Aₛ).toLinearMap :=
  isLocalizedModule_iff_isLocalization.mpr ‹_›

variable (A)

/--
lemma `isLocalizedModule_iff_isLocalization'` / 引理 `isLocalizedModule_iff_isLocalization'`

English:
lemma isLocalizedModule_iff_isLocalization'
  proof: by
  convert! isLocalizedModule_iff_isLocalization (S := S) (A := R) (Aₛ := A)
  exact (Submonoid.map_id S).symm

中文:
引理 isLocalizedModule_iff_isLocalization'
  证明: by
  convert! isLocalizedModule_iff_isLocalization (S := S) (A := R) (Aₛ := A)
  exact (Submonoid.map_id S).symm

Depends on / 依赖: Submonoid, Submonoid.map_id, convert, isLocalizedModule_iff_isLocalization, map_id
-/
lemma isLocalizedModule_iff_isLocalization' :
    IsLocalizedModule S (Algebra.linearMap R A) ↔ IsLocalization S A := by
  convert! isLocalizedModule_iff_isLocalization (S := S) (A := R) (Aₛ := A)
  exact (Submonoid.map_id S).symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsLocalization
  signature: S A] : IsLocalizedModule S (Algebra.linearMap R A)
  body: (isLocalizedModule_iff_isLocalization' S _).mpr inferInstance

中文:
实例 [是Localization
  签名: S A] : 是Localized模 S (代数.linearMap R A)
  定义体: (isLocalizedModule_iff_isLocalization' S _).mpr inferInstance

Depends on / 依赖: isLocalizedModule_iff_isLocalization
-/
instance [IsLocalization S A] : IsLocalizedModule S (Algebra.linearMap R A) :=
  (isLocalizedModule_iff_isLocalization' S _).mpr inferInstance

variable {S A} in
/--
lemma `IsLocalization.mk'_algebraMap_eq_mk'` / 引理 `IsLocalization.mk'_algebraMap_eq_mk'`

English:
lemma IsLocalization.mk'_algebraMap_eq_mk'
  statement: [IsLocalization (Algebra.algebraMapSubmonoid A S) Aₛ]
  proof: by
  rw [← IsLocalizedModule.smul_inj (IsScalarTower.toAlgHom R A Aₛ).toLinearMap s]; rw [IsLocalizedModule.mk'_cancel']; rw [Submonoid.smul_def]; rw [← algebraMap_smul A]
  exact IsLocalization.smul_mk'_self (m := ⟨_, _⟩)

中文:
引理 是Localization.mk'_algebraMap_eq_mk'
  结论: [是Localization (代数.algebraMapSubmonoid A S) Aₛ]
  证明: by
  rw [← IsLocalizedModule.smul_inj (IsScalarTower.toAlgHom R A Aₛ).toLinearMap s]; rw [IsLocalizedModule.mk'_cancel']; rw [Submonoid.smul_def]; rw [← algebraMap_smul A]
  exact IsLocalization.smul_mk'_self (m := ⟨_, _⟩)

Depends on / 依赖: IsLocalization, IsLocalization.smul_mk, IsLocalizedModule, IsLocalizedModule.mk, IsLocalizedModule.smul_inj, IsScalarTower, IsScalarTower.toAlgHom, Submonoid, Submonoid.smul_def, _cancel, _self, algebraMap_smul, smul_def, smul_inj, smul_mk, toAlgHom, toLinearMap
-/
lemma IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization (Algebra.algebraMapSubmonoid A S) Aₛ]
    {x : A} {s : S} : IsLocalization.mk' Aₛ x ⟨_, Algebra.mem_algebraMapSubmonoid_of_mem s⟩ =
      IsLocalizedModule.mk' (IsScalarTower.toAlgHom R A Aₛ).toLinearMap x s := by
  rw [← IsLocalizedModule.smul_inj (IsScalarTower.toAlgHom R A Aₛ).toLinearMap s]; rw [IsLocalizedModule.mk'_cancel']; rw [Submonoid.smul_def]; rw [← algebraMap_smul A]
  exact IsLocalization.smul_mk'_self (m := ⟨_, _⟩)

/--
lemma `IsLocalization.mk'_eq_mk'` / 引理 `IsLocalization.mk'_eq_mk'`

English:
lemma IsLocalization.mk'_eq_mk'
  given: [IsLocalization S A] (x : R) (s : S)
  proof: by
  rw [← IsLocalizedModule.smul_inj (Algebra.linearMap R A) s]; rw [IsLocalizedModule.mk'_cancel']
  exact IsLocalization.smul_mk'_self

中文:
引理 是Localization.mk'_eq_mk'
  条件: [是Localization S A] (x : R) (s : S)
  证明: by
  rw [← IsLocalizedModule.smul_inj (Algebra.linearMap R A) s]; rw [IsLocalizedModule.mk'_cancel']
  exact IsLocalization.smul_mk'_self
-/
lemma IsLocalization.mk'_eq_mk' [IsLocalization S A] (x : R) (s : S) :
    IsLocalization.mk' A x s = IsLocalizedModule.mk' (Algebra.linearMap R A) x s := by
  rw [← IsLocalizedModule.smul_inj (Algebra.linearMap R A) s]; rw [IsLocalizedModule.mk'_cancel']
  exact IsLocalization.smul_mk'_self

end IsLocalizedModule
