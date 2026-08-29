/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.PolynomialAlgebra

/-!
# Localization of algebra maps

In this file we provide constructors to localize algebra maps. Also we show that
localization commutes with taking kernels for ring homomorphisms.

## Implementation detail

The proof that localization commutes with taking kernels does not use the result for linear maps,
as the translation is currently tedious and can be unified easily after the localization refactor.

-/

@[expose] public section

variable {R S P : Type*} (Q : Type*) [CommSemiring R] [CommSemiring S] [CommSemiring P]
  [CommSemiring Q]
  {M : Submonoid R} {T : Submonoid P}
  [Algebra R S] [Algebra P Q] [IsLocalization M S] [IsLocalization T Q]
  (g : R ->+* P)

open IsLocalization in
variable (M S) in
-- TODO: golf using `Ideal.localized'_eq_map`
/--
Instance `Algebra.idealMap_isLocalizedModule` / 实例 `Algebra.idealMap_isLocalizedModule`

English:
instance Algebra.idealMap_isLocalizedModule
  signature: (I : Ideal R)
  body: (Module.End.isUnit_iff _).mpr ⟨fun a b e => Subtype.ext ((map_units S x).mul_right_injective
      (by simpa [Algebra.smul_def] using congr(($e).1))),
      fun a => ⟨⟨_, Ideal.mul_mem_left _ (map_units S x).unit⁻¹.1 a.2⟩,
        Subtype.ext (by simp [Algebra.smul_def, ← mul_assoc])⟩⟩
  surj y :=
 

中文:
实例 Algebra.idealMap_isLocalizedModule
  签名: (I : Ideal R)
  定义体: (Module.End.isUnit_iff _).mpr ⟨fun a b e => Subtype.ext ((map_units S x).mul_right_injective
      (by simpa [Algebra.smul_def] using congr(($e).1))),
      fun a => ⟨⟨_, Ideal.mul_mem_left _ (map_units S x).unit⁻¹.1 a.2⟩,
        Subtype.ext (by simp [Algebra.smul_def, ← mul_assoc])⟩⟩
  surj y :=
 
-/
instance Algebra.idealMap_isLocalizedModule (I : Ideal R) :
    IsLocalizedModule M (Algebra.idealMap I (S := S)) where
  map_units x :=
    (Module.End.isUnit_iff _).mpr ⟨fun a b e => Subtype.ext ((map_units S x).mul_right_injective
      (by simpa [Algebra.smul_def] using congr(($e).1))),
      fun a => ⟨⟨_, Ideal.mul_mem_left _ (map_units S x).unit⁻¹.1 a.2⟩,
        Subtype.ext (by simp [Algebra.smul_def, ← mul_assoc])⟩⟩
  surj y :=
    have ⟨x, hx⟩ := (mem_map_algebraMap_iff M S).mp y.property
    ⟨x, Subtype.ext (by simp [Submonoid.smul_def, Algebra.smul_def, mul_comm, hx])⟩
  exists_of_eq h := ⟨_, Subtype.ext (exists_of_eq congr(($h).1)).choose_spec⟩

/--
lemma `IsLocalization.ker_map` / 引理 `IsLocalization.ker_map`

English:
lemma IsLocalization.ker_map
  given: (hT : Submonoid.map g M = T)
  proof: by
  ext x
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq M x
  simp [RingHom.mem_ker, IsLocalization.map_mk', IsLocalization.mk'_eq_zero_iff,
    IsLocalization.mk'_mem_map_algebraMap_iff, ← hT]

中文:
引理 IsLocalization.ker_map
  条件: (hT : Submonoid.map g M = T)
  证明: by
  ext x
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq M x
  simp [RingHom.mem_ker, IsLocalization.map_mk', IsLocalization.mk'_eq_zero_iff,
    IsLocalization.mk'_mem_map_algebraMap_iff, ← hT]

Depends on / 依赖: IsLocalization, IsLocalization.exists_mk, IsLocalization.map_mk, IsLocalization.mk, RingHom, RingHom.mem_ker, _eq_zero_iff, _mem_map_algebraMap_iff, exists_mk, map_mk, mem_ker
-/
lemma IsLocalization.ker_map (hT : Submonoid.map g M = T) :
    RingHom.ker (IsLocalization.map Q g (hT.symm ▸ M.le_comap_map) : S ->+* Q) =
      (RingHom.ker g).map (algebraMap R S) := by
  ext x
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq M x
  simp [RingHom.mem_ker, IsLocalization.map_mk', IsLocalization.mk'_eq_zero_iff,
    IsLocalization.mk'_mem_map_algebraMap_iff, ← hT]

variable (S) in
/--
Definition of `RingHom.toKerIsLocalization` / `RingHom.toKerIsLocalization` 的定义

English:
definition RingHom.toKerIsLocalization
  signature: (hy : M <= Submonoid.comap g T)
  body: ⟨algebraMap R S x, by simp [RingHom.mem_ker, RingHom.mem_ker.mp x.property]⟩
  map_add' x y := by
    simp only [Submodule.coe_add, map_add, AddMemClass.mk_add_mk]
  map_smul' a x := by
    simp only [SetLike.val_smul, smul_eq_mul, map_mul, id_apply, SetLike.mk_smul_of_tower_mk,
      Algebra.smul_d

中文:
定义 RingHom.toKerIsLocalization
  签名: (hy : M <= Submonoid.comap g T)
  定义体: ⟨algebraMap R S x, by simp [RingHom.mem_ker, RingHom.mem_ker.mp x.property]⟩
  map_add' x y := by
    simp only [Submodule.coe_add, map_add, AddMemClass.mk_add_mk]
  map_smul' a x := by
    simp only [SetLike.val_smul, smul_eq_mul, map_mul, id_apply, SetLike.mk_smul_of_tower_mk,
      Algebra.smul_d

Depends on / 依赖: RingHom, RingHom.mem_ker, RingHom.mem_ker.mp, algebraMap, mem_ker, property, x.property
-/
noncomputable def RingHom.toKerIsLocalization (hy : M <= Submonoid.comap g T) :
    RingHom.ker g ->ₗ[R] RingHom.ker (IsLocalization.map Q g hy : S ->+* Q) where
  toFun x := ⟨algebraMap R S x, by simp [RingHom.mem_ker, RingHom.mem_ker.mp x.property]⟩
  map_add' x y := by
    simp only [Submodule.coe_add, map_add, AddMemClass.mk_add_mk]
  map_smul' a x := by
    simp only [SetLike.val_smul, smul_eq_mul, map_mul, id_apply, SetLike.mk_smul_of_tower_mk,
      Algebra.smul_def]

@[simp]
/--
lemma `RingHom.toKerIsLocalization_apply` / 引理 `RingHom.toKerIsLocalization_apply`

English:
lemma RingHom.toKerIsLocalization_apply
  given: (hy : M <= Submonoid.comap g T) (r : RingHom.ker g)
  proof: rfl

中文:
引理 RingHom.toKerIsLocalization_apply
  条件: (hy : M <= Submonoid.comap g T) (r : RingHom.ker g)
  证明: rfl
-/
lemma RingHom.toKerIsLocalization_apply (hy : M <= Submonoid.comap g T) (r : RingHom.ker g) :
    (RingHom.toKerIsLocalization S Q g hy r).val = algebraMap R S r :=
  rfl

/--
lemma `RingHom.toKerIsLocalization_isLocalizedModule` / 引理 `RingHom.toKerIsLocalization_isLocalizedModule`

English:
lemma RingHom.toKerIsLocalization_isLocalizedModule
  given: (hT : Submonoid.map g M = T)
  proof: by
  let e := LinearEquiv.ofEq _ _ (IsLocalization.ker_map (S := S) Q g hT).symm
  convert_to! IsLocalizedModule M ((e.restrictScalars R).toLinearMap ∘ₗ
    Algebra.idealMap S (RingHom.ker g))
  apply IsLocalizedModule.of_linearEquiv

中文:
引理 RingHom.toKerIsLocalization_isLocalizedModule
  条件: (hT : Submonoid.map g M = T)
  证明: by
  let e := LinearEquiv.ofEq _ _ (IsLocalization.ker_map (S := S) Q g hT).symm
  convert_to! IsLocalizedModule M ((e.restrictScalars R).toLinearMap ∘ₗ
    Algebra.idealMap S (RingHom.ker g))
  apply IsLocalizedModule.of_linearEquiv

Depends on / 依赖: Algebra, Algebra.idealMap, IsLocalization, IsLocalization.ker_map, IsLocalizedModule, IsLocalizedModule.of_linearEquiv, LinearEquiv, LinearEquiv.ofEq, RingHom, RingHom.ker, convert_to, e.restrictScalars, idealMap, ker_map, of_linearEquiv, restrictScalars, toLinearMap
-/
lemma RingHom.toKerIsLocalization_isLocalizedModule (hT : Submonoid.map g M = T) :
    IsLocalizedModule M (toKerIsLocalization S Q g (hT.symm ▸ Submonoid.le_comap_map M)) := by
  let e := LinearEquiv.ofEq _ _ (IsLocalization.ker_map (S := S) Q g hT).symm
  convert_to! IsLocalizedModule M ((e.restrictScalars R).toLinearMap ∘ₗ
    Algebra.idealMap S (RingHom.ker g))
  apply IsLocalizedModule.of_linearEquiv

section Algebra

open Algebra

variable {R : Type*} [CommSemiring R] (M : Submonoid R)
variable {A : Type*} [CommSemiring A] [Algebra R A]
variable {B : Type*} [CommSemiring B] [Algebra R B]
variable (Rₚ : Type*) [CommSemiring Rₚ] [Algebra R Rₚ] [IsLocalization M Rₚ]
variable (Aₚ : Type*) [CommSemiring Aₚ] [Algebra R Aₚ] [Algebra A Aₚ] [IsScalarTower R A Aₚ]
  [IsLocalization (Algebra.algebraMapSubmonoid A M) Aₚ]
variable (Bₚ : Type*) [CommSemiring Bₚ] [Algebra R Bₚ] [Algebra B Bₚ] [IsScalarTower R B Bₚ]
  [IsLocalization (Algebra.algebraMapSubmonoid B M) Bₚ]
variable [Algebra Rₚ Aₚ] [Algebra Rₚ Bₚ] [IsScalarTower R Rₚ Aₚ] [IsScalarTower R Rₚ Bₚ]

namespace IsLocalization

/--
Instance `isLocalization_algebraMapSubmonoid_map_algHom` / 实例 `isLocalization_algebraMapSubmonoid_map_algHom`

English:
instance isLocalization_algebraMapSubmonoid_map_algHom
  signature: (f : A ->ₐ[R] B)
  body: by
  rw [AlgHom.toRingHom_eq_coe]; rw [← Submonoid.map_coe_toMonoidHom]; rw [AlgHom.toRingHom_toMonoidHom]; rw [Submonoid.map_coe_toMonoidHom]; rw [algebraMapSubmonoid_map_eq M f]
  infer_instance

中文:
实例 isLocalization_algebraMapSubmonoid_map_algHom
  签名: (f : A ->ₐ[R] B)
  定义体: by
  rw [AlgHom.toRingHom_eq_coe]; rw [← Submonoid.map_coe_toMonoidHom]; rw [AlgHom.toRingHom_toMonoidHom]; rw [Submonoid.map_coe_toMonoidHom]; rw [algebraMapSubmonoid_map_eq M f]
  infer_instance

Depends on / 依赖: AlgHom, AlgHom.toRingHom_eq_coe, AlgHom.toRingHom_toMonoidHom, Submonoid, Submonoid.map_coe_toMonoidHom, algebraMapSubmonoid_map_eq, infer_instance, map_coe_toMonoidHom, toRingHom_eq_coe, toRingHom_toMonoidHom
-/
instance isLocalization_algebraMapSubmonoid_map_algHom (f : A ->ₐ[R] B) :
    IsLocalization ((algebraMapSubmonoid A M).map f.toRingHom) Bₚ := by
  rw [AlgHom.toRingHom_eq_coe]; rw [← Submonoid.map_coe_toMonoidHom]; rw [AlgHom.toRingHom_toMonoidHom]; rw [Submonoid.map_coe_toMonoidHom]; rw [algebraMapSubmonoid_map_eq M f]
  infer_instance

/--
Definition of `mapₐ` / `mapₐ` 的定义

English:
definition mapₐ
  signature: (f : A ->ₐ[R] B)
  body: ⟨IsLocalization.map Bₚ f.toRingHom (Algebra.algebraMapSubmonoid_le_comap M f), fun r => by
    obtain ⟨a, m, rfl⟩ := IsLocalization.exists_mk'_eq M r
    simp [algebraMap_mk' (S := A), algebraMap_mk' (S := B), map_mk']⟩

@[simp]

中文:
定义 mapₐ
  签名: (f : A ->ₐ[R] B)
  定义体: ⟨IsLocalization.map Bₚ f.toRingHom (Algebra.algebraMapSubmonoid_le_comap M f), fun r => by
    obtain ⟨a, m, rfl⟩ := IsLocalization.exists_mk'_eq M r
    simp [algebraMap_mk' (S := A), algebraMap_mk' (S := B), map_mk']⟩

@[simp]

Depends on / 依赖: Algebra, Algebra.algebraMapSubmonoid_le_comap, IsLocalization, IsLocalization.exists_mk, IsLocalization.map, algebraMapSubmonoid_le_comap, algebraMap_mk, exists_mk, f.toRingHom, map_mk, toRingHom
-/
noncomputable def mapₐ (f : A ->ₐ[R] B) : Aₚ ->ₐ[Rₚ] Bₚ :=
  ⟨IsLocalization.map Bₚ f.toRingHom (Algebra.algebraMapSubmonoid_le_comap M f), fun r => by
    obtain ⟨a, m, rfl⟩ := IsLocalization.exists_mk'_eq M r
    simp [algebraMap_mk' (S := A), algebraMap_mk' (S := B), map_mk']⟩

@[simp]
/--
lemma `mapₐ_coe` / 引理 `mapₐ_coe`

English:
lemma mapₐ_coe
  given: (f : A ->ₐ[R] B)
  proof: rfl

中文:
引理 mapₐ_coe
  条件: (f : A ->ₐ[R] B)
  证明: rfl
-/
lemma mapₐ_coe (f : A ->ₐ[R] B) :
    (mapₐ M Rₚ Aₚ Bₚ f : Aₚ -> Bₚ) = map Bₚ f.toRingHom (algebraMapSubmonoid_le_comap M f) :=
  rfl

/--
lemma `mapₐ_injective_of_injective` / 引理 `mapₐ_injective_of_injective`

English:
lemma mapₐ_injective_of_injective
  given: (f : A ->ₐ[R] B) (hf : Function.Injective f)
  proof: IsLocalization.map_injective_of_injective _ _ _ hf

中文:
引理 mapₐ_injective_of_injective
  条件: (f : A ->ₐ[R] B) (hf : Function.Injective f)
  证明: IsLocalization.map_injective_of_injective _ _ _ hf

Depends on / 依赖: IsLocalization, IsLocalization.map_injective_of_injective, map_injective_of_injective
-/
lemma mapₐ_injective_of_injective (f : A ->ₐ[R] B) (hf : Function.Injective f) :
    Function.Injective (mapₐ M Rₚ Aₚ Bₚ f) :=
  IsLocalization.map_injective_of_injective _ _ _ hf

/--
lemma `mapₐ_surjective_of_surjective` / 引理 `mapₐ_surjective_of_surjective`

English:
lemma mapₐ_surjective_of_surjective
  given: (f : A ->ₐ[R] B) (hf : Function.Surjective f)
  proof: IsLocalization.map_surjective_of_surjective _ _ _ hf

中文:
引理 mapₐ_surjective_of_surjective
  条件: (f : A ->ₐ[R] B) (hf : Function.Surjective f)
  证明: IsLocalization.map_surjective_of_surjective _ _ _ hf

Depends on / 依赖: IsLocalization, IsLocalization.map_surjective_of_surjective, map_surjective_of_surjective
-/
lemma mapₐ_surjective_of_surjective (f : A ->ₐ[R] B) (hf : Function.Surjective f) :
    Function.Surjective (mapₐ M Rₚ Aₚ Bₚ f) :=
  IsLocalization.map_surjective_of_surjective _ _ _ hf

section

/--
lemma `mapExtendScalars_eq_toLinearMap_mapₐ` / 引理 `mapExtendScalars_eq_toLinearMap_mapₐ`

English:
lemma mapExtendScalars_eq_toLinearMap_mapₐ
  given: (f : A ->ₐ[R] B)
  proof: by
  refine LinearMap.restrictScalars_injective R ?_
  apply IsLocalizedModule.linearMap_ext M
    (IsScalarTower.toAlgHom R A Aₚ).toLinearMap
    ((IsScalarTower.toAlgHom R B Bₚ).toLinearMap)
  ext x
  rw [LinearMap.coe_comp]; rw [LinearMap.coe_restrictScalars]; rw [Function.comp_apply]; rw [IsLoca

中文:
引理 mapExtendScalars_eq_toLinearMap_mapₐ
  条件: (f : A ->ₐ[R] B)
  证明: by
  refine LinearMap.restrictScalars_injective R ?_
  apply IsLocalizedModule.linearMap_ext M
    (IsScalarTower.toAlgHom R A Aₚ).toLinearMap
    ((IsScalarTower.toAlgHom R B Bₚ).toLinearMap)
  ext x
  rw [LinearMap.coe_comp]; rw [LinearMap.coe_restrictScalars]; rw [Function.comp_apply]; rw [IsLoca

Depends on / 依赖: Function, Function.comp_apply, IsLocalizedModule, IsLocalizedModule.linearMap_ext, IsLocalizedModule.mapExtendScalars_apply_apply, IsLocalizedModule.map_apply, IsScalarTower, IsScalarTower.toAlgHom, LinearMap, LinearMap.coe_comp, LinearMap.coe_restrictScalars, LinearMap.restrictScalars_injective, coe_comp, coe_restrictScalars, comp_apply, linearMap_ext, mapExtendScalars_apply_apply, map_apply, restrictScalars_injective, toAlgHom
-/
lemma mapExtendScalars_eq_toLinearMap_mapₐ (f : A ->ₐ[R] B) :
    IsLocalizedModule.mapExtendScalars M (IsScalarTower.toAlgHom R A Aₚ).toLinearMap
      (IsScalarTower.toAlgHom R B Bₚ).toLinearMap Rₚ f.toLinearMap =
      (IsLocalization.mapₐ M Rₚ Aₚ Bₚ f).toLinearMap := by
  refine LinearMap.restrictScalars_injective R ?_
  apply IsLocalizedModule.linearMap_ext M
    (IsScalarTower.toAlgHom R A Aₚ).toLinearMap
    ((IsScalarTower.toAlgHom R B Bₚ).toLinearMap)
  ext x
  rw [LinearMap.coe_comp]; rw [LinearMap.coe_restrictScalars]; rw [Function.comp_apply]; rw [IsLocalizedModule.mapExtendScalars_apply_apply]; rw [IsLocalizedModule.map_apply]
  simp

/--
lemma `map_eq_toLinearMap_mapₐ` / 引理 `map_eq_toLinearMap_mapₐ`

English:
lemma map_eq_toLinearMap_mapₐ
  given: (f : A ->ₐ[R] B)
  proof: by
  ext x
  exact DFunLike.congr_fun (mapExtendScalars_eq_toLinearMap_mapₐ M Rₚ Aₚ Bₚ f) x

中文:
引理 map_eq_toLinearMap_mapₐ
  条件: (f : A ->ₐ[R] B)
  证明: by
  ext x
  exact DFunLike.congr_fun (mapExtendScalars_eq_toLinearMap_mapₐ M Rₚ Aₚ Bₚ f) x

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun
-/
lemma map_eq_toLinearMap_mapₐ (f : A ->ₐ[R] B) :
    IsLocalizedModule.map M (IsScalarTower.toAlgHom R A Aₚ).toLinearMap
      (IsScalarTower.toAlgHom R B Bₚ).toLinearMap f.toLinearMap =
      (IsLocalization.mapₐ M Rₚ Aₚ Bₚ f).toLinearMap := by
  ext x
  exact DFunLike.congr_fun (mapExtendScalars_eq_toLinearMap_mapₐ M Rₚ Aₚ Bₚ f) x

/--
lemma `map_linearMap_eq_toLinearMap_mapₐ` / 引理 `map_linearMap_eq_toLinearMap_mapₐ`

English:
lemma map_linearMap_eq_toLinearMap_mapₐ
  proof: map_eq_toLinearMap_mapₐ M Rₚ Rₚ Aₚ (Algebra.ofId R A)

中文:
引理 map_linearMap_eq_toLinearMap_mapₐ
  证明: map_eq_toLinearMap_mapₐ M Rₚ Rₚ Aₚ (Algebra.ofId R A)

Depends on / 依赖: Algebra, Algebra.ofId
-/
lemma map_linearMap_eq_toLinearMap_mapₐ :
    IsLocalizedModule.map M (Algebra.linearMap R Rₚ) (IsScalarTower.toAlgHom R A Aₚ).toLinearMap
      (Algebra.linearMap R A) = (IsLocalization.mapₐ M Rₚ Rₚ Aₚ (Algebra.ofId R A)).toLinearMap :=
  map_eq_toLinearMap_mapₐ M Rₚ Rₚ Aₚ (Algebra.ofId R A)

end

end IsLocalization

open IsLocalization

/--
Definition of `AlgHom.toKerIsLocalization` / `AlgHom.toKerIsLocalization` 的定义

English:
definition AlgHom.toKerIsLocalization
  signature: (f : A ->ₐ[R] B)
  body: RingHom.toKerIsLocalization Aₚ Bₚ f.toRingHom (algebraMapSubmonoid_le_comap M f)

@[simp]

中文:
定义 AlgHom.toKerIsLocalization
  签名: (f : A ->ₐ[R] B)
  定义体: RingHom.toKerIsLocalization Aₚ Bₚ f.toRingHom (algebraMapSubmonoid_le_comap M f)

@[simp]

Depends on / 依赖: RingHom, RingHom.toKerIsLocalization, algebraMapSubmonoid_le_comap, f.toRingHom, toKerIsLocalization, toRingHom
-/
noncomputable def AlgHom.toKerIsLocalization (f : A ->ₐ[R] B) :
    RingHom.ker f ->ₗ[A] RingHom.ker (mapₐ M Rₚ Aₚ Bₚ f) :=
  RingHom.toKerIsLocalization Aₚ Bₚ f.toRingHom (algebraMapSubmonoid_le_comap M f)

@[simp]
/--
lemma `AlgHom.toKerIsLocalization_apply` / 引理 `AlgHom.toKerIsLocalization_apply`

English:
lemma AlgHom.toKerIsLocalization_apply
  given: (f : A ->ₐ[R] B) (x : RingHom.ker f)
  proof: rfl

中文:
引理 AlgHom.toKerIsLocalization_apply
  条件: (f : A ->ₐ[R] B) (x : RingHom.ker f)
  证明: rfl
-/
lemma AlgHom.toKerIsLocalization_apply (f : A ->ₐ[R] B) (x : RingHom.ker f) :
    AlgHom.toKerIsLocalization M Rₚ Aₚ Bₚ f x =
      RingHom.toKerIsLocalization Aₚ Bₚ f.toRingHom (algebraMapSubmonoid_le_comap M f) x :=
  rfl

/--
lemma `AlgHom.toKerIsLocalization_isLocalizedModule` / 引理 `AlgHom.toKerIsLocalization_isLocalizedModule`

English:
lemma AlgHom.toKerIsLocalization_isLocalizedModule
  given: (f : A ->ₐ[R] B)
  proof: RingHom.toKerIsLocalization_isLocalizedModule Bₚ f.toRingHom
    (algebraMapSubmonoid_map_eq M f)

中文:
引理 AlgHom.toKerIsLocalization_isLocalizedModule
  条件: (f : A ->ₐ[R] B)
  证明: RingHom.toKerIsLocalization_isLocalizedModule Bₚ f.toRingHom
    (algebraMapSubmonoid_map_eq M f)

Depends on / 依赖: RingHom, RingHom.toKerIsLocalization_isLocalizedModule, algebraMapSubmonoid_map_eq, f.toRingHom, toKerIsLocalization_isLocalizedModule, toRingHom
-/
lemma AlgHom.toKerIsLocalization_isLocalizedModule (f : A ->ₐ[R] B) :
    IsLocalizedModule (Algebra.algebraMapSubmonoid A M)
      (AlgHom.toKerIsLocalization M Rₚ Aₚ Bₚ f) :=
  RingHom.toKerIsLocalization_isLocalizedModule Bₚ f.toRingHom
    (algebraMapSubmonoid_map_eq M f)

end Algebra

namespace Polynomial

attribute [local instance] Polynomial.algebra in
/--
lemma `isLocalization` / 引理 `isLocalization`

English:
lemma isLocalization
  statement: {R} [CommSemiring R] (S : Submonoid R) (A) [CommSemiring A] [Algebra R A]
  proof: isLocalizedModule_iff_isLocalization.mp (isLocalizedModule_iff_isBaseChange S A _).mpr
    .of_equiv (polyEquivTensor' R A).symm.toLinearEquiv fun _ => by simp

中文:
引理 isLocalization
  结论: {R} [CommSemiring R] (S : Submonoid R) (A) [CommSemiring A] [Algebra R A]
  证明: isLocalizedModule_iff_isLocalization.mp (isLocalizedModule_iff_isBaseChange S A _).mpr
    .of_equiv (polyEquivTensor' R A).symm.toLinearEquiv fun _ => by simp

Depends on / 依赖: isLocalizedModule_iff_isBaseChange, isLocalizedModule_iff_isLocalization, isLocalizedModule_iff_isLocalization.mp, of_equiv, polyEquivTensor, symm.toLinearEquiv, toLinearEquiv
-/
lemma isLocalization {R} [CommSemiring R] (S : Submonoid R) (A) [CommSemiring A] [Algebra R A]
    [IsLocalization S A] : IsLocalization (S.map C) A[X] :=
isLocalizedModule_iff_isLocalization.mp (isLocalizedModule_iff_isBaseChange S A _).mpr
    .of_equiv (polyEquivTensor' R A).symm.toLinearEquiv fun _ => by simp

end Polynomial
