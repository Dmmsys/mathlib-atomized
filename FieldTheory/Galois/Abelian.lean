/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.FieldTheory.Galois.Infinite

/-!

# Abelian extensions

In this file, we define the typeclass of abelian extensions and provide some basic API.

-/

public section

variable (K L M : Type*) [Field K] [Field L] [Algebra K L]
variable [Field M] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

/--
Definition of `IsAbelianGalois` / `IsAbelianGalois` 的定义

English:
class IsAbelianGalois
  parameters: (K L : Type*) [Field K] [Field L] [Algebra K L]
  (no additional axioms)

中文:
类 是AbelianGalois
  参数: (K L : 类型) [域 K] [域 L] [代数 K L]
  (无附加公理)
-/
class IsAbelianGalois (K L : Type*) [Field K] [Field L] [Algebra K L] : Prop extends
  IsGalois K L, IsMulCommutative Gal(L/K)

open scoped IsMulCommutative in
/--
lemma `IsAbelianGalois.tower_bot` / 引理 `IsAbelianGalois.tower_bot`

English:
lemma IsAbelianGalois.tower_bot
  given: [IsAbelianGalois K M]
  proof: have : IsGalois K L :=
    ((AlgEquiv.ofBijective (IsScalarTower.toAlgHom K L M).rangeRestrict
      ⟨RingHom.injective _, AlgHom.rangeRestrict_surjective _⟩).transfer_galois
        (E' := (IsScalarTower.toAlgHom K L M).fieldRange)).mpr
      ((InfiniteGalois.normal_iff_isGalois _).mp inferInstance

中文:
引理 是AbelianGalois.tower_bot
  条件: [是AbelianGalois K M]
  证明: have : IsGalois K L :=
    ((AlgEquiv.ofBijective (IsScalarTower.toAlgHom K L M).rangeRestrict
      ⟨RingHom.injective _, AlgHom.rangeRestrict_surjective _⟩).transfer_galois
        (E' := (IsScalarTower.toAlgHom K L M).fieldRange)).mpr
      ((InfiniteGalois.normal_iff_isGalois _).mp inferInstance

Depends on / 依赖: AlgEquiv, AlgEquiv.ofBijective, AlgEquiv.restrictNormalHom_surjective, AlgHom, AlgHom.rangeRestrict_surjective, InfiniteGalois, InfiniteGalois.normal_iff_isGalois, IsGalois, IsScalarTower, IsScalarTower.toAlgHom, RingHom, RingHom.injective, fieldRange, injective, is_comm, is_comm.comm, map_mul, mul_comm, normal_iff_isGalois, ofBijective
-/
lemma IsAbelianGalois.tower_bot [IsAbelianGalois K M] :
    IsAbelianGalois K L :=
  have : IsGalois K L :=
    ((AlgEquiv.ofBijective (IsScalarTower.toAlgHom K L M).rangeRestrict
      ⟨RingHom.injective _, AlgHom.rangeRestrict_surjective _⟩).transfer_galois
        (E' := (IsScalarTower.toAlgHom K L M).fieldRange)).mpr
      ((InfiniteGalois.normal_iff_isGalois _).mp inferInstance)
  { is_comm.comm x y := by
      obtain ⟨x, rfl⟩ := AlgEquiv.restrictNormalHom_surjective M x
      obtain ⟨y, rfl⟩ := AlgEquiv.restrictNormalHom_surjective M y
      rw [← map_mul]; rw [← map_mul]; rw [mul_comm] }

open scoped IsMulCommutative in
/--
lemma `IsAbelianGalois.tower_top` / 引理 `IsAbelianGalois.tower_top`

English:
lemma IsAbelianGalois.tower_top
  given: [IsAbelianGalois K M]
  proof: have : IsGalois L M := .tower_top_of_isGalois K L M
  { is_comm.comm x y := AlgEquiv.restrictScalars_injective K
      (mul_comm (x.restrictScalars K) (y.restrictScalars K)) }

中文:
引理 是AbelianGalois.tower_top
  条件: [是AbelianGalois K M]
  证明: have : IsGalois L M := .tower_top_of_isGalois K L M
  { is_comm.comm x y := AlgEquiv.restrictScalars_injective K
      (mul_comm (x.restrictScalars K) (y.restrictScalars K)) }

Depends on / 依赖: AlgEquiv, AlgEquiv.restrictScalars_injective, IsGalois, is_comm, is_comm.comm, mul_comm, restrictScalars, restrictScalars_injective, tower_top_of_isGalois, x.restrictScalars, y.restrictScalars
-/
lemma IsAbelianGalois.tower_top [IsAbelianGalois K M] :
    IsAbelianGalois L M :=
  have : IsGalois L M := .tower_top_of_isGalois K L M
  { is_comm.comm x y := AlgEquiv.restrictScalars_injective K
      (mul_comm (x.restrictScalars K) (y.restrictScalars K)) }

variable {K L M} in
omit [IsScalarTower K L M] [Algebra L M] in
/--
lemma `IsAbelianGalois.of_algHom` / 引理 `IsAbelianGalois.of_algHom`

English:
lemma IsAbelianGalois.of_algHom
  given: (f : L ->ₐ[K] M) [IsAbelianGalois K M]
  proof: letI := f.toRingHom.toAlgebra
  haveI := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  .tower_bot K L M

中文:
引理 是AbelianGalois.of_algHom
  条件: (f : L ->ₐ[K] M) [是AbelianGalois K M]
  证明: letI := f.toRingHom.toAlgebra
  haveI := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  .tower_bot K L M

Depends on / 依赖: IsScalarTower, IsScalarTower.of_algebraMap_eq, comp_algebraMap, f.comp_algebraMap.symm, f.toRingHom.toAlgebra, of_algebraMap_eq, toAlgebra, toRingHom, tower_bot
-/
lemma IsAbelianGalois.of_algHom (f : L ->ₐ[K] M) [IsAbelianGalois K M] :
    IsAbelianGalois K L :=
  letI := f.toRingHom.toAlgebra
  haveI := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  .tower_bot K L M

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsAbelianGalois
  signature: K L] (K'
  body: .tower_bot K K' L

中文:
实例 [是AbelianGalois
  签名: K L] (K'
  定义体: .tower_bot K K' L

Depends on / 依赖: tower_bot
-/
instance [IsAbelianGalois K L] (K' : IntermediateField K L) : IsAbelianGalois K K' :=
  .tower_bot K K' L

instance (K L : Type*) [Field K] [Field L] [Algebra K L] [IsAbelianGalois K L]
    (K' : IntermediateField K L) : IsAbelianGalois K' L :=
  .tower_top K _ L

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsAbelianGalois K K
  body: Subsingleton.elim _ _

中文:
实例 :
  签名: 是AbelianGalois K K
  定义体: Subsingleton.elim _ _

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
instance : IsAbelianGalois K K where
  is_comm.comm _ _ := Subsingleton.elim _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsAbelianGalois K (⊥ : IntermediateField K L)
  body: .of_algHom (IntermediateField.botEquiv K L).toAlgHom

中文:
实例 :
  签名: 是AbelianGalois K (⊥ : 中间域 K L)
  定义体: .of_algHom (IntermediateField.botEquiv K L).toAlgHom

Depends on / 依赖: IntermediateField, IntermediateField.botEquiv, botEquiv, of_algHom, toAlgHom
-/
instance : IsAbelianGalois K (⊥ : IntermediateField K L) :=
  .of_algHom (IntermediateField.botEquiv K L).toAlgHom

/--
lemma `IsAbelianGalois.of_isCyclic` / 引理 `IsAbelianGalois.of_isCyclic`

English:
lemma IsAbelianGalois.of_isCyclic
  given: [IsGalois K L] [IsCyclic Gal(L/K)]
  statement: IsAbelianGalois K L where

中文:
引理 是AbelianGalois.of_isCyclic
  条件: [是Galois K L] [是循环 Gal(L/K)]
  结论: 是AbelianGalois K L where
-/
lemma IsAbelianGalois.of_isCyclic [IsGalois K L] [IsCyclic Gal(L/K)] : IsAbelianGalois K L where
