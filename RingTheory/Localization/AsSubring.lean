/-
Copyright (c) 2022 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Junyan Xu
-/
module

public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Tower

/-!

# Localizations of domains as subalgebras of the fraction field.

Given a domain `A` with fraction field `K`, and a submonoid `S` of `A` which
does not contain zero, this file constructs the localization of `A` at `S`
as a subalgebra of the field `K` over `A`.

-/

@[expose] public section


namespace Localization

open nonZeroDivisors

variable {A : Type*} (K : Type*) [CommRing A] (S : Submonoid A) (hS : S <= A⁰)

section CommRing

variable [CommRing K] [Algebra A K] [IsFractionRing A K]

/--
theorem `map_isUnit_of_le` / 定理 `map_isUnit_of_le`

English:
theorem map_isUnit_of_le
  given: (hS : S <= A⁰) (s : S)
  statement: IsUnit (algebraMap A K s)
  proof: by
  apply IsLocalization.map_units K (⟨s.1, hS s.2⟩ : A⁰)

中文:
定理 map_isUnit_of_le
  条件: (hS : S <= A⁰) (s : S)
  结论: 是单位 (algebraMap A K s)
  证明: by
  apply IsLocalization.map_units K (⟨s.1, hS s.2⟩ : A⁰)

Depends on / 依赖: IsLocalization, IsLocalization.map_units, map_units
-/
theorem map_isUnit_of_le (hS : S <= A⁰) (s : S) : IsUnit (algebraMap A K s) := by
  apply IsLocalization.map_units K (⟨s.1, hS s.2⟩ : A⁰)

/--
Definition of `mapToFractionRing` / `mapToFractionRing` 的定义

English:
definition mapToFractionRing
  signature: (B : Type*) [CommRing B] [Algebra A B] [IsLocalization S B]
  body: { IsLocalization.lift (map_isUnit_of_le K S hS) with commutes' := fun a => by simp }

@[simp]

中文:
定义 mapToFractionRing
  签名: (B : 类型) [交换环 B] [代数 A B] [是Localization S B]
  定义体: { IsLocalization.lift (map_isUnit_of_le K S hS) with commutes' := fun a => by simp }

@[simp]

Depends on / 依赖: IsLocalization, IsLocalization.lift, commutes, map_isUnit_of_le
-/
noncomputable def mapToFractionRing (B : Type*) [CommRing B] [Algebra A B] [IsLocalization S B]
    (hS : S <= A⁰) : B ->ₐ[A] K :=
  { IsLocalization.lift (map_isUnit_of_le K S hS) with commutes' := fun a => by simp }

@[simp]
/--
theorem `mapToFractionRing_apply` / 定理 `mapToFractionRing_apply`

English:
theorem mapToFractionRing_apply
  statement: {B : Type*} [CommRing B] [Algebra A B] [IsLocalization S B]
  proof: rfl

中文:
定理 mapToFractionRing_apply
  结论: {B : 类型} [交换环 B] [代数 A B] [是Localization S B]
  证明: rfl
-/
theorem mapToFractionRing_apply {B : Type*} [CommRing B] [Algebra A B] [IsLocalization S B]
    (hS : S <= A⁰) (b : B) :
    mapToFractionRing K S B hS b = IsLocalization.lift (map_isUnit_of_le K S hS) b :=
  rfl

/--
theorem `mem_range_mapToFractionRing_iff` / 定理 `mem_range_mapToFractionRing_iff`

English:
theorem mem_range_mapToFractionRing_iff
  statement: (B : Type*) [CommRing B] [Algebra A B] [IsLocalization S B]
  proof: ⟨by
    rintro ⟨x, rfl⟩
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq S x
    use a, s, s.2
    apply IsLocalization.lift_mk', by
    rintro ⟨a, s, hs, rfl⟩
    use IsLocalization.mk' _ a ⟨s, hs⟩
    apply IsLocalization.lift_mk'⟩

中文:
定理 mem_range_mapToFractionRing_iff
  结论: (B : 类型) [交换环 B] [代数 A B] [是Localization S B]
  证明: ⟨by
    rintro ⟨x, rfl⟩
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq S x
    use a, s, s.2
    apply IsLocalization.lift_mk', by
    rintro ⟨a, s, hs, rfl⟩
    use IsLocalization.mk' _ a ⟨s, hs⟩
    apply IsLocalization.lift_mk'⟩

Depends on / 依赖: IsLocalization, IsLocalization.exists_mk, IsLocalization.lift_mk, IsLocalization.mk, exists_mk, lift_mk
-/
theorem mem_range_mapToFractionRing_iff (B : Type*) [CommRing B] [Algebra A B] [IsLocalization S B]
    (hS : S <= A⁰) (x : K) :
    x in (mapToFractionRing K S B hS).range ↔
      exists (a s : A) (hs : s in S), x = IsLocalization.mk' K a ⟨s, hS hs⟩ :=
  ⟨by
    rintro ⟨x, rfl⟩
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq S x
    use a, s, s.2
    apply IsLocalization.lift_mk', by
    rintro ⟨a, s, hs, rfl⟩
    use IsLocalization.mk' _ a ⟨s, hs⟩
    apply IsLocalization.lift_mk'⟩

/--
Instance `isLocalization_range_mapToFractionRing` / 实例 `isLocalization_range_mapToFractionRing`

English:
instance isLocalization_range_mapToFractionRing
  signature: (B : Type*) [CommRing B] [Algebra A B]
  body: IsLocalization.isLocalization_of_algEquiv S
    show B ≃ₐ[A] _ from AlgEquiv.ofBijective (mapToFractionRing K S B hS).rangeRestrict (by
      refine ⟨fun a b h => ?_, Set.rangeFactorization_surjective⟩
      refine (IsLocalization.lift_injective_iff _).2 (fun a b => ?_) (Subtype.ext_iff.1 h)
      exact ⟨fun h => congr_arg _ (IsLocalization.injective _ hS h),
        fun h => congr_arg _ (IsFractionRing.injective A K h)⟩)

中文:
实例 isLocalization_range_mapToFractionRing
  签名: (B : 类型) [交换环 B] [代数 A B]
  定义体: IsLocalization.isLocalization_of_algEquiv S
    show B ≃ₐ[A] _ from AlgEquiv.ofBijective (mapToFractionRing K S B hS).rangeRestrict (by
      refine ⟨fun a b h => ?_, Set.rangeFactorization_surjective⟩
      refine (IsLocalization.lift_injective_iff _).2 (fun a b => ?_) (Subtype.ext_iff.1 h)
      exact ⟨fun h => congr_arg _ (IsLocalization.injective _ hS h),
        fun h => congr_arg _ (IsFractionRing.injective A K h)⟩)

Depends on / 依赖: AlgEquiv, AlgEquiv.ofBijective, IsFractionRing, IsFractionRing.injective, IsLocalization, IsLocalization.injective, IsLocalization.isLocalization_of_algEquiv, IsLocalization.lift_injective_iff, Set.rangeFactorization_surjective, Subtype, Subtype.ext_iff, congr_arg, ext_iff, injective, isLocalization_of_algEquiv, lift_injective_iff, mapToFractionRing, ofBijective, rangeFactorization_surjective, rangeRestrict
-/
instance isLocalization_range_mapToFractionRing (B : Type*) [CommRing B] [Algebra A B]
    [IsLocalization S B] (hS : S <= A⁰) : IsLocalization S (mapToFractionRing K S B hS).range :=
IsLocalization.isLocalization_of_algEquiv S
    show B ≃ₐ[A] _ from AlgEquiv.ofBijective (mapToFractionRing K S B hS).rangeRestrict (by
      refine ⟨fun a b h => ?_, Set.rangeFactorization_surjective⟩
      refine (IsLocalization.lift_injective_iff _).2 (fun a b => ?_) (Subtype.ext_iff.1 h)
      exact ⟨fun h => congr_arg _ (IsLocalization.injective _ hS h),
        fun h => congr_arg _ (IsFractionRing.injective A K h)⟩)

/--
Instance `isFractionRing_range_mapToFractionRing` / 实例 `isFractionRing_range_mapToFractionRing`

English:
instance isFractionRing_range_mapToFractionRing
  signature: (B : Type*) [CommRing B] [Algebra A B]
  body: IsFractionRing.isFractionRing_of_isLocalization S _ _ hS

中文:
实例 isFractionRing_range_mapToFractionRing
  签名: (B : 类型) [交换环 B] [代数 A B]
  定义体: IsFractionRing.isFractionRing_of_isLocalization S _ _ hS

Depends on / 依赖: IsFractionRing, IsFractionRing.isFractionRing_of_isLocalization, isFractionRing_of_isLocalization
-/
instance isFractionRing_range_mapToFractionRing (B : Type*) [CommRing B] [Algebra A B]
    [IsLocalization S B] (hS : S <= A⁰) : IsFractionRing (mapToFractionRing K S B hS).range K :=
  IsFractionRing.isFractionRing_of_isLocalization S _ _ hS

/--
Definition of `subalgebra` / `subalgebra` 的定义

English:
definition subalgebra
  signature: (hS : S <= A⁰)
  body: (mapToFractionRing K S (Localization S) hS).range.copy
{ x | exists (a s : A) (hs : s in S), x = IsLocalization.mk' K a ⟨s, hS hs⟩ } by
    ext
    symm
    apply mem_range_mapToFractionRing_iff

中文:
定义 subalgebra
  签名: (hS : S <= A⁰)
  定义体: (mapToFractionRing K S (Localization S) hS).range.copy
{ x | exists (a s : A) (hs : s in S), x = IsLocalization.mk' K a ⟨s, hS hs⟩ } by
    ext
    symm
    apply mem_range_mapToFractionRing_iff

Depends on / 依赖: IsLocalization, IsLocalization.mk, Localization, mapToFractionRing, mem_range_mapToFractionRing_iff, range.copy
-/
noncomputable def subalgebra (hS : S <= A⁰) : Subalgebra A K :=
  (mapToFractionRing K S (Localization S) hS).range.copy
{ x | exists (a s : A) (hs : s in S), x = IsLocalization.mk' K a ⟨s, hS hs⟩ } by
    ext
    symm
    apply mem_range_mapToFractionRing_iff

namespace subalgebra

/--
Instance `isLocalization_subalgebra` / 实例 `isLocalization_subalgebra`

English:
instance isLocalization_subalgebra
  signature: : IsLocalization S (subalgebra K S hS)
  body: by
  dsimp +instances only [Localization.subalgebra]
  rw [Subalgebra.copy_eq]
  infer_instance

中文:
实例 isLocalization_subalgebra
  签名: : 是Localization S (subalgebra K S hS)
  定义体: by
  dsimp +instances only [Localization.subalgebra]
  rw [Subalgebra.copy_eq]
  infer_instance

Depends on / 依赖: Localization, Localization.subalgebra, Subalgebra, Subalgebra.copy_eq, copy_eq, infer_instance, instances, subalgebra
-/
instance isLocalization_subalgebra : IsLocalization S (subalgebra K S hS) := by
  dsimp +instances only [Localization.subalgebra]
  rw [Subalgebra.copy_eq]
  infer_instance

/--
Instance `isFractionRing` / 实例 `isFractionRing`

English:
instance isFractionRing
  signature: : IsFractionRing (subalgebra K S hS) K
  body: IsFractionRing.isFractionRing_of_isLocalization S _ _ hS

中文:
实例 isFractionRing
  签名: : IsFractionRing (subalgebra K S hS) K
  定义体: IsFractionRing.isFractionRing_of_isLocalization S _ _ hS

Depends on / 依赖: IsFractionRing, IsFractionRing.isFractionRing_of_isLocalization, isFractionRing_of_isLocalization
-/
instance isFractionRing : IsFractionRing (subalgebra K S hS) K :=
  IsFractionRing.isFractionRing_of_isLocalization S _ _ hS

end subalgebra

end CommRing

section Field

variable [Field K] [Algebra A K] [IsFractionRing A K]

namespace subalgebra

/--
theorem `mem_range_mapToFractionRing_iff_ofField` / 定理 `mem_range_mapToFractionRing_iff_ofField`

English:
theorem mem_range_mapToFractionRing_iff_ofField
  statement: (B : Type*) [CommRing B] [Algebra A B]
  proof: by
  rw [mem_range_mapToFractionRing_iff]
  convert! Iff.rfl
  congr
  rw [Units.val_inv_eq_inv_val]
  rfl

中文:
定理 mem_range_mapToFractionRing_iff_ofField
  结论: (B : 类型) [交换环 B] [代数 A B]
  证明: by
  rw [mem_range_mapToFractionRing_iff]
  convert! Iff.rfl
  congr
  rw [Units.val_inv_eq_inv_val]
  rfl

Depends on / 依赖: Iff.rfl, Units.val_inv_eq_inv_val, convert, mem_range_mapToFractionRing_iff, val_inv_eq_inv_val
-/
theorem mem_range_mapToFractionRing_iff_ofField (B : Type*) [CommRing B] [Algebra A B]
    [IsLocalization S B] (x : K) :
    x in (mapToFractionRing K S B hS).range ↔
      exists (a s : A) (_ : s in S), x = algebraMap A K a * (algebraMap A K s)⁻¹ := by
  rw [mem_range_mapToFractionRing_iff]
  convert! Iff.rfl
  congr
  rw [Units.val_inv_eq_inv_val]
  rfl

/--
Definition of `ofField` / `ofField` 的定义

English:
definition ofField
  signature: : Subalgebra A K
  body: (mapToFractionRing K S (Localization S) hS).range.copy
{ x | exists (a s : A) (_ : s in S), x = algebraMap A K a * (algebraMap A K s)⁻¹ } by
    ext
    symm
    apply mem_range_mapToFractionRing_iff_ofField

中文:
定义 ofField
  签名: : 子代数 A K
  定义体: (mapToFractionRing K S (Localization S) hS).range.copy
{ x | exists (a s : A) (_ : s in S), x = algebraMap A K a * (algebraMap A K s)⁻¹ } by
    ext
    symm
    apply mem_range_mapToFractionRing_iff_ofField

Depends on / 依赖: Localization, algebraMap, mapToFractionRing, mem_range_mapToFractionRing_iff_ofField, range.copy
-/
noncomputable def ofField : Subalgebra A K :=
  (mapToFractionRing K S (Localization S) hS).range.copy
{ x | exists (a s : A) (_ : s in S), x = algebraMap A K a * (algebraMap A K s)⁻¹ } by
    ext
    symm
    apply mem_range_mapToFractionRing_iff_ofField

/--
theorem `ofField_eq` / 定理 `ofField_eq`

English:
theorem ofField_eq
  statement: ofField K S hS = subalgebra K S hS
  proof: by
  simp_rw [ofField, subalgebra, Subalgebra.copy_eq]

中文:
定理 ofField_eq
  结论: ofField K S hS = subalgebra K S hS
  证明: by
  simp_rw [ofField, subalgebra, Subalgebra.copy_eq]

Depends on / 依赖: Subalgebra, Subalgebra.copy_eq, copy_eq, ofField, simp_rw, subalgebra
-/
theorem ofField_eq : ofField K S hS = subalgebra K S hS := by
  simp_rw [ofField, subalgebra, Subalgebra.copy_eq]

/--
Instance `isLocalization_ofField` / 实例 `isLocalization_ofField`

English:
instance isLocalization_ofField
  signature: : IsLocalization S (ofField K S hS)
  body: by
  rw [ofField_eq]
  exact isLocalization_subalgebra K S hS

中文:
实例 isLocalization_ofField
  签名: : 是Localization S (ofField K S hS)
  定义体: by
  rw [ofField_eq]
  exact isLocalization_subalgebra K S hS

Depends on / 依赖: isLocalization_subalgebra, ofField_eq
-/
instance isLocalization_ofField : IsLocalization S (ofField K S hS) := by
  rw [ofField_eq]
  exact isLocalization_subalgebra K S hS

instance (S : Subalgebra A K) : IsFractionRing S K := by
  refine IsFractionRing.of_field S K fun z => ?_
  rcases IsFractionRing.div_surjective A z with ⟨x, y, _, eq⟩
  exact ⟨algebraMap A S x, algebraMap A S y, eq.symm⟩

/--
Instance `isFractionRing_ofField` / 实例 `isFractionRing_ofField`

English:
instance isFractionRing_ofField
  signature: : IsFractionRing (ofField K S hS) K
  body: inferInstance

中文:
实例 isFractionRing_ofField
  签名: : IsFractionRing (ofField K S hS) K
  定义体: inferInstance
-/
instance isFractionRing_ofField : IsFractionRing (ofField K S hS) K :=
  inferInstance

end subalgebra

end Field

end Localization
