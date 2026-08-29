/-
Copyright (c) 2025 Michal Staromiejski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Staromiejski
-/
module

public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-!
# Algebras over Artinian rings

In this file we collect results about algebras over Artinian rings.
-/

public section

namespace IsArtinianRing

variable {R A : Type*}
variable [CommRing R] [IsArtinianRing R] [Ring A] [Algebra R A]

open nonZeroDivisors

/--
theorem `isUnit_of_isIntegral_of_nonZeroDivisor` / 定理 `isUnit_of_isIntegral_of_nonZeroDivisor`

English:
theorem isUnit_of_isIntegral_of_nonZeroDivisor
  statement: {a : A}
  proof: let B := Algebra.adjoin R {a}
  let b : B := ⟨a, Algebra.self_mem_adjoin_singleton R a⟩
  haveI : Module.Finite R B := Algebra.finite_adjoin_simple_of_isIntegral hi
  haveI : IsArtinianRing B := isArtinian_of_tower R inferInstance
  have hinj : Function.Injective B.subtype := Subtype.val_injective
 

中文:
定理 isUnit_of_is整数egral_of_nonZeroDivisor
  结论: {a : A}
  证明: let B := Algebra.adjoin R {a}
  let b : B := ⟨a, Algebra.self_mem_adjoin_singleton R a⟩
  haveI : Module.Finite R B := Algebra.finite_adjoin_simple_of_isIntegral hi
  haveI : IsArtinianRing B := isArtinian_of_tower R inferInstance
  have hinj : Function.Injective B.subtype := Subtype.val_injective
 

Depends on / 依赖: Algebra, Algebra.adjoin, Algebra.finite_adjoin_simple_of_isIntegral, Algebra.self_mem_adjoin_singleton, B.subtype, Finite, Function, Function.Injective, Injective, IsArtinianRing, Module, Module.Finite, Subtype, Subtype.val_injective, adjoin, comap_nonZeroDivisors_le_of_injective, finite_adjoin_simple_of_isIntegral, isArtinian_of_tower, isUnit_of_mem_nonZeroDivisors, self_mem_adjoin_singleton
-/
theorem isUnit_of_isIntegral_of_nonZeroDivisor {a : A}
    (hi : IsIntegral R a) (ha : a in A⁰) : IsUnit a :=
  let B := Algebra.adjoin R {a}
  let b : B := ⟨a, Algebra.self_mem_adjoin_singleton R a⟩
  haveI : Module.Finite R B := Algebra.finite_adjoin_simple_of_isIntegral hi
  haveI : IsArtinianRing B := isArtinian_of_tower R inferInstance
  have hinj : Function.Injective B.subtype := Subtype.val_injective
  have hb : b in B⁰ := comap_nonZeroDivisors_le_of_injective hinj ha
  (isUnit_of_mem_nonZeroDivisors hb).map B.subtype

/--
theorem `isUnit_iff_nonZeroDivisor_of_isIntegral` / 定理 `isUnit_iff_nonZeroDivisor_of_isIntegral`

English:
theorem isUnit_iff_nonZeroDivisor_of_isIntegral
  statement: {a : A}
  proof: ⟨IsUnit.mem_nonZeroDivisors, isUnit_of_isIntegral_of_nonZeroDivisor hi⟩

中文:
定理 isUnit_iff_nonZeroDivisor_of_is整数egral
  结论: {a : A}
  证明: ⟨IsUnit.mem_nonZeroDivisors, isUnit_of_isIntegral_of_nonZeroDivisor hi⟩

Depends on / 依赖: IsUnit, IsUnit.mem_nonZeroDivisors, isUnit_of_isIntegral_of_nonZeroDivisor, mem_nonZeroDivisors
-/
theorem isUnit_iff_nonZeroDivisor_of_isIntegral {a : A}
    (hi : IsIntegral R a) : IsUnit a ↔ a in A⁰ :=
  ⟨IsUnit.mem_nonZeroDivisors, isUnit_of_isIntegral_of_nonZeroDivisor hi⟩

/--
theorem `isUnit_of_nonZeroDivisor_of_isIntegral'` / 定理 `isUnit_of_nonZeroDivisor_of_isIntegral'`

English:
theorem isUnit_of_nonZeroDivisor_of_isIntegral'
  statement: [Algebra.IsIntegral R A] {a : A}
  proof: isUnit_of_isIntegral_of_nonZeroDivisor (R := R) (Algebra.IsIntegral.isIntegral a) ha

中文:
定理 isUnit_of_nonZeroDivisor_of_is整数egral'
  结论: [代数.是整 R A] {a : A}
  证明: isUnit_of_isIntegral_of_nonZeroDivisor (R := R) (Algebra.IsIntegral.isIntegral a) ha

Depends on / 依赖: Algebra, Algebra.IsIntegral.isIntegral, IsIntegral, isIntegral, isUnit_of_isIntegral_of_nonZeroDivisor
-/
theorem isUnit_of_nonZeroDivisor_of_isIntegral' [Algebra.IsIntegral R A] {a : A}
    (ha : a in A⁰) : IsUnit a :=
  isUnit_of_isIntegral_of_nonZeroDivisor (R := R) (Algebra.IsIntegral.isIntegral a) ha

/--
theorem `isUnit_iff_nonZeroDivisor_of_isIntegral'` / 定理 `isUnit_iff_nonZeroDivisor_of_isIntegral'`

English:
theorem isUnit_iff_nonZeroDivisor_of_isIntegral'
  given: [Algebra.IsIntegral R A] {a : A}
  proof: isUnit_iff_nonZeroDivisor_of_isIntegral (R := R) (Algebra.IsIntegral.isIntegral a)

中文:
定理 isUnit_iff_nonZeroDivisor_of_is整数egral'
  条件: [代数.是整 R A] {a : A}
  证明: isUnit_iff_nonZeroDivisor_of_isIntegral (R := R) (Algebra.IsIntegral.isIntegral a)

Depends on / 依赖: Algebra, Algebra.IsIntegral.isIntegral, IsIntegral, isIntegral, isUnit_iff_nonZeroDivisor_of_isIntegral
-/
theorem isUnit_iff_nonZeroDivisor_of_isIntegral' [Algebra.IsIntegral R A] {a : A} :
    IsUnit a ↔ a in A⁰ :=
  isUnit_iff_nonZeroDivisor_of_isIntegral (R := R) (Algebra.IsIntegral.isIntegral a)

/--
theorem `isUnit_submonoid_eq_of_isIntegral` / 定理 `isUnit_submonoid_eq_of_isIntegral`

English:
theorem isUnit_submonoid_eq_of_isIntegral
  given: [Algebra.IsIntegral R A]
  statement: IsUnit.submonoid A = A⁰
  proof: by
  ext; simpa [IsUnit.mem_submonoid_iff] using isUnit_iff_nonZeroDivisor_of_isIntegral' (R := R)

中文:
定理 isUnit_submonoid_eq_of_is整数egral
  条件: [代数.是整 R A]
  结论: 是单位.submonoid A = A⁰
  证明: by
  ext; simpa [IsUnit.mem_submonoid_iff] using isUnit_iff_nonZeroDivisor_of_isIntegral' (R := R)

Depends on / 依赖: IsUnit, IsUnit.mem_submonoid_iff, isUnit_iff_nonZeroDivisor_of_isIntegral, mem_submonoid_iff
-/
theorem isUnit_submonoid_eq_of_isIntegral [Algebra.IsIntegral R A] : IsUnit.submonoid A = A⁰ := by
  ext; simpa [IsUnit.mem_submonoid_iff] using isUnit_iff_nonZeroDivisor_of_isIntegral' (R := R)

end IsArtinianRing
