/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Yongle Hu
-/
module

public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.RingTheory.Ideal.Over

/-!
# Finiteness of quotient modules
-/

public section

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable (P : Ideal B) (p : Ideal A) [P.LiesOver p]

/--
Instance `module_finite_of_liesOver` / 实例 `module_finite_of_liesOver`

English:
instance module_finite_of_liesOver
  signature: [Module.Finite A B]
  body: Module.Finite.of_restrictScalars_finite A (A ⧸ p) (B ⧸ P)

example [Module.Finite A B] : Module.Finite (A ⧸ P.under A) (B ⧸ P) := inferInstance

中文:
实例 module_finite_of_liesOver
  签名: [模.有限 A B]
  定义体: Module.Finite.of_restrictScalars_finite A (A ⧸ p) (B ⧸ P)

example [Module.Finite A B] : Module.Finite (A ⧸ P.under A) (B ⧸ P) := inferInstance

Depends on / 依赖: Finite, Module, Module.Finite.of_restrictScalars_finite, of_restrictScalars_finite
-/
instance module_finite_of_liesOver [Module.Finite A B] : Module.Finite (A ⧸ p) (B ⧸ P) :=
  Module.Finite.of_restrictScalars_finite A (A ⧸ p) (B ⧸ P)

example [Module.Finite A B] : Module.Finite (A ⧸ P.under A) (B ⧸ P) := inferInstance

/--
Instance `algebra_finiteType_of_liesOver` / 实例 `algebra_finiteType_of_liesOver`

English:
instance algebra_finiteType_of_liesOver
  signature: [Algebra.FiniteType A B]
  body: Algebra.FiniteType.of_restrictScalars_finiteType A (A ⧸ p) (B ⧸ P)

中文:
实例 algebra_finiteType_of_liesOver
  签名: [代数.有限型 A B]
  定义体: Algebra.FiniteType.of_restrictScalars_finiteType A (A ⧸ p) (B ⧸ P)

Depends on / 依赖: Algebra, Algebra.FiniteType.of_restrictScalars_finiteType, FiniteType, of_restrictScalars_finiteType
-/
instance algebra_finiteType_of_liesOver [Algebra.FiniteType A B] :
    Algebra.FiniteType (A ⧸ p) (B ⧸ P) :=
  Algebra.FiniteType.of_restrictScalars_finiteType A (A ⧸ p) (B ⧸ P)

/--
Instance `isNoetherian_of_liesOver` / 实例 `isNoetherian_of_liesOver`

English:
instance isNoetherian_of_liesOver
  signature: [IsNoetherian A B]
  body: isNoetherian_of_tower A inferInstance

中文:
实例 isNoetherian_of_liesOver
  签名: [是Noether A B]
  定义体: isNoetherian_of_tower A inferInstance

Depends on / 依赖: isNoetherian_of_tower
-/
instance isNoetherian_of_liesOver [IsNoetherian A B] : IsNoetherian (A ⧸ p) (B ⧸ P) :=
  isNoetherian_of_tower A inferInstance

/--
Instance `QuotientMapQuotient.isNoetherian` / 实例 `QuotientMapQuotient.isNoetherian`

English:
instance QuotientMapQuotient.isNoetherian
  signature: [IsNoetherian A B]
  body: isNoetherian_of_tower A
isNoetherian_of_surjective (Ideal.Quotient.mkₐ A _).toLinearMap
      LinearMap.range_eq_top.mpr Ideal.Quotient.mk_surjective

中文:
实例 QuotientMapQuotient.isNoetherian
  签名: [是Noether A B]
  定义体: isNoetherian_of_tower A
isNoetherian_of_surjective (Ideal.Quotient.mkₐ A _).toLinearMap
      LinearMap.range_eq_top.mpr Ideal.Quotient.mk_surjective

Depends on / 依赖: Ideal.Quotient.mk, Ideal.Quotient.mk_surjective, LinearMap, LinearMap.range_eq_top.mpr, Quotient, isNoetherian_of_surjective, isNoetherian_of_tower, mk_surjective, range_eq_top, toLinearMap
-/
instance QuotientMapQuotient.isNoetherian [IsNoetherian A B] :
    IsNoetherian (A ⧸ p) (B ⧸ p.map (algebraMap A B)) :=
isNoetherian_of_tower A
isNoetherian_of_surjective (Ideal.Quotient.mkₐ A _).toLinearMap
      LinearMap.range_eq_top.mpr Ideal.Quotient.mk_surjective
