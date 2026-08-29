/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yuyang Zhao
-/
module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Algebra towers for polynomial

This file proves some basic results about the algebra tower structure for the type `R[X]`.

This structure itself is provided elsewhere as `Polynomial.isScalarTower`

When you update this file, you can also try to make a corresponding update in
`RingTheory.MvPolynomial.Tower`.
-/

public section


open Module

variable (R A B : Type*)

namespace Polynomial

section Semiring

variable [CommSemiring R] [CommSemiring A] [Semiring B]
variable [Algebra R A] [Algebra A B] [Algebra R B]
variable [IsScalarTower R A B]
variable {R B}

@[simp]
/--
theorem `aeval_map_algebraMap` / 定理 `aeval_map_algebraMap`

English:
theorem aeval_map_algebraMap
  given: (x : B) (p : R[X])
  statement: aeval x (map (algebraMap R A) p) = aeval x p
  proof: by
  rw [aeval_def]; rw [aeval_def]; rw [eval₂_map]; rw [IsScalarTower.algebraMap_eq R A B]

中文:
定理 aeval_map_algebraMap
  条件: (x : B) (p : R[X])
  结论: aeval x (map (algebraMap R A) p) = aeval x p
  证明: by
  rw [aeval_def]; rw [aeval_def]; rw [eval₂_map]; rw [IsScalarTower.algebraMap_eq R A B]

Depends on / 依赖: IsScalarTower, IsScalarTower.algebraMap_eq, aeval_def, algebraMap_eq
-/
theorem aeval_map_algebraMap (x : B) (p : R[X]) : aeval x (map (algebraMap R A) p) = aeval x p := by
  rw [aeval_def]; rw [aeval_def]; rw [eval₂_map]; rw [IsScalarTower.algebraMap_eq R A B]

end Semiring

section CommSemiring

variable [CommSemiring R] [CommSemiring A] [Semiring B]
variable [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
variable {R A}

/--
theorem `aeval_algebraMap_apply` / 定理 `aeval_algebraMap_apply`

English:
theorem aeval_algebraMap_apply
  given: (x : A) (p : R[X])
  proof: by
  rw [aeval_def]; rw [aeval_def]; rw [hom_eval₂]; rw [← IsScalarTower.algebraMap_eq]

@[simp]

中文:
定理 aeval_algebraMap_apply
  条件: (x : A) (p : R[X])
  证明: by
  rw [aeval_def]; rw [aeval_def]; rw [hom_eval₂]; rw [← IsScalarTower.algebraMap_eq]

@[simp]

Depends on / 依赖: IsScalarTower, IsScalarTower.algebraMap_eq, aeval_def, algebraMap_eq
-/
theorem aeval_algebraMap_apply (x : A) (p : R[X]) :
    aeval (algebraMap A B x) p = algebraMap A B (aeval x p) := by
  rw [aeval_def]; rw [aeval_def]; rw [hom_eval₂]; rw [← IsScalarTower.algebraMap_eq]

@[simp]
/--
theorem `aeval_algebraMap_eq_zero_iff` / 定理 `aeval_algebraMap_eq_zero_iff`

English:
theorem aeval_algebraMap_eq_zero_iff
  statement: [IsDomain A] [IsTorsionFree A B] [Nontrivial B] (x : A)
  proof: by
  rw [aeval_algebraMap_apply]; rw [Algebra.algebraMap_eq_smul_one]; rw [smul_eq_zero]; rw [iff_false_intro (one_ne_zero' B)]; rw [or_false]

中文:
定理 aeval_algebraMap_eq_zero_iff
  结论: [是整环 A] [是无挠 A B] [非平凡 B] (x : A)
  证明: by
  rw [aeval_algebraMap_apply]; rw [Algebra.algebraMap_eq_smul_one]; rw [smul_eq_zero]; rw [iff_false_intro (one_ne_zero' B)]; rw [or_false]

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, aeval_algebraMap_apply, algebraMap_eq_smul_one, iff_false_intro, one_ne_zero, or_false, smul_eq_zero
-/
theorem aeval_algebraMap_eq_zero_iff [IsDomain A] [IsTorsionFree A B] [Nontrivial B] (x : A)
    (p : R[X]) : aeval (algebraMap A B x) p = 0 ↔ aeval x p = 0 := by
  rw [aeval_algebraMap_apply]; rw [Algebra.algebraMap_eq_smul_one]; rw [smul_eq_zero]; rw [iff_false_intro (one_ne_zero' B)]; rw [or_false]

variable {B}

/--
theorem `aeval_algebraMap_eq_zero_iff_of_injective` / 定理 `aeval_algebraMap_eq_zero_iff_of_injective`

English:
theorem aeval_algebraMap_eq_zero_iff_of_injective
  statement: {x : A} {p : R[X]}
  proof: by
  rw [aeval_algebraMap_apply]; rw [← (algebraMap A B).map_zero]; rw [h.eq_iff]

中文:
定理 aeval_algebraMap_eq_zero_iff_of_injective
  结论: {x : A} {p : R[X]}
  证明: by
  rw [aeval_algebraMap_apply]; rw [← (algebraMap A B).map_zero]; rw [h.eq_iff]

Depends on / 依赖: aeval_algebraMap_apply, algebraMap, eq_iff, h.eq_iff, map_zero
-/
theorem aeval_algebraMap_eq_zero_iff_of_injective {x : A} {p : R[X]}
    (h : Function.Injective (algebraMap A B)) : aeval (algebraMap A B x) p = 0 ↔ aeval x p = 0 := by
  rw [aeval_algebraMap_apply]; rw [← (algebraMap A B).map_zero]; rw [h.eq_iff]

end CommSemiring

end Polynomial

namespace Subalgebra

open Polynomial

section CommSemiring

variable {R A} [CommSemiring R] [CommSemiring A] [Algebra R A]

@[simp]
/--
theorem `aeval_coe` / 定理 `aeval_coe`

English:
theorem aeval_coe
  given: (S : Subalgebra R A) (x : S) (p : R[X])
  statement: aeval (x : A) p = aeval x p
  proof: aeval_algebraMap_apply A x p

中文:
定理 aeval_coe
  条件: (S : 子代数 R A) (x : S) (p : R[X])
  结论: aeval (x : A) p = aeval x p
  证明: aeval_algebraMap_apply A x p

Depends on / 依赖: aeval_algebraMap_apply
-/
theorem aeval_coe (S : Subalgebra R A) (x : S) (p : R[X]) : aeval (x : A) p = aeval x p :=
  aeval_algebraMap_apply A x p

end CommSemiring

end Subalgebra

namespace Polynomial

variable {R A} [CommSemiring R] [CommRing A] [Algebra R A]

/--
theorem `aeval_root_of_mapAlg_eq_multiset_prod_X_sub_C` / 定理 `aeval_root_of_mapAlg_eq_multiset_prod_X_sub_C`

English:
theorem aeval_root_of_mapAlg_eq_multiset_prod_X_sub_C
  statement: (s : Multiset A) {x : A} (hx : x in s)
  proof: by
  rw [← aeval_map_algebraMap A]; rw [← mapAlg_eq_map]; rw [hp]; rw [map_multiset_prod]; rw [Multiset.prod_eq_zero]
  rw [Multiset.map_map]; rw [Multiset.mem_map]
  exact ⟨x, hx, by simp⟩

中文:
定理 aeval_root_of_mapAlg_eq_multiset_prod_X_sub_C
  结论: (s : Multiset A) {x : A} (hx : x in s)
  证明: by
  rw [← aeval_map_algebraMap A]; rw [← mapAlg_eq_map]; rw [hp]; rw [map_multiset_prod]; rw [Multiset.prod_eq_zero]
  rw [Multiset.map_map]; rw [Multiset.mem_map]
  exact ⟨x, hx, by simp⟩

Depends on / 依赖: Multiset, Multiset.map_map, Multiset.mem_map, Multiset.prod_eq_zero, aeval_map_algebraMap, mapAlg_eq_map, map_map, map_multiset_prod, mem_map, prod_eq_zero
-/
theorem aeval_root_of_mapAlg_eq_multiset_prod_X_sub_C (s : Multiset A) {x : A} (hx : x in s)
    {p : R[X]} (hp : p.mapAlg R A = (s.map (X - C ·)).prod) : aeval x p = 0 := by
  rw [← aeval_map_algebraMap A]; rw [← mapAlg_eq_map]; rw [hp]; rw [map_multiset_prod]; rw [Multiset.prod_eq_zero]
  rw [Multiset.map_map]; rw [Multiset.mem_map]
  exact ⟨x, hx, by simp⟩

end Polynomial
