/-
Copyright (c) 2022 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Tower
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Algebra towers for multivariate polynomial

This file proves some basic results about the algebra tower structure for the type
`MvPolynomial σ R`.

This structure itself is provided elsewhere as `MvPolynomial.isScalarTower`

When you update this file, you can also try to make a corresponding update in
`RingTheory.Polynomial.Tower`.
-/

public section


variable (R A B : Type*) {σ : Type*}

namespace MvPolynomial

section Semiring

variable [CommSemiring R] [CommSemiring A] [CommSemiring B]
variable [Algebra R A] [Algebra A B] [Algebra R B]
variable [IsScalarTower R A B]
variable {R B}

/--
theorem `aeval_map_algebraMap` / 定理 `aeval_map_algebraMap`

English:
theorem aeval_map_algebraMap
  given: (x : σ -> B) (p : MvPolynomial σ R)
  proof: by
  rw [aeval_def]; rw [aeval_def]; rw [eval₂_map]; rw [IsScalarTower.algebraMap_eq R A B]

中文:
定理 aeval_map_algebraMap
  条件: (x : σ -> B) (p : MvPolynomial σ R)
  证明: by
  rw [aeval_def]; rw [aeval_def]; rw [eval₂_map]; rw [IsScalarTower.algebraMap_eq R A B]

Depends on / 依赖: IsScalarTower, IsScalarTower.algebraMap_eq, aeval_def, algebraMap_eq
-/
theorem aeval_map_algebraMap (x : σ -> B) (p : MvPolynomial σ R) :
    aeval x (map (algebraMap R A) p) = aeval x p := by
  rw [aeval_def]; rw [aeval_def]; rw [eval₂_map]; rw [IsScalarTower.algebraMap_eq R A B]

end Semiring

section CommSemiring

variable [CommSemiring R] [CommSemiring A] [CommSemiring B]
variable [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
variable {R A}

/--
theorem `aeval_algebraMap_apply` / 定理 `aeval_algebraMap_apply`

English:
theorem aeval_algebraMap_apply
  given: (x : σ -> A) (p : MvPolynomial σ R)
  proof: by
  rw [aeval_def]; rw [aeval_def]; rw [← coe_eval₂Hom]; rw [← coe_eval₂Hom]; rw [map_eval₂Hom]; rw [←
    IsScalarTower.algebraMap_eq]; rw [Function.comp_def]

@[simp]

中文:
定理 aeval_algebraMap_apply
  条件: (x : σ -> A) (p : MvPolynomial σ R)
  证明: by
  rw [aeval_def]; rw [aeval_def]; rw [← coe_eval₂Hom]; rw [← coe_eval₂Hom]; rw [map_eval₂Hom]; rw [←
    IsScalarTower.algebraMap_eq]; rw [Function.comp_def]

@[simp]

Depends on / 依赖: Function, Function.comp_def, IsScalarTower, IsScalarTower.algebraMap_eq, aeval_def, algebraMap_eq, comp_def
-/
theorem aeval_algebraMap_apply (x : σ -> A) (p : MvPolynomial σ R) :
    aeval (algebraMap A B ∘ x) p = algebraMap A B (MvPolynomial.aeval x p) := by
  rw [aeval_def]; rw [aeval_def]; rw [← coe_eval₂Hom]; rw [← coe_eval₂Hom]; rw [map_eval₂Hom]; rw [←
    IsScalarTower.algebraMap_eq]; rw [Function.comp_def]

@[simp]
/--
lemma `aeval_C_comp_left` / 引理 `aeval_C_comp_left`

English:
lemma aeval_C_comp_left
  given: {ι : Type*} (f : σ -> A) (p : MvPolynomial σ R)
  proof: aeval_algebraMap_apply ..

中文:
引理 aeval_C_comp_left
  条件: {ι : 类型} (f : σ -> A) (p : MvPolynomial σ R)
  证明: aeval_algebraMap_apply ..
-/
lemma aeval_C_comp_left {ι : Type*} (f : σ -> A) (p : MvPolynomial σ R) :
    aeval (C (σ := ι) ∘ f) p = C (aeval f p) :=
  aeval_algebraMap_apply ..

/--
lemma `aeval_algebraMap_eq_zero_iff` / 引理 `aeval_algebraMap_eq_zero_iff`

English:
lemma aeval_algebraMap_eq_zero_iff
  statement: [IsDomain A] [Module.IsTorsionFree A B] [Nontrivial B]
  proof: by
  rw [aeval_algebraMap_apply]; rw [Algebra.algebraMap_eq_smul_one]; rw [smul_eq_zero]; rw [iff_false_intro (one_ne_zero' B)]; rw [or_false]

中文:
引理 aeval_algebraMap_eq_zero_iff
  结论: [IsDomain A] [Module.IsTorsionFree A B] [Nontrivial B]
  证明: by
  rw [aeval_algebraMap_apply]; rw [Algebra.algebraMap_eq_smul_one]; rw [smul_eq_zero]; rw [iff_false_intro (one_ne_zero' B)]; rw [or_false]

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, aeval_algebraMap_apply, algebraMap_eq_smul_one, iff_false_intro, one_ne_zero, or_false, smul_eq_zero
-/
lemma aeval_algebraMap_eq_zero_iff [IsDomain A] [Module.IsTorsionFree A B] [Nontrivial B]
    (x : σ -> A) (p : MvPolynomial σ R) : aeval (algebraMap A B ∘ x) p = 0 ↔ aeval x p = 0 := by
  rw [aeval_algebraMap_apply]; rw [Algebra.algebraMap_eq_smul_one]; rw [smul_eq_zero]; rw [iff_false_intro (one_ne_zero' B)]; rw [or_false]

/--
theorem `aeval_algebraMap_eq_zero_iff_of_injective` / 定理 `aeval_algebraMap_eq_zero_iff_of_injective`

English:
theorem aeval_algebraMap_eq_zero_iff_of_injective
  statement: {x : σ -> A} {p : MvPolynomial σ R}
  proof: by
  rw [aeval_algebraMap_apply]; rw [← (algebraMap A B).map_zero]; rw [h.eq_iff]

中文:
定理 aeval_algebraMap_eq_zero_iff_of_injective
  结论: {x : σ -> A} {p : MvPolynomial σ R}
  证明: by
  rw [aeval_algebraMap_apply]; rw [← (algebraMap A B).map_zero]; rw [h.eq_iff]

Depends on / 依赖: aeval_algebraMap_apply, algebraMap, eq_iff, h.eq_iff, map_zero
-/
theorem aeval_algebraMap_eq_zero_iff_of_injective {x : σ -> A} {p : MvPolynomial σ R}
    (h : Function.Injective (algebraMap A B)) :
    aeval (algebraMap A B ∘ x) p = 0 ↔ aeval x p = 0 := by
  rw [aeval_algebraMap_apply]; rw [← (algebraMap A B).map_zero]; rw [h.eq_iff]

end CommSemiring

end MvPolynomial

namespace Subalgebra

open MvPolynomial

section CommSemiring

variable {R A} [CommSemiring R] [CommSemiring A] [Algebra R A]

@[simp]
/--
theorem `mvPolynomial_aeval_coe` / 定理 `mvPolynomial_aeval_coe`

English:
theorem mvPolynomial_aeval_coe
  given: (S : Subalgebra R A) (x : σ -> S) (p : MvPolynomial σ R)
  proof: by convert! aeval_algebraMap_apply A x p

中文:
定理 mvPolynomial_aeval_coe
  条件: (S : Subalgebra R A) (x : σ -> S) (p : MvPolynomial σ R)
  证明: by convert! aeval_algebraMap_apply A x p

Depends on / 依赖: aeval_algebraMap_apply, convert
-/
theorem mvPolynomial_aeval_coe (S : Subalgebra R A) (x : σ -> S) (p : MvPolynomial σ R) :
    aeval (fun i => (x i : A)) p = aeval x p := by convert! aeval_algebraMap_apply A x p

end CommSemiring

end Subalgebra
