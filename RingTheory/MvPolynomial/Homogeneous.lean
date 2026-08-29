/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Eric Wieser
-/
module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.SetTheory.Cardinal.Basic
public import Mathlib.RingTheory.Ideal.Span

/-!
# Homogeneous polynomials

A multivariate polynomial `φ` is homogeneous of degree `n`
if all monomials occurring in `φ` have degree `n`.

## Main definitions/lemmas

* `IsHomogeneous φ n`: a predicate that asserts that `φ` is homogeneous of degree `n`.
* `homogeneousSubmodule σ R n`: the submodule of homogeneous polynomials of degree `n`.
* `homogeneousComponent n`: the additive morphism that projects polynomials onto
  their summand that is homogeneous of degree `n`.
* `sum_homogeneousComponent`: every polynomial is the sum of its homogeneous components.

## Library notes

* The `MvPolynomial.weightedGradedAlgebra` instance provides a `GradedAlgebra` structure, yielding
  the isomorphism `MvPolynomial σ R ≃ₐ[R] ⨁ m, weightedHomogeneousSubmodule R w m` for a weight
  function `w`.
* The special case with `w = 1` of the above yields the algebra isomorphism
  `MvPolynomial σ R ≃ₐ[R] ⨁ i, homogeneousSubmodule σ R i`.
-/

@[expose] public section


namespace MvPolynomial

variable {σ : Type*} {τ : Type*} {R : Type*} {S : Type*}

open Finsupp

/--
Definition of `IsHomogeneous` / `IsHomogeneous` 的定义

English:
definition IsHomogeneous
  signature: [CommSemiring R] (φ : MvPolynomial σ R) (n : Nat)
  body: IsWeightedHomogeneous 1 φ n

中文:
定义 IsHomogeneous
  签名: [交换半环 R] (φ : 多元多项式 σ R) (n : 自然数)
  定义体: IsWeightedHomogeneous 1 φ n

Depends on / 依赖: IsWeightedHomogeneous
-/
def IsHomogeneous [CommSemiring R] (φ : MvPolynomial σ R) (n : Nat) :=
  IsWeightedHomogeneous 1 φ n

variable [CommSemiring R]

/-- The `degrees` of a polynomial `p` is a special case of the `weightedTotalDegree` of `p` where
  the weights are singletons containing each variable. -/
@[simp]
/--
theorem `weightedTotalDegree_singleton` / 定理 `weightedTotalDegree_singleton`

English:
theorem weightedTotalDegree_singleton
  given: [DecidableEq σ] (p : MvPolynomial σ R)
  proof: by
  rw [degrees_def]; rfl

中文:
定理 weightedTotalDegree_singleton
  条件: [DecidableEq σ] (p : 多元多项式 σ R)
  证明: by
  rw [degrees_def]; rfl

Depends on / 依赖: ProfiniteGrp, ProfiniteGrp.Hom, degrees_def
-/
theorem weightedTotalDegree_singleton [DecidableEq σ] (p : MvPolynomial σ R) :
    weightedTotalDegree (fun i => {i}) p = degrees p := by
  rw [degrees_def]; rfl

/--
theorem `weightedTotalDegree_one` / 定理 `weightedTotalDegree_one`

English:
theorem weightedTotalDegree_one
  given: (φ : MvPolynomial σ R)
  proof: by
  simp only [totalDegree, weightedTotalDegree, weight, LinearMap.toAddMonoidHom_coe,
    linearCombination, Pi.one_apply, Finsupp.coe_lsum, LinearMap.coe_smulRight, LinearMap.id_coe,
    id, smul_eq_mul, mul_one]

中文:
定理 weightedTotalDegree_one
  条件: (φ : 多元多项式 σ R)
  证明: by
  simp only [totalDegree, weightedTotalDegree, weight, LinearMap.toAddMonoidHom_coe,
    linearCombination, Pi.one_apply, Finsupp.coe_lsum, LinearMap.coe_smulRight, LinearMap.id_coe,
    id, smul_eq_mul, mul_one]

Depends on / 依赖: Finsupp, Finsupp.coe_lsum, LinearMap, LinearMap.coe_smulRight, LinearMap.id_coe, LinearMap.toAddMonoidHom_coe, Pi.one_apply, coe_lsum, coe_smulRight, f.hom, id_coe, linearCombination, mul_one, one_apply, smul_eq_mul, toAddMonoidHom_coe, totalDegree, weight, weightedTotalDegree
-/
theorem weightedTotalDegree_one (φ : MvPolynomial σ R) :
    weightedTotalDegree (1 : σ -> Nat) φ = φ.totalDegree := by
  simp only [totalDegree, weightedTotalDegree, weight, LinearMap.toAddMonoidHom_coe,
    linearCombination, Pi.one_apply, Finsupp.coe_lsum, LinearMap.coe_smulRight, LinearMap.id_coe,
    id, smul_eq_mul, mul_one]

/-- The `degreeOf` a variable `i` for a polynomial `p` is a special case of the
  `weightedTotalDegree` of `p` where `i` has the only nonzero weight and that weight is `1`. -/
@[simp]
/--
theorem `weightedTotalDegree_piSingle` / 定理 `weightedTotalDegree_piSingle`

English:
theorem weightedTotalDegree_piSingle
  given: [DecidableEq σ] (i : σ) (p : MvPolynomial σ R)
  proof: by
  simp only [weightedTotalDegree, weight, linearCombination, Pi.single_apply, degreeOf, degrees,
    Multiset.count_finset_sup]
  congr; ext d
  simp +contextual

中文:
定理 weightedTotalDegree_piSingle
  条件: [DecidableEq σ] (i : σ) (p : 多元多项式 σ R)
  证明: by
  simp only [weightedTotalDegree, weight, linearCombination, Pi.single_apply, degreeOf, degrees,
    Multiset.count_finset_sup]
  congr; ext d
  simp +contextual

Depends on / 依赖: Multiset, Multiset.count_finset_sup, Pi.single_apply, contextual, count_finset_sup, degreeOf, degrees, linearCombination, single_apply, weight, weightedTotalDegree
-/
theorem weightedTotalDegree_piSingle [DecidableEq σ] (i : σ) (p : MvPolynomial σ R) :
    weightedTotalDegree (Pi.single i 1) p = degreeOf i p := by
  simp only [weightedTotalDegree, weight, linearCombination, Pi.single_apply, degreeOf, degrees,
    Multiset.count_finset_sup]
  congr; ext d
  simp +contextual

/--
theorem `weightedTotalDegree_rename_of_injective` / 定理 `weightedTotalDegree_rename_of_injective`

English:
theorem weightedTotalDegree_rename_of_injective
  statement: {σ τ : Type*} {e : σ -> τ}
  proof: by
  classical
  unfold weightedTotalDegree
  rw [support_rename_of_injective he]; rw [Finset.sup_image]
  congr; ext; unfold weight; simp

中文:
定理 weightedTotalDegree_rename_of_injective
  结论: {σ τ : 类型} {e : σ -> τ}
  证明: by
  classical
  unfold weightedTotalDegree
  rw [support_rename_of_injective he]; rw [Finset.sup_image]
  congr; ext; unfold weight; simp

Depends on / 依赖: Finset, Finset.sup_image, classical, sup_image, support_rename_of_injective, weight, weightedTotalDegree
-/
theorem weightedTotalDegree_rename_of_injective {σ τ : Type*} {e : σ -> τ}
    {w : τ -> Nat} {P : MvPolynomial σ R} (he : Function.Injective e) :
    weightedTotalDegree w (rename e P) = weightedTotalDegree (w ∘ e) P := by
  classical
  unfold weightedTotalDegree
  rw [support_rename_of_injective he]; rw [Finset.sup_image]
  congr; ext; unfold weight; simp

variable (σ R)

/--
Definition of `homogeneousSubmodule` / `homogeneousSubmodule` 的定义

English:
definition homogeneousSubmodule
  signature: (n : Nat)
  body: { x | x.IsHomogeneous n }
  __ := weightedHomogeneousSubmodule R 1 n

@[simp]

中文:
定义 homogeneousSubmodule
  签名: (n : 自然数)
  定义体: { x | x.IsHomogeneous n }
  __ := weightedHomogeneousSubmodule R 1 n

@[simp]

Depends on / 依赖: IsHomogeneous, f.hom, x.IsHomogeneous
-/
def homogeneousSubmodule (n : Nat) : Submodule R (MvPolynomial σ R) where
  carrier := { x | x.IsHomogeneous n }
  __ := weightedHomogeneousSubmodule R 1 n

@[simp]
/--
lemma `weightedHomogeneousSubmodule_one` / 引理 `weightedHomogeneousSubmodule_one`

English:
lemma weightedHomogeneousSubmodule_one
  given: (n : Nat)
  proof: rfl

中文:
引理 weightedHomogeneousSubmodule_one
  条件: (n : 自然数)
  证明: rfl
-/
lemma weightedHomogeneousSubmodule_one (n : Nat) :
    weightedHomogeneousSubmodule R 1 n = homogeneousSubmodule σ R n := rfl

variable {σ R}

@[simp]
/--
theorem `mem_homogeneousSubmodule` / 定理 `mem_homogeneousSubmodule`

English:
theorem mem_homogeneousSubmodule
  given: (n : Nat) (p : MvPolynomial σ R)
  proof: Iff.rfl

中文:
定理 mem_homogeneousSubmodule
  条件: (n : 自然数) (p : 多元多项式 σ R)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_homogeneousSubmodule (n : Nat) (p : MvPolynomial σ R) :
    p in homogeneousSubmodule σ R n ↔ p.IsHomogeneous n := Iff.rfl

variable (σ R)

/--
theorem `homogeneousSubmodule_eq_finsupp_supported` / 定理 `homogeneousSubmodule_eq_finsupp_supported`

English:
theorem homogeneousSubmodule_eq_finsupp_supported
  given: (n : Nat)
  proof: by
  simp_rw [degree_eq_weight_one]
  exact weightedHomogeneousSubmodule_eq_finsupp_supported R 1 n

中文:
定理 homogeneousSubmodule_eq_finsupp_supported
  条件: (n : 自然数)
  证明: by
  simp_rw [degree_eq_weight_one]
  exact weightedHomogeneousSubmodule_eq_finsupp_supported R 1 n

Depends on / 依赖: degree_eq_weight_one, simp_rw, weightedHomogeneousSubmodule_eq_finsupp_supported
-/
theorem homogeneousSubmodule_eq_finsupp_supported (n : Nat) :
    homogeneousSubmodule σ R n = AddMonoidAlgebra.supported _ R {d | d.degree = n} := by
  simp_rw [degree_eq_weight_one]
  exact weightedHomogeneousSubmodule_eq_finsupp_supported R 1 n

/--
lemma `homogeneousSubmodule_fg` / 引理 `homogeneousSubmodule_fg`

English:
lemma homogeneousSubmodule_fg
  given: [Finite σ] (n : Nat)
  proof: weightedHomogeneousSubmodule_fg R (1 : σ -> Nat) (by simp) n

中文:
引理 homogeneousSubmodule_fg
  条件: [有限 σ] (n : 自然数)
  证明: weightedHomogeneousSubmodule_fg R (1 : σ -> Nat) (by simp) n

Depends on / 依赖: weightedHomogeneousSubmodule_fg
-/
lemma homogeneousSubmodule_fg [Finite σ] (n : Nat) :
    (homogeneousSubmodule σ R n).FG :=
  weightedHomogeneousSubmodule_fg R (1 : σ -> Nat) (by simp) n

variable {σ R}

set_option backward.isDefEq.respectTransparency false in
/--
theorem `homogeneousSubmodule_mul` / 定理 `homogeneousSubmodule_mul`

English:
theorem homogeneousSubmodule_mul
  given: (m n : Nat)
  proof: weightedHomogeneousSubmodule_mul 1 m n

中文:
定理 homogeneousSubmodule_mul
  条件: (m n : 自然数)
  证明: weightedHomogeneousSubmodule_mul 1 m n

Depends on / 依赖: weightedHomogeneousSubmodule_mul
-/
theorem homogeneousSubmodule_mul (m n : Nat) :
    homogeneousSubmodule σ R m * homogeneousSubmodule σ R n <= homogeneousSubmodule σ R (m + n) :=
  weightedHomogeneousSubmodule_mul 1 m n

set_option backward.isDefEq.respectTransparency false in
/--
lemma `homogeneousSubmodule_one_eq_span_X` / 引理 `homogeneousSubmodule_one_eq_span_X`

English:
lemma homogeneousSubmodule_one_eq_span_X
  proof: by
  simp [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported,
    AddMonoidAlgebra.supported_eq_span_single, MvPolynomial.single_eq_monomial,
    ← Finsupp.range_single_one, ← Set.range_comp, Function.comp_def, ← X_pow_eq_monomial]

中文:
引理 homogeneousSubmodule_one_eq_span_X
  证明: by
  simp [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported,
    AddMonoidAlgebra.supported_eq_span_single, MvPolynomial.single_eq_monomial,
    ← Finsupp.range_single_one, ← Set.range_comp, Function.comp_def, ← X_pow_eq_monomial]

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.supported_eq_span_single, Finsupp, Finsupp.range_single_one, Function, Function.comp_def, MvPolynomial, MvPolynomial.homogeneousSubmodule_eq_finsupp_supported, MvPolynomial.single_eq_monomial, Set.range_comp, X_pow_eq_monomial, comp_def, homogeneousSubmodule_eq_finsupp_supported, range_comp, range_single_one, single_eq_monomial, supported_eq_span_single
-/
lemma homogeneousSubmodule_one_eq_span_X :
    MvPolynomial.homogeneousSubmodule σ R 1 = .span R (.range X) := by
  simp [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported,
    AddMonoidAlgebra.supported_eq_span_single, MvPolynomial.single_eq_monomial,
    ← Finsupp.range_single_one, ← Set.range_comp, Function.comp_def, ← X_pow_eq_monomial]

section

/--
theorem `isHomogeneous_monomial` / 定理 `isHomogeneous_monomial`

English:
theorem isHomogeneous_monomial
  given: {d : σ ->₀ Nat} (r : R) {n : Nat} (hn : d.degree = n)
  proof: by
  rw [degree_eq_weight_one] at hn
  exact isWeightedHomogeneous_monomial 1 d r hn

中文:
定理 isHomogeneous_monomial
  条件: {d : σ ->₀ 自然数} (r : R) {n : 自然数} (hn : d.degree = n)
  证明: by
  rw [degree_eq_weight_one] at hn
  exact isWeightedHomogeneous_monomial 1 d r hn

Depends on / 依赖: degree_eq_weight_one, isWeightedHomogeneous_monomial
-/
theorem isHomogeneous_monomial {d : σ ->₀ Nat} (r : R) {n : Nat} (hn : d.degree = n) :
    IsHomogeneous (monomial d r) n := by
  rw [degree_eq_weight_one] at hn
  exact isWeightedHomogeneous_monomial 1 d r hn

variable (σ)

/--
theorem `totalDegree_eq_zero_iff` / 定理 `totalDegree_eq_zero_iff`

English:
theorem totalDegree_eq_zero_iff
  given: (p : MvPolynomial σ R)
  proof: by
  rw [← weightedTotalDegree_one]; rw [weightedTotalDegree_eq_zero_iff _ p]
  exact nonTorsionWeight_of (Function.const σ one_ne_zero)

中文:
定理 totalDegree_eq_zero_iff
  条件: (p : 多元多项式 σ R)
  证明: by
  rw [← weightedTotalDegree_one]; rw [weightedTotalDegree_eq_zero_iff _ p]
  exact nonTorsionWeight_of (Function.const σ one_ne_zero)

Depends on / 依赖: Function, Function.const, nonTorsionWeight_of, one_ne_zero, weightedTotalDegree_eq_zero_iff, weightedTotalDegree_one
-/
theorem totalDegree_eq_zero_iff (p : MvPolynomial σ R) :
    p.totalDegree = 0 ↔ forall (m : σ ->₀ Nat) (_ : m in p.support) (x : σ), m x = 0 := by
  rw [← weightedTotalDegree_one]; rw [weightedTotalDegree_eq_zero_iff _ p]
  exact nonTorsionWeight_of (Function.const σ one_ne_zero)

/--
theorem `totalDegree_zero_iff_isHomogeneous` / 定理 `totalDegree_zero_iff_isHomogeneous`

English:
theorem totalDegree_zero_iff_isHomogeneous
  given: {p : MvPolynomial σ R}
  proof: by
  rw [← weightedTotalDegree_one]; rw [← isWeightedHomogeneous_zero_iff_weightedTotalDegree_eq_zero]; rw [IsHomogeneous]

alias ⟨isHomogeneous_of_totalDegree_zero, _⟩ := totalDegree_zero_iff_isHomogeneous

@[simp]

中文:
定理 totalDegree_zero_iff_isHomogeneous
  条件: {p : 多元多项式 σ R}
  证明: by
  rw [← weightedTotalDegree_one]; rw [← isWeightedHomogeneous_zero_iff_weightedTotalDegree_eq_zero]; rw [IsHomogeneous]

alias ⟨isHomogeneous_of_totalDegree_zero, _⟩ := totalDegree_zero_iff_isHomogeneous

@[simp]

Depends on / 依赖: IsHomogeneous, isWeightedHomogeneous_zero_iff_weightedTotalDegree_eq_zero, weightedTotalDegree_one
-/
theorem totalDegree_zero_iff_isHomogeneous {p : MvPolynomial σ R} :
    p.totalDegree = 0 ↔ IsHomogeneous p 0 := by
  rw [← weightedTotalDegree_one]; rw [← isWeightedHomogeneous_zero_iff_weightedTotalDegree_eq_zero]; rw [IsHomogeneous]

alias ⟨isHomogeneous_of_totalDegree_zero, _⟩ := totalDegree_zero_iff_isHomogeneous

@[simp]
/--
lemma `homogeneousSubmodule_zero` / 引理 `homogeneousSubmodule_zero`

English:
lemma homogeneousSubmodule_zero
  proof: by
  ext
  rw [MvPolynomial.mem_homogeneousSubmodule]; rw [← MvPolynomial.totalDegree_zero_iff_isHomogeneous]; rw [Submodule.mem_one]; rw [MvPolynomial.algebraMap_eq]; rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C]
  grind [coeff_zero_C]

中文:
引理 homogeneousSubmodule_zero
  证明: by
  ext
  rw [MvPolynomial.mem_homogeneousSubmodule]; rw [← MvPolynomial.totalDegree_zero_iff_isHomogeneous]; rw [Submodule.mem_one]; rw [MvPolynomial.algebraMap_eq]; rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C]
  grind [coeff_zero_C]

Depends on / 依赖: MvPolynomial, MvPolynomial.algebraMap_eq, MvPolynomial.mem_homogeneousSubmodule, MvPolynomial.totalDegree_eq_zero_iff_eq_C, MvPolynomial.totalDegree_zero_iff_isHomogeneous, Submodule, Submodule.mem_one, algebraMap_eq, coeff_zero_C, mem_homogeneousSubmodule, mem_one, totalDegree_eq_zero_iff_eq_C, totalDegree_zero_iff_isHomogeneous
-/
lemma homogeneousSubmodule_zero :
    MvPolynomial.homogeneousSubmodule σ R 0 = 1 := by
  ext
  rw [MvPolynomial.mem_homogeneousSubmodule]; rw [← MvPolynomial.totalDegree_zero_iff_isHomogeneous]; rw [Submodule.mem_one]; rw [MvPolynomial.algebraMap_eq]; rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C]
  grind [coeff_zero_C]

/--
theorem `isHomogeneous_C` / 定理 `isHomogeneous_C`

English:
theorem isHomogeneous_C
  given: (r : R)
  statement: IsHomogeneous (C r : MvPolynomial σ R) 0
  proof: by
  apply isHomogeneous_monomial
  simp only [degree_apply, Finsupp.support_zero, zero_apply, Finset.sum_const_zero]

中文:
定理 isHomogeneous_C
  条件: (r : R)
  结论: IsHomogeneous (C r : 多元多项式 σ R) 0
  证明: by
  apply isHomogeneous_monomial
  simp only [degree_apply, Finsupp.support_zero, zero_apply, Finset.sum_const_zero]

Depends on / 依赖: Finset, Finset.sum_const_zero, Finsupp, Finsupp.support_zero, degree_apply, isHomogeneous_monomial, sum_const_zero, support_zero, zero_apply
-/
theorem isHomogeneous_C (r : R) : IsHomogeneous (C r : MvPolynomial σ R) 0 := by
  apply isHomogeneous_monomial
  simp only [degree_apply, Finsupp.support_zero, zero_apply, Finset.sum_const_zero]

variable (R)

/--
theorem `isHomogeneous_zero` / 定理 `isHomogeneous_zero`

English:
theorem isHomogeneous_zero
  given: (n : Nat)
  statement: IsHomogeneous (0 : MvPolynomial σ R) n
  proof: (homogeneousSubmodule σ R n).zero_mem

中文:
定理 isHomogeneous_zero
  条件: (n : 自然数)
  结论: IsHomogeneous (0 : 多元多项式 σ R) n
  证明: (homogeneousSubmodule σ R n).zero_mem

Depends on / 依赖: homogeneousSubmodule, zero_mem
-/
theorem isHomogeneous_zero (n : Nat) : IsHomogeneous (0 : MvPolynomial σ R) n :=
  (homogeneousSubmodule σ R n).zero_mem

/--
theorem `isHomogeneous_one` / 定理 `isHomogeneous_one`

English:
theorem isHomogeneous_one
  statement: IsHomogeneous (1 : MvPolynomial σ R) 0
  proof: isHomogeneous_C _ _

中文:
定理 isHomogeneous_one
  结论: IsHomogeneous (1 : 多元多项式 σ R) 0
  证明: isHomogeneous_C _ _

Depends on / 依赖: isHomogeneous_C
-/
theorem isHomogeneous_one : IsHomogeneous (1 : MvPolynomial σ R) 0 :=
  isHomogeneous_C _ _

/--
lemma `isHomogeneous_of_isEmpty` / 引理 `isHomogeneous_of_isEmpty`

English:
lemma isHomogeneous_of_isEmpty
  given: [IsEmpty σ] (f : MvPolynomial σ R)
  statement: f.IsHomogeneous 0
  proof: by
  rw [eq_C_of_isEmpty f]
  exact isHomogeneous_C _ _

中文:
引理 isHomogeneous_of_isEmpty
  条件: [是空 σ] (f : 多元多项式 σ R)
  结论: f.IsHomogeneous 0
  证明: by
  rw [eq_C_of_isEmpty f]
  exact isHomogeneous_C _ _

Depends on / 依赖: eq_C_of_isEmpty, isHomogeneous_C
-/
lemma isHomogeneous_of_isEmpty [IsEmpty σ] (f : MvPolynomial σ R) : f.IsHomogeneous 0 := by
  rw [eq_C_of_isEmpty f]
  exact isHomogeneous_C _ _

variable {σ}

/--
theorem `isHomogeneous_X` / 定理 `isHomogeneous_X`

English:
theorem isHomogeneous_X
  given: (i : σ)
  statement: IsHomogeneous (X i : MvPolynomial σ R) 1
  proof: by
  apply isHomogeneous_monomial
  simp only [degree_apply, Finsupp.support_single _ one_ne_zero, Finset.sum_singleton,
    single_eq_same]

中文:
定理 isHomogeneous_X
  条件: (i : σ)
  结论: IsHomogeneous (X i : 多元多项式 σ R) 1
  证明: by
  apply isHomogeneous_monomial
  simp only [degree_apply, Finsupp.support_single _ one_ne_zero, Finset.sum_singleton,
    single_eq_same]

Depends on / 依赖: Finset, Finset.sum_singleton, Finsupp, Finsupp.support_single, degree_apply, isHomogeneous_monomial, one_ne_zero, single_eq_same, sum_singleton, support_single
-/
theorem isHomogeneous_X (i : σ) : IsHomogeneous (X i : MvPolynomial σ R) 1 := by
  apply isHomogeneous_monomial
  simp only [degree_apply, Finsupp.support_single _ one_ne_zero, Finset.sum_singleton,
    single_eq_same]

variable {R} in
/--
lemma `monomial_mem_homogeneousSubmodule_pow_degree` / 引理 `monomial_mem_homogeneousSubmodule_pow_degree`

English:
lemma monomial_mem_homogeneousSubmodule_pow_degree
  proof: by
  induction s using Finsupp.induction with
  | zero => simp
  | single_add a b f _ _ h =>
    rw [map_add]; rw [Finsupp.degree_single]; rw [monomial_single_add]; rw [pow_add]
    exact Submodule.mul_mem_mul (Submodule.pow_mem_pow _ (isHomogeneous_X R a) _) h

@[simp]

中文:
引理 monomial_mem_homogeneousSubmodule_pow_degree
  证明: by
  induction s using Finsupp.induction with
  | zero => simp
  | single_add a b f _ _ h =>
    rw [map_add]; rw [Finsupp.degree_single]; rw [monomial_single_add]; rw [pow_add]
    exact Submodule.mul_mem_mul (Submodule.pow_mem_pow _ (isHomogeneous_X R a) _) h

@[simp]

Depends on / 依赖: Finsupp, Finsupp.degree_single, Finsupp.induction, Submodule, Submodule.mul_mem_mul, Submodule.pow_mem_pow, degree_single, isHomogeneous_X, map_add, monomial_single_add, mul_mem_mul, pow_add, pow_mem_pow, single_add
-/
lemma monomial_mem_homogeneousSubmodule_pow_degree
    (r : R) (s : σ ->₀ Nat) :
    monomial s r in (homogeneousSubmodule σ R 1) ^ s.degree := by
  induction s using Finsupp.induction with
  | zero => simp
  | single_add a b f _ _ h =>
    rw [map_add]; rw [Finsupp.degree_single]; rw [monomial_single_add]; rw [pow_add]
    exact Submodule.mul_mem_mul (Submodule.pow_mem_pow _ (isHomogeneous_X R a) _) h

@[simp]
/--
lemma `homogeneousSubmodule_one_pow` / 引理 `homogeneousSubmodule_one_pow`

English:
lemma homogeneousSubmodule_one_pow
  given: (n : Nat)
  proof: by
  refine le_antisymm ?_ fun x hx => ?_
  · induction n with
    | zero => simp [homogeneousSubmodule_zero]
    | succ n ih =>
      grw [pow_add, pow_one, ih]
      apply homogeneousSubmodule_mul
  · simp only [mem_homogeneousSubmodule] at hx
    induction hx using IsWeightedHomogeneous.induction

中文:
引理 homogeneousSubmodule_one_pow
  条件: (n : 自然数)
  证明: by
  refine le_antisymm ?_ fun x hx => ?_
  · induction n with
    | zero => simp [homogeneousSubmodule_zero]
    | succ n ih =>
      grw [pow_add, pow_one, ih]
      apply homogeneousSubmodule_mul
  · simp only [mem_homogeneousSubmodule] at hx
    induction hx using IsWeightedHomogeneous.induction

Depends on / 依赖: Finsupp, Finsupp.degree_eq_weight_one, IsWeightedHomogeneous, IsWeightedHomogeneous.induction_on, Pi.one_def, Submodule, Submodule.add_mem, add_mem, convert, degree_eq_weight_one, homogeneousSubmodule_mul, homogeneousSubmodule_zero, induction_on, le_antisymm, mem_homogeneousSubmodule, monomial, monomial_mem_homogeneousSubmodule_pow_degree, one_def, pow_add, pow_one
-/
lemma homogeneousSubmodule_one_pow (n : Nat) :
    (homogeneousSubmodule σ R 1) ^ n = homogeneousSubmodule σ R n := by
  refine le_antisymm ?_ fun x hx => ?_
  · induction n with
    | zero => simp [homogeneousSubmodule_zero]
    | succ n ih =>
      grw [pow_add, pow_one, ih]
      apply homogeneousSubmodule_mul
  · simp only [mem_homogeneousSubmodule] at hx
    induction hx using IsWeightedHomogeneous.induction_on with
    | zero => simp
    | add p q _ _ hp hq => exact Submodule.add_mem _ hp hq
    | monomial d r hr =>
      convert! monomial_mem_homogeneousSubmodule_pow_degree _ _
      rw [Finsupp.degree_eq_weight_one]; rw [← Pi.one_def]; rw [← hr]

end

namespace IsHomogeneous

variable [CommSemiring S] {φ ψ : MvPolynomial σ R} {m n : Nat}

/--
theorem `coeff_eq_zero` / 定理 `coeff_eq_zero`

English:
theorem coeff_eq_zero
  given: (hφ : IsHomogeneous φ n) {d : σ ->₀ Nat} (hd : d.degree != n)
  proof: by
  rw [degree_eq_weight_one] at hd
  exact IsWeightedHomogeneous.coeff_eq_zero hφ d hd

中文:
定理 coeff_eq_zero
  条件: (hφ : IsHomogeneous φ n) {d : σ ->₀ 自然数} (hd : d.degree != n)
  证明: by
  rw [degree_eq_weight_one] at hd
  exact IsWeightedHomogeneous.coeff_eq_zero hφ d hd

Depends on / 依赖: IsWeightedHomogeneous, IsWeightedHomogeneous.coeff_eq_zero, coeff_eq_zero, degree_eq_weight_one
-/
theorem coeff_eq_zero (hφ : IsHomogeneous φ n) {d : σ ->₀ Nat} (hd : d.degree != n) :
    coeff d φ = 0 := by
  rw [degree_eq_weight_one] at hd
  exact IsWeightedHomogeneous.coeff_eq_zero hφ d hd

/--
theorem `inj_right` / 定理 `inj_right`

English:
theorem inj_right
  given: (hm : IsHomogeneous φ m) (hn : IsHomogeneous φ n) (hφ : φ != 0)
  statement: m = n
  proof: by
  obtain ⟨d, hd⟩ : exists d, coeff d φ != 0 := exists_coeff_ne_zero hφ
  rw [← hm hd]; rw [← hn hd]

中文:
定理 inj_right
  条件: (hm : IsHomogeneous φ m) (hn : IsHomogeneous φ n) (hφ : φ != 0)
  结论: m = n
  证明: by
  obtain ⟨d, hd⟩ : exists d, coeff d φ != 0 := exists_coeff_ne_zero hφ
  rw [← hm hd]; rw [← hn hd]

Depends on / 依赖: exists_coeff_ne_zero
-/
theorem inj_right (hm : IsHomogeneous φ m) (hn : IsHomogeneous φ n) (hφ : φ != 0) : m = n := by
  obtain ⟨d, hd⟩ : exists d, coeff d φ != 0 := exists_coeff_ne_zero hφ
  rw [← hm hd]; rw [← hn hd]

/--
theorem `add` / 定理 `add`

English:
theorem add
  given: (hφ : IsHomogeneous φ n) (hψ : IsHomogeneous ψ n)
  statement: IsHomogeneous (φ + ψ) n
  proof: (homogeneousSubmodule σ R n).add_mem hφ hψ

中文:
定理 add
  条件: (hφ : IsHomogeneous φ n) (hψ : IsHomogeneous ψ n)
  结论: IsHomogeneous (φ + ψ) n
  证明: (homogeneousSubmodule σ R n).add_mem hφ hψ

Depends on / 依赖: add_mem, homogeneousSubmodule
-/
theorem add (hφ : IsHomogeneous φ n) (hψ : IsHomogeneous ψ n) : IsHomogeneous (φ + ψ) n :=
  (homogeneousSubmodule σ R n).add_mem hφ hψ

/--
theorem `sum` / 定理 `sum`

English:
theorem sum
  statement: {ι : Type*} (s : Finset ι) (φ : ι -> MvPolynomial σ R) (n : Nat)
  proof: (homogeneousSubmodule σ R n).sum_mem h

中文:
定理 求和
  结论: {ι : 类型} (s : 有限集 ι) (φ : ι -> 多元多项式 σ R) (n : 自然数)
  证明: (homogeneousSubmodule σ R n).sum_mem h

Depends on / 依赖: homogeneousSubmodule, sum_mem
-/
theorem sum {ι : Type*} (s : Finset ι) (φ : ι -> MvPolynomial σ R) (n : Nat)
    (h : forall i in s, IsHomogeneous (φ i) n) : IsHomogeneous (∑ i in s, φ i) n :=
  (homogeneousSubmodule σ R n).sum_mem h

set_option backward.isDefEq.respectTransparency false in
/--
theorem `mul` / 定理 `mul`

English:
theorem mul
  given: (hφ : IsHomogeneous φ m) (hψ : IsHomogeneous ψ n)
  statement: IsHomogeneous (φ * ψ) (m + n)
  proof: homogeneousSubmodule_mul m n Submodule.mul_mem_mul hφ hψ

中文:
定理 mul
  条件: (hφ : IsHomogeneous φ m) (hψ : IsHomogeneous ψ n)
  结论: IsHomogeneous (φ * ψ) (m + n)
  证明: homogeneousSubmodule_mul m n Submodule.mul_mem_mul hφ hψ

Depends on / 依赖: Submodule, Submodule.mul_mem_mul, homogeneousSubmodule_mul, mul_mem_mul
-/
theorem mul (hφ : IsHomogeneous φ m) (hψ : IsHomogeneous ψ n) : IsHomogeneous (φ * ψ) (m + n) :=
homogeneousSubmodule_mul m n Submodule.mul_mem_mul hφ hψ

/--
theorem `prod` / 定理 `prod`

English:
theorem prod
  statement: {ι : Type*} (s : Finset ι) (φ : ι -> MvPolynomial σ R) (n : ι -> Nat)
  proof: by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro
    simp only [isHomogeneous_one, Finset.sum_empty, Finset.prod_empty]
  · intro i s his IH h
    simp only [his, Finset.prod_insert, Finset.sum_insert, not_false_iff]
    apply (h i (by grind)).mul (IH _)
    grind

中文:
定理 乘积
  结论: {ι : 类型} (s : 有限集 ι) (φ : ι -> 多元多项式 σ R) (n : ι -> 自然数)
  证明: by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro
    simp only [isHomogeneous_one, Finset.sum_empty, Finset.prod_empty]
  · intro i s his IH h
    simp only [his, Finset.prod_insert, Finset.sum_insert, not_false_iff]
    apply (h i (by grind)).mul (IH _)
    grind

Depends on / 依赖: Finset, Finset.induction_on, Finset.prod_empty, Finset.prod_insert, Finset.sum_empty, Finset.sum_insert, classical, induction_on, isHomogeneous_one, not_false_iff, prod_empty, prod_insert, revert, sum_empty, sum_insert
-/
theorem prod {ι : Type*} (s : Finset ι) (φ : ι -> MvPolynomial σ R) (n : ι -> Nat)
    (h : forall i in s, IsHomogeneous (φ i) (n i)) : IsHomogeneous (∏ i in s, φ i) (∑ i in s, n i) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro
    simp only [isHomogeneous_one, Finset.sum_empty, Finset.prod_empty]
  · intro i s his IH h
    simp only [his, Finset.prod_insert, Finset.sum_insert, not_false_iff]
    apply (h i (by grind)).mul (IH _)
    grind

/--
lemma `C_mul` / 引理 `C_mul`

English:
lemma C_mul
  given: (hφ : φ.IsHomogeneous m) (r : R)
  proof: by
  simpa only [zero_add] using (isHomogeneous_C _ _).mul hφ

中文:
引理 C_mul
  条件: (hφ : φ.IsHomogeneous m) (r : R)
  证明: by
  simpa only [zero_add] using (isHomogeneous_C _ _).mul hφ

Depends on / 依赖: isHomogeneous_C, zero_add
-/
lemma C_mul (hφ : φ.IsHomogeneous m) (r : R) :
    (C r * φ).IsHomogeneous m := by
  simpa only [zero_add] using (isHomogeneous_C _ _).mul hφ

/--
lemma `_root_.MvPolynomial.isHomogeneous_C_mul_X` / 引理 `_root_.MvPolynomial.isHomogeneous_C_mul_X`

English:
lemma _root_.MvPolynomial.isHomogeneous_C_mul_X
  given: (r : R) (i : σ)
  proof: (isHomogeneous_X _ _).C_mul _

中文:
引理 _root_.多元多项式.isHomogeneous_C_mul_X
  条件: (r : R) (i : σ)
  证明: (isHomogeneous_X _ _).C_mul _

Depends on / 依赖: C_mul, isHomogeneous_X
-/
lemma _root_.MvPolynomial.isHomogeneous_C_mul_X (r : R) (i : σ) :
    (C r * X i).IsHomogeneous 1 :=
  (isHomogeneous_X _ _).C_mul _

/--
lemma `pow` / 引理 `pow`

English:
lemma pow
  given: (hφ : φ.IsHomogeneous m) (n : Nat)
  statement: (φ ^ n).IsHomogeneous (m * n)
  proof: by
  rw [show φ ^ n = ∏ _i in Finset.range n]; rw [φ by simp]
  rw [show m * n = ∑ _i in Finset.range n]; rw [m by simp [mul_comm]]
  apply IsHomogeneous.prod _ _ _ (fun _ _ => hφ)

中文:
引理 pow
  条件: (hφ : φ.IsHomogeneous m) (n : 自然数)
  结论: (φ ^ n).IsHomogeneous (m * n)
  证明: by
  rw [show φ ^ n = ∏ _i in Finset.range n]; rw [φ by simp]
  rw [show m * n = ∑ _i in Finset.range n]; rw [m by simp [mul_comm]]
  apply IsHomogeneous.prod _ _ _ (fun _ _ => hφ)

Depends on / 依赖: Finset, Finset.range, IsHomogeneous, IsHomogeneous.prod, mul_comm
-/
lemma pow (hφ : φ.IsHomogeneous m) (n : Nat) : (φ ^ n).IsHomogeneous (m * n) := by
  rw [show φ ^ n = ∏ _i in Finset.range n]; rw [φ by simp]
  rw [show m * n = ∑ _i in Finset.range n]; rw [m by simp [mul_comm]]
  apply IsHomogeneous.prod _ _ _ (fun _ _ => hφ)

/--
lemma `_root_.MvPolynomial.isHomogeneous_X_pow` / 引理 `_root_.MvPolynomial.isHomogeneous_X_pow`

English:
lemma _root_.MvPolynomial.isHomogeneous_X_pow
  given: (i : σ) (n : Nat)
  proof: by
  simpa only [one_mul] using (isHomogeneous_X _ _).pow n

中文:
引理 _root_.多元多项式.isHomogeneous_X_pow
  条件: (i : σ) (n : 自然数)
  证明: by
  simpa only [one_mul] using (isHomogeneous_X _ _).pow n

Depends on / 依赖: IsHomogeneous, isHomogeneous_X, one_mul
-/
lemma _root_.MvPolynomial.isHomogeneous_X_pow (i : σ) (n : Nat) :
    (X (R := R) i ^ n).IsHomogeneous n := by
  simpa only [one_mul] using (isHomogeneous_X _ _).pow n

/--
lemma `_root_.MvPolynomial.isHomogeneous_C_mul_X_pow` / 引理 `_root_.MvPolynomial.isHomogeneous_C_mul_X_pow`

English:
lemma _root_.MvPolynomial.isHomogeneous_C_mul_X_pow
  given: (r : R) (i : σ) (n : Nat)
  proof: (isHomogeneous_X_pow _ _).C_mul _

中文:
引理 _root_.多元多项式.isHomogeneous_C_mul_X_pow
  条件: (r : R) (i : σ) (n : 自然数)
  证明: (isHomogeneous_X_pow _ _).C_mul _

Depends on / 依赖: C_mul, isHomogeneous_X_pow
-/
lemma _root_.MvPolynomial.isHomogeneous_C_mul_X_pow (r : R) (i : σ) (n : Nat) :
    (C r * X i ^ n).IsHomogeneous n :=
  (isHomogeneous_X_pow _ _).C_mul _

/--
lemma `eval₂` / 引理 `eval₂`

English:
lemma eval₂
  statement: (hφ : φ.IsHomogeneous m) (f : R ->+* MvPolynomial τ S) (g : σ -> MvPolynomial τ S)
  proof: by
  apply IsHomogeneous.sum
  intro i hi
  rw [← zero_add (n * m)]
  apply IsHomogeneous.mul (hf _) _
  convert! IsHomogeneous.prod _ _ (fun k => n * i k) _
  · rw [Finsupp.mem_support_iff] at hi
    rw [← Finset.mul_sum]; rw [← hφ hi]; rw [weight_apply]
    simp_rw [smul_eq_mul, Finsupp.sum, Pi.on

中文:
引理 eval₂
  结论: (hφ : φ.IsHomogeneous m) (f : R ->+* 多元多项式 τ S) (g : σ -> 多元多项式 τ S)
  证明: by
  apply IsHomogeneous.sum
  intro i hi
  rw [← zero_add (n * m)]
  apply IsHomogeneous.mul (hf _) _
  convert! IsHomogeneous.prod _ _ (fun k => n * i k) _
  · rw [Finsupp.mem_support_iff] at hi
    rw [← Finset.mul_sum]; rw [← hφ hi]; rw [weight_apply]
    simp_rw [smul_eq_mul, Finsupp.sum, Pi.on

Depends on / 依赖: Finset, Finset.mul_sum, Finsupp, Finsupp.mem_support_iff, Finsupp.sum, IsHomogeneous, IsHomogeneous.mul, IsHomogeneous.prod, IsHomogeneous.sum, Pi.one_apply, convert, mem_support_iff, mul_one, mul_sum, one_apply, simp_rw, smul_eq_mul, weight_apply, zero_add
-/
lemma eval₂ (hφ : φ.IsHomogeneous m) (f : R ->+* MvPolynomial τ S) (g : σ -> MvPolynomial τ S)
    (hf : forall r, (f r).IsHomogeneous 0) (hg : forall i, (g i).IsHomogeneous n) :
    (eval₂ f g φ).IsHomogeneous (n * m) := by
  apply IsHomogeneous.sum
  intro i hi
  rw [← zero_add (n * m)]
  apply IsHomogeneous.mul (hf _) _
  convert! IsHomogeneous.prod _ _ (fun k => n * i k) _
  · rw [Finsupp.mem_support_iff] at hi
    rw [← Finset.mul_sum]; rw [← hφ hi]; rw [weight_apply]
    simp_rw [smul_eq_mul, Finsupp.sum, Pi.one_apply, mul_one]
  · rintro k -
    apply (hg k).pow

/--
lemma `map` / 引理 `map`

English:
lemma map
  given: (hφ : φ.IsHomogeneous n) (f : R ->+* S)
  statement: (map f φ).IsHomogeneous n
  proof: by
  rw [map_eq_eval₂Hom_C_comp]
  simpa [one_mul] using hφ.eval₂ _ _ (fun r => isHomogeneous_C _ (f r)) (isHomogeneous_X _)

中文:
引理 map
  条件: (hφ : φ.IsHomogeneous n) (f : R ->+* S)
  结论: (map f φ).IsHomogeneous n
  证明: by
  rw [map_eq_eval₂Hom_C_comp]
  simpa [one_mul] using hφ.eval₂ _ _ (fun r => isHomogeneous_C _ (f r)) (isHomogeneous_X _)
-/
protected lemma map (hφ : φ.IsHomogeneous n) (f : R ->+* S) : (map f φ).IsHomogeneous n := by
  rw [map_eq_eval₂Hom_C_comp]
  simpa [one_mul] using hφ.eval₂ _ _ (fun r => isHomogeneous_C _ (f r)) (isHomogeneous_X _)

/--
lemma `of_map` / 引理 `of_map`

English:
lemma of_map
  statement: {f : R ->+* S} (hf : Function.Injective f)
  proof: fun u hu => h (coeff_map f φ u ▸ map_zero f ▸ hf.ne hu)

中文:
引理 of_map
  结论: {f : R ->+* S} (hf : 函数.单射 f)
  证明: fun u hu => h (coeff_map f φ u ▸ map_zero f ▸ hf.ne hu)

Depends on / 依赖: coeff_map, hf.ne, map_zero
-/
lemma of_map {f : R ->+* S} (hf : Function.Injective f)
    (h : (MvPolynomial.map f φ).IsHomogeneous n) : φ.IsHomogeneous n :=
  fun u hu => h (coeff_map f φ u ▸ map_zero f ▸ hf.ne hu)

/--
lemma `aeval` / 引理 `aeval`

English:
lemma aeval
  statement: [Algebra R S] (hφ : φ.IsHomogeneous m)
  proof: hφ.eval₂ _ _ (fun _ => isHomogeneous_C _ _) hg

中文:
引理 aeval
  结论: [代数 R S] (hφ : φ.IsHomogeneous m)
  证明: hφ.eval₂ _ _ (fun _ => isHomogeneous_C _ _) hg

Depends on / 依赖: isHomogeneous_C
-/
lemma aeval [Algebra R S] (hφ : φ.IsHomogeneous m)
    (g : σ -> MvPolynomial τ S) (hg : forall i, (g i).IsHomogeneous n) :
    (aeval g φ).IsHomogeneous (n * m) :=
  hφ.eval₂ _ _ (fun _ => isHomogeneous_C _ _) hg

section CommRing

-- In this section we shadow the semiring `R` with a ring `R`.
variable {R σ : Type*} [CommRing R] {φ ψ : MvPolynomial σ R} {n : Nat}

/--
theorem `neg` / 定理 `neg`

English:
theorem neg
  given: (hφ : IsHomogeneous φ n)
  statement: IsHomogeneous (-φ) n
  proof: (homogeneousSubmodule σ R n).neg_mem hφ

中文:
定理 neg
  条件: (hφ : IsHomogeneous φ n)
  结论: IsHomogeneous (-φ) n
  证明: (homogeneousSubmodule σ R n).neg_mem hφ

Depends on / 依赖: homogeneousSubmodule, neg_mem
-/
theorem neg (hφ : IsHomogeneous φ n) : IsHomogeneous (-φ) n :=
  (homogeneousSubmodule σ R n).neg_mem hφ

/--
theorem `sub` / 定理 `sub`

English:
theorem sub
  given: (hφ : IsHomogeneous φ n) (hψ : IsHomogeneous ψ n)
  statement: IsHomogeneous (φ - ψ) n
  proof: (homogeneousSubmodule σ R n).sub_mem hφ hψ

中文:
定理 sub
  条件: (hφ : IsHomogeneous φ n) (hψ : IsHomogeneous ψ n)
  结论: IsHomogeneous (φ - ψ) n
  证明: (homogeneousSubmodule σ R n).sub_mem hφ hψ

Depends on / 依赖: homogeneousSubmodule, sub_mem
-/
theorem sub (hφ : IsHomogeneous φ n) (hψ : IsHomogeneous ψ n) : IsHomogeneous (φ - ψ) n :=
  (homogeneousSubmodule σ R n).sub_mem hφ hψ

end CommRing

/--
lemma `totalDegree_le` / 引理 `totalDegree_le`

English:
lemma totalDegree_le
  given: (hφ : IsHomogeneous φ n)
  statement: φ.totalDegree <= n
  proof: by
  apply Finset.sup_le
  intro d hd
  rw [mem_support_iff] at hd
  simp_rw [Finsupp.sum, ← hφ hd, weight_apply, Pi.one_apply, smul_eq_mul, mul_one, Finsupp.sum,
    le_rfl]

中文:
引理 totalDegree_le
  条件: (hφ : IsHomogeneous φ n)
  结论: φ.totalDegree <= n
  证明: by
  apply Finset.sup_le
  intro d hd
  rw [mem_support_iff] at hd
  simp_rw [Finsupp.sum, ← hφ hd, weight_apply, Pi.one_apply, smul_eq_mul, mul_one, Finsupp.sum,
    le_rfl]

Depends on / 依赖: Finset, Finset.sup_le, Finsupp, Finsupp.sum, Pi.one_apply, le_rfl, mem_support_iff, mul_one, one_apply, simp_rw, smul_eq_mul, sup_le, weight_apply
-/
lemma totalDegree_le (hφ : IsHomogeneous φ n) : φ.totalDegree <= n := by
  apply Finset.sup_le
  intro d hd
  rw [mem_support_iff] at hd
  simp_rw [Finsupp.sum, ← hφ hd, weight_apply, Pi.one_apply, smul_eq_mul, mul_one, Finsupp.sum,
    le_rfl]

/--
theorem `totalDegree` / 定理 `totalDegree`

English:
theorem totalDegree
  given: (hφ : IsHomogeneous φ n) (h : φ != 0)
  statement: totalDegree φ = n
  proof: by
  apply le_antisymm hφ.totalDegree_le
  obtain ⟨d, hd⟩ : exists d, coeff d φ != 0 := exists_coeff_ne_zero h
  simp only [← hφ hd, MvPolynomial.totalDegree, Finsupp.sum]
  replace hd := Finsupp.mem_support_iff.mpr hd
  simp only [weight_apply, Pi.one_apply, smul_eq_mul, mul_one]
  -- Porting note:

中文:
定理 totalDegree
  条件: (hφ : IsHomogeneous φ n) (h : φ != 0)
  结论: totalDegree φ = n
  证明: by
  apply le_antisymm hφ.totalDegree_le
  obtain ⟨d, hd⟩ : exists d, coeff d φ != 0 := exists_coeff_ne_zero h
  simp only [← hφ hd, MvPolynomial.totalDegree, Finsupp.sum]
  replace hd := Finsupp.mem_support_iff.mpr hd
  simp only [weight_apply, Pi.one_apply, smul_eq_mul, mul_one]
  -- Porting note:

Depends on / 依赖: Finsupp, Finsupp.mem_support_iff.mpr, Finsupp.sum, MvPolynomial, MvPolynomial.totalDegree, Pi.one_apply, exists_coeff_ne_zero, le_antisymm, mem_support_iff, mul_one, one_apply, replace, smul_eq_mul, totalDegree, totalDegree_le, weight_apply
-/
theorem totalDegree (hφ : IsHomogeneous φ n) (h : φ != 0) : totalDegree φ = n := by
  apply le_antisymm hφ.totalDegree_le
  obtain ⟨d, hd⟩ : exists d, coeff d φ != 0 := exists_coeff_ne_zero h
  simp only [← hφ hd, MvPolynomial.totalDegree, Finsupp.sum]
  replace hd := Finsupp.mem_support_iff.mpr hd
  simp only [weight_apply, Pi.one_apply, smul_eq_mul, mul_one]
  -- Porting note: Original proof did not define `f`
  exact Finset.le_sup (f := fun s => ∑ x in s.support, s x) hd

/--
lemma `degree_eq_sum_deg_support` / 引理 `degree_eq_sum_deg_support`

English:
lemma degree_eq_sum_deg_support
  given: (hφ : φ.IsHomogeneous n) {s : σ ->₀ Nat} (hs : s in φ.support)
  proof: by
  simp [← hφ <| mem_support_iff.mp hs, ← degree_apply, degree_eq_weight_one, Pi.one_def]

中文:
引理 degree_eq_sum_deg_support
  条件: (hφ : φ.IsHomogeneous n) {s : σ ->₀ 自然数} (hs : s in φ.support)
  证明: by
  simp [← hφ <| mem_support_iff.mp hs, ← degree_apply, degree_eq_weight_one, Pi.one_def]

Depends on / 依赖: Pi.one_def, degree_apply, degree_eq_weight_one, mem_support_iff, mem_support_iff.mp, one_def
-/
lemma degree_eq_sum_deg_support (hφ : φ.IsHomogeneous n) {s : σ ->₀ Nat} (hs : s in φ.support) :
    n = ∑ i in s.support, s i := by
  simp [← hφ <| mem_support_iff.mp hs, ← degree_apply, degree_eq_weight_one, Pi.one_def]

/--
theorem `rename_isHomogeneous` / 定理 `rename_isHomogeneous`

English:
theorem rename_isHomogeneous
  given: {f : σ -> τ} (h : φ.IsHomogeneous n)
  proof: by
  rw [← φ.support_sum_monomial_coeff]; rw [map_sum]; simp_rw [rename_monomial]
  apply IsHomogeneous.sum _ _ _ fun d hd => isHomogeneous_monomial _ _
  intro d hd
  apply (Finsupp.sum_mapDomain_index_addMonoidHom fun _ => .id Nat).trans
  convert! h (mem_support_iff.mp hd)
  simp only [weight_app

中文:
定理 rename_isHomogeneous
  条件: {f : σ -> τ} (h : φ.IsHomogeneous n)
  证明: by
  rw [← φ.support_sum_monomial_coeff]; rw [map_sum]; simp_rw [rename_monomial]
  apply IsHomogeneous.sum _ _ _ fun d hd => isHomogeneous_monomial _ _
  intro d hd
  apply (Finsupp.sum_mapDomain_index_addMonoidHom fun _ => .id Nat).trans
  convert! h (mem_support_iff.mp hd)
  simp only [weight_app

Depends on / 依赖: AddMonoidHom, AddMonoidHom.id_apply, Finsupp, Finsupp.sum_mapDomain_index_addMonoidHom, IsHomogeneous, IsHomogeneous.sum, Pi.one_apply, convert, id_apply, isHomogeneous_monomial, map_sum, mem_support_iff, mem_support_iff.mp, mul_one, one_apply, rename_monomial, simp_rw, smul_eq_mul, sum_mapDomain_index_addMonoidHom, support_sum_monomial_coeff
-/
theorem rename_isHomogeneous {f : σ -> τ} (h : φ.IsHomogeneous n) :
    (rename f φ).IsHomogeneous n := by
  rw [← φ.support_sum_monomial_coeff]; rw [map_sum]; simp_rw [rename_monomial]
  apply IsHomogeneous.sum _ _ _ fun d hd => isHomogeneous_monomial _ _
  intro d hd
  apply (Finsupp.sum_mapDomain_index_addMonoidHom fun _ => .id Nat).trans
  convert! h (mem_support_iff.mp hd)
  simp only [weight_apply, AddMonoidHom.id_apply, Pi.one_apply, smul_eq_mul, mul_one]

/--
theorem `rename_isHomogeneous_iff` / 定理 `rename_isHomogeneous_iff`

English:
theorem rename_isHomogeneous_iff
  given: {f : σ -> τ} (hf : f.Injective)
  proof: by
  refine ⟨fun h d hd => ?_, rename_isHomogeneous⟩
  convert! ← @h (d.mapDomain f) _
  · simp only [weight_apply, Pi.one_apply, smul_eq_mul, mul_one]
    exact Finsupp.sum_mapDomain_index_inj (h := fun _ => id) hf
  · rwa [coeff_rename_mapDomain f hf]

中文:
定理 rename_isHomogeneous_iff
  条件: {f : σ -> τ} (hf : f.单射)
  证明: by
  refine ⟨fun h d hd => ?_, rename_isHomogeneous⟩
  convert! ← @h (d.mapDomain f) _
  · simp only [weight_apply, Pi.one_apply, smul_eq_mul, mul_one]
    exact Finsupp.sum_mapDomain_index_inj (h := fun _ => id) hf
  · rwa [coeff_rename_mapDomain f hf]

Depends on / 依赖: Finsupp, Finsupp.sum_mapDomain_index_inj, Pi.one_apply, coeff_rename_mapDomain, convert, d.mapDomain, mapDomain, mul_one, one_apply, rename_isHomogeneous, smul_eq_mul, sum_mapDomain_index_inj, weight_apply
-/
theorem rename_isHomogeneous_iff {f : σ -> τ} (hf : f.Injective) :
    (rename f φ).IsHomogeneous n ↔ φ.IsHomogeneous n := by
  refine ⟨fun h d hd => ?_, rename_isHomogeneous⟩
  convert! ← @h (d.mapDomain f) _
  · simp only [weight_apply, Pi.one_apply, smul_eq_mul, mul_one]
    exact Finsupp.sum_mapDomain_index_inj (h := fun _ => id) hf
  · rwa [coeff_rename_mapDomain f hf]

/--
lemma `finSuccEquiv_coeff_isHomogeneous` / 引理 `finSuccEquiv_coeff_isHomogeneous`

English:
lemma finSuccEquiv_coeff_isHomogeneous
  statement: {N : Nat} {φ : MvPolynomial (Fin (N + 1)) R} {n : Nat}
  proof: by
  intro d hd
  rw [finSuccEquiv_coeff_coeff] at hd
  have h' : (weight 1) (Finsupp.cons i d) = i + j := by
    simpa [Finset.sum_subset_zero_on_sdiff (g := d.cons i)
     (d.cons_support (y := i)) (by simp) (fun _ _ => rfl), ← h] using hφ hd
  simp only [weight_apply, Pi.one_apply, smul_eq_mul, m

中文:
引理 finSuccEquiv_coeff_isHomogeneous
  结论: {N : 自然数} {φ : 多元多项式 (有限集 (N + 1)) R} {n : 自然数}
  证明: by
  intro d hd
  rw [finSuccEquiv_coeff_coeff] at hd
  have h' : (weight 1) (Finsupp.cons i d) = i + j := by
    simpa [Finset.sum_subset_zero_on_sdiff (g := d.cons i)
     (d.cons_support (y := i)) (by simp) (fun _ _ => rfl), ← h] using hφ hd
  simp only [weight_apply, Pi.one_apply, smul_eq_mul, m

Depends on / 依赖: Finset, Finset.sum_subset_zero_on_sdiff, Finsupp, Finsupp.cons, Finsupp.sum_cons, Pi.one_apply, add_right_inj, cons_support, d.cons, d.cons_support, finSuccEquiv_coeff_coeff, mul_one, one_apply, smul_eq_mul, sum_cons, sum_subset_zero_on_sdiff, weight, weight_apply
-/
lemma finSuccEquiv_coeff_isHomogeneous {N : Nat} {φ : MvPolynomial (Fin (N + 1)) R} {n : Nat}
    (hφ : φ.IsHomogeneous n) (i j : Nat) (h : i + j = n) :
    ((finSuccEquiv _ _ φ).coeff i).IsHomogeneous j := by
  intro d hd
  rw [finSuccEquiv_coeff_coeff] at hd
  have h' : (weight 1) (Finsupp.cons i d) = i + j := by
    simpa [Finset.sum_subset_zero_on_sdiff (g := d.cons i)
     (d.cons_support (y := i)) (by simp) (fun _ _ => rfl), ← h] using hφ hd
  simp only [weight_apply, Pi.one_apply, smul_eq_mul, mul_one, Finsupp.sum_cons,
    add_right_inj] at h' ⊢
  exact h'

set_option backward.defeqAttrib.useBackward true in
-- TODO: develop API for `optionEquivLeft` and get rid of the `[Fintype σ]` assumption
/--
lemma `coeff_isHomogeneous_of_optionEquivLeft_symm` / 引理 `coeff_isHomogeneous_of_optionEquivLeft_symm`

English:
lemma coeff_isHomogeneous_of_optionEquivLeft_symm
  proof: by
  obtain ⟨k, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  let e' := e.optionCongr.trans (_root_.finSuccEquiv _).symm
  let F := renameEquiv R e
  let F' := renameEquiv R e'
  let φ := F' ((optionEquivLeft R σ).symm p)
  have hφ : φ.IsHomogeneous n := hp.rename_isHomogeneous
  suffices IsHomogeneous (F (p.

中文:
引理 coeff_isHomogeneous_of_optionEquivLeft_symm
  证明: by
  obtain ⟨k, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  let e' := e.optionCongr.trans (_root_.finSuccEquiv _).symm
  let F := renameEquiv R e
  let F' := renameEquiv R e'
  let φ := F' ((optionEquivLeft R σ).symm p)
  have hφ : φ.IsHomogeneous n := hp.rename_isHomogeneous
  suffices IsHomogeneous (F (p.

Depends on / 依赖: Finite, Finite.exists_equiv_fin, IsHomogeneous, IsHomogeneous.rename_isHomogeneous_iff, _root_, _root_.finSuccEquiv, convert, e.injective, e.optionCongr.trans, exists_equiv_fin, finSuccEquiv, finSuccEquiv_coeff_isHomogeneous, finSuccEquiv_rename_finSuccEquiv, hp.rename_isHomogeneous, injective, optionCongr, optionEquivLeft, p.coeff, renameEquiv, renameEquiv_apply
-/
lemma coeff_isHomogeneous_of_optionEquivLeft_symm
    [hσ : Finite σ] {p : Polynomial (MvPolynomial σ R)}
    (hp : ((optionEquivLeft R σ).symm p).IsHomogeneous n) (i j : Nat) (h : i + j = n) :
    (p.coeff i).IsHomogeneous j := by
  obtain ⟨k, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  let e' := e.optionCongr.trans (_root_.finSuccEquiv _).symm
  let F := renameEquiv R e
  let F' := renameEquiv R e'
  let φ := F' ((optionEquivLeft R σ).symm p)
  have hφ : φ.IsHomogeneous n := hp.rename_isHomogeneous
  suffices IsHomogeneous (F (p.coeff i)) j by
    rwa [← (IsHomogeneous.rename_isHomogeneous_iff e.injective)]
  convert! hφ.finSuccEquiv_coeff_isHomogeneous i j h using 1
  dsimp only [φ, F', F, renameEquiv_apply]
  rw [finSuccEquiv_rename_finSuccEquiv]; rw [AlgEquiv.apply_symm_apply]
  simp

open Polynomial in
private
/--
lemma `exists_eval_ne_zero_of_coeff_finSuccEquiv_ne_zero_aux` / 引理 `exists_eval_ne_zero_of_coeff_finSuccEquiv_ne_zero_aux`

English:
lemma exists_eval_ne_zero_of_coeff_finSuccEquiv_ne_zero_aux
  proof: by
  have hF₀ : F != 0 := by contrapose hFn; simp [hFn]
  have hdeg : natDegree (finSuccEquiv R N F) < n + 1 := by
    linarith [natDegree_finSuccEquiv F, degreeOf_le_totalDegree F 0, hF.totalDegree hF₀]
  use Fin.cons 1 0
  have aux : forall i in Finset.range n, constantCoeff ((finSuccEquiv R N F).

中文:
引理 存在_eval_ne_zero_of_coeff_finSuccEquiv_ne_zero_aux
  证明: by
  have hF₀ : F != 0 := by contrapose hFn; simp [hFn]
  have hdeg : natDegree (finSuccEquiv R N F) < n + 1 := by
    linarith [natDegree_finSuccEquiv F, degreeOf_le_totalDegree F 0, hF.totalDegree hF₀]
  use Fin.cons 1 0
  have aux : forall i in Finset.range n, constantCoeff ((finSuccEquiv R N F).

Depends on / 依赖: Fin.cons, Finset, Finset.mem_range, Finset.range, Nat.sub_ne_zero_iff_lt, coeff_eq_zero, constantCoeff, contrapose, degreeOf_le_totalDegree, finSuccEquiv, finSuccEquiv_coeff_isHomogeneous, hF.finSuccEquiv_coeff_isHomogeneous, hF.totalDegree, hi.symm, map_zero, mem_range, natDegree, natDegree_finSuccEquiv, simp_r, sub_ne_zero_iff_lt
-/
lemma exists_eval_ne_zero_of_coeff_finSuccEquiv_ne_zero_aux
    {N : Nat} {F : MvPolynomial (Fin (Nat.succ N)) R} {n : Nat} (hF : IsHomogeneous F n)
    (hFn : ((finSuccEquiv R N) F).coeff n != 0) :
    exists r, eval r F != 0 := by
  have hF₀ : F != 0 := by contrapose hFn; simp [hFn]
  have hdeg : natDegree (finSuccEquiv R N F) < n + 1 := by
    linarith [natDegree_finSuccEquiv F, degreeOf_le_totalDegree F 0, hF.totalDegree hF₀]
  use Fin.cons 1 0
  have aux : forall i in Finset.range n, constantCoeff ((finSuccEquiv R N F).coeff i) = 0 := by
    intro i hi
    rw [Finset.mem_range] at hi
    apply (hF.finSuccEquiv_coeff_isHomogeneous i (n - i) (by lia)).coeff_eq_zero
    simp only [map_zero]
    rw [← Nat.sub_ne_zero_iff_lt] at hi
    exact hi.symm
  simp_rw [eval_eq_eval_mv_eval', eval_one_map, Polynomial.eval_eq_sum_range' hdeg,
    eval_zero, one_pow, mul_one, map_sum, Finset.sum_range_succ, Finset.sum_eq_zero aux, zero_add]
  contrapose hFn
  ext d
  rw [coeff_zero]
  obtain rfl | hd := eq_or_ne d 0
  · apply hFn
  · contrapose! hd
    ext i
    rw [Finsupp.coe_zero]; rw [Pi.zero_apply]
    by_cases hi : i in d.support
    · have := hF.finSuccEquiv_coeff_isHomogeneous n 0 (add_zero _) hd
      simp only [weight_apply, Pi.one_apply, smul_eq_mul, mul_one, Finsupp.sum] at this
      rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => zero_le)] at this
      exact this i hi
    · simpa using hi

section IsDomain

-- In this section we shadow the semiring `R` with a domain `R`.
variable {R σ : Type*} [CommRing R] [IsDomain R] {F G : MvPolynomial σ R} {n : Nat}

open Cardinal Polynomial

private
/--
lemma `exists_eval_ne_zero_of_totalDegree_le_card_aux` / 引理 `exists_eval_ne_zero_of_totalDegree_le_card_aux`

English:
lemma exists_eval_ne_zero_of_totalDegree_le_card_aux
  statement: {N : Nat} {F : MvPolynomial (Fin N) R} {n : Nat}
  proof: by
  induction N generalizing n with
  | zero =>
    use 0
    contrapose hF₀
    ext d
    simpa only [Subsingleton.elim d 0, eval_zero, coeff_zero] using! hF₀
  | succ N IH =>
    have hdeg : natDegree (finSuccEquiv R N F) < n + 1 := by
      linarith [natDegree_finSuccEquiv F, degreeOf_le_totalDe

中文:
引理 存在_eval_ne_zero_of_totalDegree_le_card_aux
  结论: {N : 自然数} {F : 多元多项式 (有限集 N) R} {n : 自然数}
  证明: by
  induction N generalizing n with
  | zero =>
    use 0
    contrapose hF₀
    ext d
    simpa only [Subsingleton.elim d 0, eval_zero, coeff_zero] using! hF₀
  | succ N IH =>
    have hdeg : natDegree (finSuccEquiv R N F) < n + 1 := by
      linarith [natDegree_finSuccEquiv F, degreeOf_le_totalDe

Depends on / 依赖: Polynomial, Polynomial.ext, Subsingleton, Subsingleton.elim, coeff_zero, contrapose, degreeOf_le_totalDegree, eval_zero, finSuccEquiv, generalizing, hF.totalDegree, injective, natDegree, natDegree_finSuccEquiv, totalDegree
-/
lemma exists_eval_ne_zero_of_totalDegree_le_card_aux {N : Nat} {F : MvPolynomial (Fin N) R} {n : Nat}
    (hF : F.IsHomogeneous n) (hF₀ : F != 0) (hnR : n <= #R) :
    exists r, eval r F != 0 := by
  induction N generalizing n with
  | zero =>
    use 0
    contrapose hF₀
    ext d
    simpa only [Subsingleton.elim d 0, eval_zero, coeff_zero] using! hF₀
  | succ N IH =>
    have hdeg : natDegree (finSuccEquiv R N F) < n + 1 := by
      linarith [natDegree_finSuccEquiv F, degreeOf_le_totalDegree F 0, hF.totalDegree hF₀]
    obtain ⟨i, hi⟩ : exists i : Nat, (finSuccEquiv R N F).coeff i != 0 := by
      contrapose! hF₀
exact (finSuccEquiv _ _).injective Polynomial.ext by simpa using! hF₀
    have hin : i <= n := by
      contrapose! hi
exact coeff_eq_zero_of_natDegree_lt (Nat.le_of_lt_succ hdeg).trans_lt hi
    obtain hFn | hFn := ne_or_eq ((finSuccEquiv R N F).coeff n) 0
    · exact hF.exists_eval_ne_zero_of_coeff_finSuccEquiv_ne_zero_aux hFn
have hin : i < n := hin.lt_or_eq.elim id by aesop
obtain ⟨j, hj⟩ : exists j, i + (j + 1) = n := (Nat.exists_eq_add_of_lt hin).imp by lia
    obtain ⟨r, hr⟩ : exists r, (eval r) (Polynomial.coeff ((finSuccEquiv R N) F) i) != 0 :=
      IH (hF.finSuccEquiv_coeff_isHomogeneous _ _ hj) hi (.trans (by norm_cast; lia) hnR)
    set φ : R[X] := Polynomial.map (eval r) (finSuccEquiv _ _ F) with hφ
have hφ₀ : φ != 0 := fun hφ₀ => hr by
      rw [← coeff_eval_eq_eval_coeff]; rw [← hφ]; rw [hφ₀]; rw [Polynomial.coeff_zero]
    have hφR : φ.natDegree < #R := by
      refine lt_of_lt_of_le ?_ hnR
      norm_cast
      refine lt_of_le_of_lt natDegree_map_le ?_
      suffices (finSuccEquiv _ _ F).natDegree != n by lia
      rintro rfl
      refine leadingCoeff_ne_zero.mpr ?_ hFn
      simpa using! (finSuccEquiv R N).injective.ne hF₀
    obtain ⟨r₀, hr₀⟩ : exists r₀, Polynomial.eval r₀ φ != 0 :=
      φ.exists_eval_ne_zero_of_natDegree_lt_card hφ₀ hφR
    use Fin.cons r₀ r
    rwa [eval_eq_eval_mv_eval']

/--
lemma `eq_zero_of_forall_eval_eq_zero_of_le_card` / 引理 `eq_zero_of_forall_eval_eq_zero_of_le_card`

English:
lemma eq_zero_of_forall_eval_eq_zero_of_le_card
  proof: by
  contrapose! h
  -- reduce to the case where σ is finite
  obtain ⟨k, f, hf, F, rfl⟩ := exists_fin_rename F
  have hF₀ : F != 0 := by rintro rfl; simp at h
  have hF : F.IsHomogeneous n := by rwa [rename_isHomogeneous_iff hf] at hF
  obtain ⟨r, hr⟩ := exists_eval_ne_zero_of_totalDegree_le_card_a

中文:
引理 eq_zero_of_对任意_eval_eq_zero_of_le_card
  证明: by
  contrapose! h
  -- reduce to the case where σ is finite
  obtain ⟨k, f, hf, F, rfl⟩ := exists_fin_rename F
  have hF₀ : F != 0 := by rintro rfl; simp at h
  have hF : F.IsHomogeneous n := by rwa [rename_isHomogeneous_iff hf] at hF
  obtain ⟨r, hr⟩ := exists_eval_ne_zero_of_totalDegree_le_card_a

Depends on / 依赖: contrapose
-/
lemma eq_zero_of_forall_eval_eq_zero_of_le_card
    (hF : F.IsHomogeneous n) (h : forall r : σ -> R, eval r F = 0) (hnR : n <= #R) :
    F = 0 := by
  contrapose! h
  -- reduce to the case where σ is finite
  obtain ⟨k, f, hf, F, rfl⟩ := exists_fin_rename F
  have hF₀ : F != 0 := by rintro rfl; simp at h
  have hF : F.IsHomogeneous n := by rwa [rename_isHomogeneous_iff hf] at hF
  obtain ⟨r, hr⟩ := exists_eval_ne_zero_of_totalDegree_le_card_aux hF hF₀ hnR
obtain ⟨r, rfl⟩ := (Function.factorsThrough_iff _).mp (hf.factorsThrough r)
  use r
  rwa [eval_rename]

/--
lemma `funext_of_le_card` / 引理 `funext_of_le_card`

English:
lemma funext_of_le_card
  statement: (hF : F.IsHomogeneous n) (hG : G.IsHomogeneous n)
  proof: by
  rw [← sub_eq_zero]
  apply eq_zero_of_forall_eval_eq_zero_of_le_card (hF.sub hG) _ hnR
  simpa [sub_eq_zero] using h

中文:
引理 funext_of_le_card
  结论: (hF : F.IsHomogeneous n) (hG : G.IsHomogeneous n)
  证明: by
  rw [← sub_eq_zero]
  apply eq_zero_of_forall_eval_eq_zero_of_le_card (hF.sub hG) _ hnR
  simpa [sub_eq_zero] using h

Depends on / 依赖: eq_zero_of_forall_eval_eq_zero_of_le_card, hF.sub, sub_eq_zero
-/
lemma funext_of_le_card (hF : F.IsHomogeneous n) (hG : G.IsHomogeneous n)
    (h : forall r : σ -> R, eval r F = eval r G) (hnR : n <= #R) :
    F = G := by
  rw [← sub_eq_zero]
  apply eq_zero_of_forall_eval_eq_zero_of_le_card (hF.sub hG) _ hnR
  simpa [sub_eq_zero] using h

/--
lemma `eq_zero_of_forall_eval_eq_zero` / 引理 `eq_zero_of_forall_eval_eq_zero`

English:
lemma eq_zero_of_forall_eval_eq_zero
  statement: [Infinite R] {F : MvPolynomial σ R} {n : Nat}
  proof: by
  apply eq_zero_of_forall_eval_eq_zero_of_le_card hF h
exact Cardinal.natCast_le_aleph0.trans Cardinal.infinite_iff.mp ‹Infinite R›

中文:
引理 eq_zero_of_对任意_eval_eq_zero
  结论: [无限 R] {F : 多元多项式 σ R} {n : 自然数}
  证明: by
  apply eq_zero_of_forall_eval_eq_zero_of_le_card hF h
exact Cardinal.natCast_le_aleph0.trans Cardinal.infinite_iff.mp ‹Infinite R›

Depends on / 依赖: Cardinal, Cardinal.infinite_iff.mp, Cardinal.natCast_le_aleph0.trans, Infinite, eq_zero_of_forall_eval_eq_zero_of_le_card, infinite_iff, natCast_le_aleph0
-/
lemma eq_zero_of_forall_eval_eq_zero [Infinite R] {F : MvPolynomial σ R} {n : Nat}
    (hF : F.IsHomogeneous n) (h : forall r : σ -> R, eval r F = 0) : F = 0 := by
  apply eq_zero_of_forall_eval_eq_zero_of_le_card hF h
exact Cardinal.natCast_le_aleph0.trans Cardinal.infinite_iff.mp ‹Infinite R›

/--
lemma `funext` / 引理 `funext`

English:
lemma funext
  statement: [Infinite R] {F G : MvPolynomial σ R} {n : Nat}
  proof: by
  apply funext_of_le_card hF hG h
exact Cardinal.natCast_le_aleph0.trans Cardinal.infinite_iff.mp ‹Infinite R›

中文:
引理 funext
  结论: [无限 R] {F G : 多元多项式 σ R} {n : 自然数}
  证明: by
  apply funext_of_le_card hF hG h
exact Cardinal.natCast_le_aleph0.trans Cardinal.infinite_iff.mp ‹Infinite R›

Depends on / 依赖: Cardinal, Cardinal.infinite_iff.mp, Cardinal.natCast_le_aleph0.trans, Infinite, funext_of_le_card, infinite_iff, natCast_le_aleph0
-/
lemma funext [Infinite R] {F G : MvPolynomial σ R} {n : Nat}
    (hF : F.IsHomogeneous n) (hG : G.IsHomogeneous n)
    (h : forall r : σ -> R, eval r F = eval r G) : F = G := by
  apply funext_of_le_card hF hG h
exact Cardinal.natCast_le_aleph0.trans Cardinal.infinite_iff.mp ‹Infinite R›

end IsDomain

/--
Instance `HomogeneousSubmodule.gcommSemiring` / 实例 `HomogeneousSubmodule.gcommSemiring`

English:
instance HomogeneousSubmodule.gcommSemiring
  signature: : SetLike.GradedMonoid (homogeneousSubmodule σ R) where
  body: isHomogeneous_one σ R
  mul_mem _ _ _ _ := IsHomogeneous.mul

中文:
实例 齐次子模.gcommSemiring
  签名: : 集合状.分次幺半群 (homogeneousSubmodule σ R) where
  定义体: isHomogeneous_one σ R
  mul_mem _ _ _ _ := IsHomogeneous.mul

Depends on / 依赖: isHomogeneous_one
-/
instance HomogeneousSubmodule.gcommSemiring : SetLike.GradedMonoid (homogeneousSubmodule σ R) where
  one_mem := isHomogeneous_one σ R
  mul_mem _ _ _ _ := IsHomogeneous.mul

end IsHomogeneous

noncomputable section

open Finset

/--
Definition of `homogeneousComponent` / `homogeneousComponent` 的定义

English:
definition homogeneousComponent
  signature: (n : Nat)
  body: weightedHomogeneousComponent 1 n

中文:
定义 homogeneousComponent
  签名: (n : 自然数)
  定义体: weightedHomogeneousComponent 1 n

Depends on / 依赖: weightedHomogeneousComponent
-/
def homogeneousComponent (n : Nat) : MvPolynomial σ R ->ₗ[R] MvPolynomial σ R :=
  weightedHomogeneousComponent 1 n

section HomogeneousComponent

open Finset Finsupp

variable (n : Nat) (φ ψ : MvPolynomial σ R)

/--
theorem `homogeneousComponent_mem` / 定理 `homogeneousComponent_mem`

English:
theorem homogeneousComponent_mem
  proof: weightedHomogeneousComponent_mem _ φ n

中文:
定理 homogeneousComponent_mem
  证明: weightedHomogeneousComponent_mem _ φ n

Depends on / 依赖: weightedHomogeneousComponent_mem
-/
theorem homogeneousComponent_mem :
    homogeneousComponent n φ in homogeneousSubmodule σ R n :=
  weightedHomogeneousComponent_mem _ φ n

/--
theorem `coeff_homogeneousComponent` / 定理 `coeff_homogeneousComponent`

English:
theorem coeff_homogeneousComponent
  given: (d : σ ->₀ Nat)
  proof: by
  rw [degree_eq_weight_one]
  convert! coeff_weightedHomogeneousComponent n φ d

中文:
定理 coeff_homogeneousComponent
  条件: (d : σ ->₀ 自然数)
  证明: by
  rw [degree_eq_weight_one]
  convert! coeff_weightedHomogeneousComponent n φ d

Depends on / 依赖: coeff_weightedHomogeneousComponent, convert, degree_eq_weight_one
-/
theorem coeff_homogeneousComponent (d : σ ->₀ Nat) :
    coeff d (homogeneousComponent n φ) = if d.degree = n then coeff d φ else 0 := by
  rw [degree_eq_weight_one]
  convert! coeff_weightedHomogeneousComponent n φ d

/--
theorem `homogeneousComponent_apply` / 定理 `homogeneousComponent_apply`

English:
theorem homogeneousComponent_apply
  proof: by
  simp_rw [degree_eq_weight_one]
  convert! weightedHomogeneousComponent_apply n φ

中文:
定理 homogeneousComponent_apply
  证明: by
  simp_rw [degree_eq_weight_one]
  convert! weightedHomogeneousComponent_apply n φ

Depends on / 依赖: convert, degree_eq_weight_one, simp_rw, weightedHomogeneousComponent_apply
-/
theorem homogeneousComponent_apply :
    homogeneousComponent n φ = ∑ d in φ.support with d.degree = n, monomial d (coeff d φ) := by
  simp_rw [degree_eq_weight_one]
  convert! weightedHomogeneousComponent_apply n φ

/--
theorem `homogeneousComponent_isHomogeneous` / 定理 `homogeneousComponent_isHomogeneous`

English:
theorem homogeneousComponent_isHomogeneous
  statement: (homogeneousComponent n φ).IsHomogeneous n
  proof: weightedHomogeneousComponent_isWeightedHomogeneous n φ

@[simp]

中文:
定理 homogeneousComponent_isHomogeneous
  结论: (homogeneousComponent n φ).IsHomogeneous n
  证明: weightedHomogeneousComponent_isWeightedHomogeneous n φ

@[simp]

Depends on / 依赖: weightedHomogeneousComponent_isWeightedHomogeneous
-/
theorem homogeneousComponent_isHomogeneous : (homogeneousComponent n φ).IsHomogeneous n :=
  weightedHomogeneousComponent_isWeightedHomogeneous n φ

@[simp]
/--
theorem `homogeneousComponent_zero` / 定理 `homogeneousComponent_zero`

English:
theorem homogeneousComponent_zero
  statement: homogeneousComponent 0 φ = C (coeff 0 φ)
  proof: weightedHomogeneousComponent_zero φ (fun _ => Nat.succ_ne_zero Nat.zero)

@[simp]

中文:
定理 homogeneousComponent_zero
  结论: homogeneousComponent 0 φ = C (coeff 0 φ)
  证明: weightedHomogeneousComponent_zero φ (fun _ => Nat.succ_ne_zero Nat.zero)

@[simp]

Depends on / 依赖: Nat.succ_ne_zero, Nat.zero, succ_ne_zero, weightedHomogeneousComponent_zero
-/
theorem homogeneousComponent_zero : homogeneousComponent 0 φ = C (coeff 0 φ) :=
  weightedHomogeneousComponent_zero φ (fun _ => Nat.succ_ne_zero Nat.zero)

@[simp]
/--
theorem `homogeneousComponent_C_mul` / 定理 `homogeneousComponent_C_mul`

English:
theorem homogeneousComponent_C_mul
  given: (n : Nat) (r : R)
  proof: weightedHomogeneousComponent_C_mul φ n r

中文:
定理 homogeneousComponent_C_mul
  条件: (n : 自然数) (r : R)
  证明: weightedHomogeneousComponent_C_mul φ n r

Depends on / 依赖: weightedHomogeneousComponent_C_mul
-/
theorem homogeneousComponent_C_mul (n : Nat) (r : R) :
    homogeneousComponent n (C r * φ) = C r * homogeneousComponent n φ :=
  weightedHomogeneousComponent_C_mul φ n r

/--
theorem `homogeneousComponent_eq_zero'` / 定理 `homogeneousComponent_eq_zero'`

English:
theorem homogeneousComponent_eq_zero'
  proof: by
  simp_rw [degree_eq_weight_one] at h
  exact weightedHomogeneousComponent_eq_zero' n φ h

中文:
定理 homogeneousComponent_eq_zero'
  证明: by
  simp_rw [degree_eq_weight_one] at h
  exact weightedHomogeneousComponent_eq_zero' n φ h

Depends on / 依赖: degree_eq_weight_one, simp_rw, weightedHomogeneousComponent_eq_zero
-/
theorem homogeneousComponent_eq_zero'
    (h : forall d : σ ->₀ Nat, d in φ.support -> d.degree != n) :
    homogeneousComponent n φ = 0 := by
  simp_rw [degree_eq_weight_one] at h
  exact weightedHomogeneousComponent_eq_zero' n φ h

/--
theorem `homogeneousComponent_eq_zero` / 定理 `homogeneousComponent_eq_zero`

English:
theorem homogeneousComponent_eq_zero
  given: (h : φ.totalDegree < n)
  statement: homogeneousComponent n φ = 0
  proof: by
  apply homogeneousComponent_eq_zero'
  rw [totalDegree]; rw [Finset.sup_lt_iff (lt_of_le_of_lt (Nat.zero_le _) h)] at h
  intro d hd; exact ne_of_lt (h d hd)

中文:
定理 homogeneousComponent_eq_zero
  条件: (h : φ.totalDegree < n)
  结论: homogeneousComponent n φ = 0
  证明: by
  apply homogeneousComponent_eq_zero'
  rw [totalDegree]; rw [Finset.sup_lt_iff (lt_of_le_of_lt (Nat.zero_le _) h)] at h
  intro d hd; exact ne_of_lt (h d hd)

Depends on / 依赖: Finset, Finset.sup_lt_iff, Nat.zero_le, homogeneousComponent_eq_zero, lt_of_le_of_lt, ne_of_lt, sup_lt_iff, totalDegree, zero_le
-/
theorem homogeneousComponent_eq_zero (h : φ.totalDegree < n) : homogeneousComponent n φ = 0 := by
  apply homogeneousComponent_eq_zero'
  rw [totalDegree]; rw [Finset.sup_lt_iff (lt_of_le_of_lt (Nat.zero_le _) h)] at h
  intro d hd; exact ne_of_lt (h d hd)

/--
theorem `sum_homogeneousComponent` / 定理 `sum_homogeneousComponent`

English:
theorem sum_homogeneousComponent
  proof: by
  ext1 d
  suffices φ.totalDegree < d.support.sum d -> 0 = coeff d φ by
    simpa [coeff_sum, coeff_homogeneousComponent]
  exact fun h => (coeff_eq_zero_of_totalDegree_lt h).symm

中文:
定理 sum_homogeneousComponent
  证明: by
  ext1 d
  suffices φ.totalDegree < d.support.sum d -> 0 = coeff d φ by
    simpa [coeff_sum, coeff_homogeneousComponent]
  exact fun h => (coeff_eq_zero_of_totalDegree_lt h).symm

Depends on / 依赖: coeff_eq_zero_of_totalDegree_lt, coeff_homogeneousComponent, coeff_sum, d.support.sum, support, totalDegree
-/
theorem sum_homogeneousComponent :
    (∑ i in range (φ.totalDegree + 1), homogeneousComponent i φ) = φ := by
  ext1 d
  suffices φ.totalDegree < d.support.sum d -> 0 = coeff d φ by
    simpa [coeff_sum, coeff_homogeneousComponent]
  exact fun h => (coeff_eq_zero_of_totalDegree_lt h).symm

/--
theorem `homogeneousComponent_of_mem` / 定理 `homogeneousComponent_of_mem`

English:
theorem homogeneousComponent_of_mem
  statement: {m n : Nat} {p : MvPolynomial σ R}
  proof: weightedHomogeneousComponent_of_mem h

中文:
定理 homogeneousComponent_of_mem
  结论: {m n : 自然数} {p : 多元多项式 σ R}
  证明: weightedHomogeneousComponent_of_mem h

Depends on / 依赖: weightedHomogeneousComponent_of_mem
-/
theorem homogeneousComponent_of_mem {m n : Nat} {p : MvPolynomial σ R}
    (h : p in homogeneousSubmodule σ R n) :
    homogeneousComponent m p = if m = n then p else 0 :=
  weightedHomogeneousComponent_of_mem h

/--
lemma `homogeneousComponent_eq_self` / 引理 `homogeneousComponent_eq_self`

English:
lemma homogeneousComponent_eq_self
  statement: {n : Nat} {p : MvPolynomial σ R}
  proof: by
  simp [homogeneousComponent_of_mem hp]

中文:
引理 homogeneousComponent_eq_self
  结论: {n : 自然数} {p : 多元多项式 σ R}
  证明: by
  simp [homogeneousComponent_of_mem hp]

Depends on / 依赖: homogeneousComponent_of_mem
-/
lemma homogeneousComponent_eq_self {n : Nat} {p : MvPolynomial σ R}
    (hp : p.IsHomogeneous n) : homogeneousComponent n p = p := by
  simp [homogeneousComponent_of_mem hp]

/--
lemma `support_homogeneousComponent` / 引理 `support_homogeneousComponent`

English:
lemma support_homogeneousComponent
  given: (n : Nat) (p : MvPolynomial σ R)
  proof: by
  rw [degree_eq_weight_one]
  exact support_weightedHomogeneousComponent n p

中文:
引理 support_homogeneousComponent
  条件: (n : 自然数) (p : 多元多项式 σ R)
  证明: by
  rw [degree_eq_weight_one]
  exact support_weightedHomogeneousComponent n p

Depends on / 依赖: degree_eq_weight_one, support_weightedHomogeneousComponent
-/
lemma support_homogeneousComponent (n : Nat) (p : MvPolynomial σ R) :
    (homogeneousComponent n p).support = {c in p.support | c.degree = n} := by
  rw [degree_eq_weight_one]
  exact support_weightedHomogeneousComponent n p

/--
lemma `rename_homogeneousComponent` / 引理 `rename_homogeneousComponent`

English:
lemma rename_homogeneousComponent
  given: {τ : Type*} {φ : σ -> τ} (n : Nat) (p : MvPolynomial σ R)
  proof: by
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
    rw [rename_monomial]; rw [homogeneousComponent_of_mem (isHomogeneous_monomial c rfl)]; rw [homogeneousComponent_of_mem (isHomogeneous_monomial c (Finsupp.degree_mapDomain φ d))]
    split_ifs <;> simp [rename_monomial]
  

中文:
引理 rename_homogeneousComponent
  条件: {τ : 类型} {φ : σ -> τ} (n : 自然数) (p : 多元多项式 σ R)
  证明: by
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
    rw [rename_monomial]; rw [homogeneousComponent_of_mem (isHomogeneous_monomial c rfl)]; rw [homogeneousComponent_of_mem (isHomogeneous_monomial c (Finsupp.degree_mapDomain φ d))]
    split_ifs <;> simp [rename_monomial]
  

Depends on / 依赖: Finsupp, Finsupp.degree_mapDomain, MvPolynomial, MvPolynomial.induction_on, degree_mapDomain, homogeneousComponent_of_mem, induction_on, isHomogeneous_monomial, map_add, monomial, rename_monomial, split_ifs
-/
lemma rename_homogeneousComponent {τ : Type*} {φ : σ -> τ} (n : Nat) (p : MvPolynomial σ R) :
    rename φ (homogeneousComponent n p) = homogeneousComponent n (rename φ p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
    rw [rename_monomial]; rw [homogeneousComponent_of_mem (isHomogeneous_monomial c rfl)]; rw [homogeneousComponent_of_mem (isHomogeneous_monomial c (Finsupp.degree_mapDomain φ d))]
    split_ifs <;> simp [rename_monomial]
  | add p q hp hq => simp [map_add, hp, hq]


end HomogeneousComponent

end

noncomputable section GradedAlgebra

/--
lemma `HomogeneousSubmodule.gradedMonoid` / 引理 `HomogeneousSubmodule.gradedMonoid`

English:
lemma HomogeneousSubmodule.gradedMonoid
  proof: WeightedHomogeneousSubmodule.gradedMonoid

中文:
引理 齐次子模.gradedMonoid
  证明: WeightedHomogeneousSubmodule.gradedMonoid

Depends on / 依赖: WeightedHomogeneousSubmodule, WeightedHomogeneousSubmodule.gradedMonoid, gradedMonoid
-/
lemma HomogeneousSubmodule.gradedMonoid :
    SetLike.GradedMonoid (homogeneousSubmodule σ R) :=
  WeightedHomogeneousSubmodule.gradedMonoid

/--
Definition of `decomposition` / `decomposition` 的定义

English:
abbreviation decomposition
  signature: :
  body: fast_instance% weightedDecomposition R (1 : σ -> Nat)

中文:
缩写 decomposition
  签名: :
  定义体: fast_instance% weightedDecomposition R (1 : σ -> Nat)

Depends on / 依赖: fast_instance, weightedDecomposition
-/
abbrev decomposition :
    DirectSum.Decomposition (homogeneousSubmodule σ R) :=
  fast_instance% weightedDecomposition R (1 : σ -> Nat)

/--
Definition of `gradedAlgebra` / `gradedAlgebra` 的定义

English:
abbreviation gradedAlgebra
  signature: : GradedAlgebra (homogeneousSubmodule σ R)
  body: fast_instance% weightedGradedAlgebra R (1 : σ -> Nat)

中文:
缩写 gradedAlgebra
  签名: : 分次代数 (homogeneousSubmodule σ R)
  定义体: fast_instance% weightedGradedAlgebra R (1 : σ -> Nat)

Depends on / 依赖: fast_instance, weightedGradedAlgebra
-/
abbrev gradedAlgebra : GradedAlgebra (homogeneousSubmodule σ R) :=
  fast_instance% weightedGradedAlgebra R (1 : σ -> Nat)

/--
theorem `decomposition.decompose'_apply` / 定理 `decomposition.decompose'_apply`

English:
theorem decomposition.decompose'_apply
  given: (φ : MvPolynomial σ R) (i : Nat)
  proof: weightedDecomposition.decompose'_apply R _ φ i

中文:
定理 decomposition.decompose'_apply
  条件: (φ : 多元多项式 σ R) (i : 自然数)
  证明: weightedDecomposition.decompose'_apply R _ φ i

Depends on / 依赖: _apply, decompose, weightedDecomposition, weightedDecomposition.decompose
-/
theorem decomposition.decompose'_apply (φ : MvPolynomial σ R) (i : Nat) :
    (decomposition.decompose' φ i : MvPolynomial σ R) = homogeneousComponent i φ :=
  weightedDecomposition.decompose'_apply R _ φ i

/--
theorem `decomposition.decompose'_eq` / 定理 `decomposition.decompose'_eq`

English:
theorem decomposition.decompose'_eq
  proof: by
  rw [degree_eq_weight_one]
  rfl

中文:
定理 decomposition.decompose'_eq
  证明: by
  rw [degree_eq_weight_one]
  rfl
-/
theorem decomposition.decompose'_eq :
    decomposition.decompose' = fun φ : MvPolynomial σ R =>
      DirectSum.mk (fun i : Nat => ↥(homogeneousSubmodule σ R i)) (φ.support.image Finsupp.degree)
        fun m => ⟨homogeneousComponent m φ, homogeneousComponent_mem m φ⟩ := by
  rw [degree_eq_weight_one]
  rfl

attribute [local instance] MvPolynomial.gradedAlgebra

/--
lemma `mem_iff_homogeneousComponent_mem` / 引理 `mem_iff_homogeneousComponent_mem`

English:
lemma mem_iff_homogeneousComponent_mem
  statement: {I : Ideal (MvPolynomial σ R)}
  proof: mem_iff_weightedHomogeneousComponent_mem R (1 : σ -> Nat) h p

中文:
引理 mem_iff_homogeneousComponent_mem
  结论: {I : 理想 (多元多项式 σ R)}
  证明: mem_iff_weightedHomogeneousComponent_mem R (1 : σ -> Nat) h p

Depends on / 依赖: mem_iff_weightedHomogeneousComponent_mem
-/
lemma mem_iff_homogeneousComponent_mem {I : Ideal (MvPolynomial σ R)}
    (h : I.IsHomogeneous (homogeneousSubmodule σ R)) (p : MvPolynomial σ R) :
    p in I ↔ forall n, (homogeneousComponent n p) in I :=
  mem_iff_weightedHomogeneousComponent_mem R (1 : σ -> Nat) h p

/--
lemma `homogeneousComponent_mem_of_mem` / 引理 `homogeneousComponent_mem_of_mem`

English:
lemma homogeneousComponent_mem_of_mem
  statement: {I : Ideal (MvPolynomial σ R)}
  proof: weightedHomogeneousComponent_mem_of_mem R (1 : σ -> Nat) h hp n

中文:
引理 homogeneousComponent_mem_of_mem
  结论: {I : 理想 (多元多项式 σ R)}
  证明: weightedHomogeneousComponent_mem_of_mem R (1 : σ -> Nat) h hp n

Depends on / 依赖: weightedHomogeneousComponent_mem_of_mem
-/
lemma homogeneousComponent_mem_of_mem {I : Ideal (MvPolynomial σ R)}
    (h : I.IsHomogeneous (homogeneousSubmodule σ R)) {p : MvPolynomial σ R} (hp : p in I) (n : Nat) :
    (homogeneousComponent n p) in I :=
  weightedHomogeneousComponent_mem_of_mem R (1 : σ -> Nat) h hp n

end GradedAlgebra

end MvPolynomial

/--
lemma `Ideal.span_eq_map_homogeneousSubmodule` / 引理 `Ideal.span_eq_map_homogeneousSubmodule`

English:
lemma Ideal.span_eq_map_homogeneousSubmodule
  statement: {ι R : Type*} [CommSemiring R]
  proof: by
  simp [MvPolynomial.homogeneousSubmodule_one_eq_span_X, Submodule.map_span, ← Set.range_comp,
    Function.comp_def]

中文:
引理 理想.span_eq_map_homogeneousSubmodule
  结论: {ι R : 类型} [交换半环 R]
  证明: by
  simp [MvPolynomial.homogeneousSubmodule_one_eq_span_X, Submodule.map_span, ← Set.range_comp,
    Function.comp_def]

Depends on / 依赖: Function, Function.comp_def, MvPolynomial, MvPolynomial.homogeneousSubmodule_one_eq_span_X, Set.range_comp, Submodule, Submodule.map_span, comp_def, homogeneousSubmodule_one_eq_span_X, map_span, range_comp
-/
lemma Ideal.span_eq_map_homogeneousSubmodule {ι R : Type*} [CommSemiring R]
    (x : ι -> R) :
    Ideal.span (Set.range x) =
      Submodule.map (MvPolynomial.aeval x).toLinearMap
        (MvPolynomial.homogeneousSubmodule ι R 1) := by
  simp [MvPolynomial.homogeneousSubmodule_one_eq_span_X, Submodule.map_span, ← Set.range_comp,
    Function.comp_def]

/--
lemma `Ideal.span_pow_eq_map_homogeneousSubmodule` / 引理 `Ideal.span_pow_eq_map_homogeneousSubmodule`

English:
lemma Ideal.span_pow_eq_map_homogeneousSubmodule
  statement: {ι R : Type*} [CommSemiring R]
  proof: by
  rw [← MvPolynomial.homogeneousSubmodule_one_pow]; rw [Submodule.map_pow]; rw [Ideal.span_eq_map_homogeneousSubmodule]

中文:
引理 理想.span_pow_eq_map_homogeneousSubmodule
  结论: {ι R : 类型} [交换半环 R]
  证明: by
  rw [← MvPolynomial.homogeneousSubmodule_one_pow]; rw [Submodule.map_pow]; rw [Ideal.span_eq_map_homogeneousSubmodule]

Depends on / 依赖: Ideal.span_eq_map_homogeneousSubmodule, MvPolynomial, MvPolynomial.homogeneousSubmodule_one_pow, Submodule, Submodule.map_pow, homogeneousSubmodule_one_pow, map_pow, span_eq_map_homogeneousSubmodule
-/
lemma Ideal.span_pow_eq_map_homogeneousSubmodule {ι R : Type*} [CommSemiring R]
    (x : ι -> R) (n : Nat) :
    Ideal.span (Set.range x) ^ n =
      Submodule.map (MvPolynomial.aeval x).toLinearMap
        (MvPolynomial.homogeneousSubmodule ι R n) := by
  rw [← MvPolynomial.homogeneousSubmodule_one_pow]; rw [Submodule.map_pow]; rw [Ideal.span_eq_map_homogeneousSubmodule]

/--
lemma `Ideal.mem_span_pow_iff_exists_isHomogeneous` / 引理 `Ideal.mem_span_pow_iff_exists_isHomogeneous`

English:
lemma Ideal.mem_span_pow_iff_exists_isHomogeneous
  statement: {ι R : Type*} [CommSemiring R] {n : Nat} (x : ι -> R)
  proof: by
  simp [Ideal.span_pow_eq_map_homogeneousSubmodule]

中文:
引理 理想.mem_span_pow_iff_存在_isHomogeneous
  结论: {ι R : 类型} [交换半环 R] {n : 自然数} (x : ι -> R)
  证明: by
  simp [Ideal.span_pow_eq_map_homogeneousSubmodule]

Depends on / 依赖: Ideal.span_pow_eq_map_homogeneousSubmodule, span_pow_eq_map_homogeneousSubmodule
-/
lemma Ideal.mem_span_pow_iff_exists_isHomogeneous {ι R : Type*} [CommSemiring R] {n : Nat} (x : ι -> R)
    (y : R) :
    y in (Ideal.span <| Set.range x) ^ n ↔
      exists (p : MvPolynomial ι R), p.IsHomogeneous n ∧ p.eval x = y := by
  simp [Ideal.span_pow_eq_map_homogeneousSubmodule]

/--
lemma `Ideal.mem_span_iff_exists_isHomogeneous` / 引理 `Ideal.mem_span_iff_exists_isHomogeneous`

English:
lemma Ideal.mem_span_iff_exists_isHomogeneous
  given: {ι R : Type*} [CommSemiring R] (x : ι -> R) (y : R)
  proof: by
  simp [Ideal.span_eq_map_homogeneousSubmodule]

中文:
引理 理想.mem_span_iff_存在_isHomogeneous
  条件: {ι R : 类型} [交换半环 R] (x : ι -> R) (y : R)
  证明: by
  simp [Ideal.span_eq_map_homogeneousSubmodule]

Depends on / 依赖: Ideal.span_eq_map_homogeneousSubmodule, span_eq_map_homogeneousSubmodule
-/
lemma Ideal.mem_span_iff_exists_isHomogeneous {ι R : Type*} [CommSemiring R] (x : ι -> R) (y : R) :
    y in Ideal.span (.range x) ↔
      exists (p : MvPolynomial ι R), p.IsHomogeneous 1 ∧ p.eval x = y := by
  simp [Ideal.span_eq_map_homogeneousSubmodule]
