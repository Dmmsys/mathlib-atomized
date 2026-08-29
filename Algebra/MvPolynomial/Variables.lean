/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Johan Commelin, Mario Carneiro
-/
module

public import Mathlib.Data.Finsupp.Lex
public import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# Variables of polynomials

This file establishes many results about the variable sets of a multivariate polynomial.

The *variable set* of a polynomial $P \in R[X]$ is a `Finset` containing each $x \in X$
that appears in a monomial in $P$.


## Main declarations

* `MvPolynomial.vars p` : the finset of variables occurring in `p`.
  For example if `p = x⁴y+yz` then `vars p = {x, y, z}`

## Notation

As in other polynomial files, we typically use the notation:

+ `σ τ : Type*` (indexing the variables)

+ `R : Type*` `[CommSemiring R]` (the coefficients)

+ `s : σ →₀ ℕ`, a function from `σ` to `ℕ` which is zero away from a finite set.
  This will give rise to a monomial in `MvPolynomial σ R` which mathematicians might call `X^s`.

+ `r : R`

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `p : MvPolynomial σ R`

-/

@[expose] public section


noncomputable section

open Set Function Finsupp AddMonoidAlgebra

universe u v w

variable {R : Type u} {S : Type v}

namespace MvPolynomial

variable {σ τ : Type*} {r : R} {e : Nat} {n m : σ} {s : σ ->₀ Nat}

section CommSemiring

variable [CommSemiring R] {p q : MvPolynomial σ R}

section Vars

/-! ### `vars` -/


/--
Definition of `vars` / `vars` 的定义

English:
definition vars
  signature: (p : MvPolynomial σ R)
  body: letI := Classical.decEq σ
  p.degrees.toFinset

中文:
定义 vars
  签名: (p : 多元多项式 σ R)
  定义体: letI := Classical.decEq σ
  p.degrees.toFinset

Depends on / 依赖: Classical, Classical.decEq, degrees, p.degrees.toFinset, toFinset
-/
def vars (p : MvPolynomial σ R) : Finset σ :=
  letI := Classical.decEq σ
  p.degrees.toFinset

/--
theorem `vars_def` / 定理 `vars_def`

English:
theorem vars_def
  given: [DecidableEq σ] (p : MvPolynomial σ R)
  statement: p.vars = p.degrees.toFinset
  proof: by
  rw [vars]
  convert! rfl

@[simp]

中文:
定理 vars_def
  条件: [DecidableEq σ] (p : 多元多项式 σ R)
  结论: p.vars = p.degrees.toFinset
  证明: by
  rw [vars]
  convert! rfl

@[simp]

Depends on / 依赖: convert
-/
theorem vars_def [DecidableEq σ] (p : MvPolynomial σ R) : p.vars = p.degrees.toFinset := by
  rw [vars]
  convert! rfl

@[simp]
/--
theorem `vars_0` / 定理 `vars_0`

English:
theorem vars_0
  statement: (0 : MvPolynomial σ R).vars = ∅
  proof: by
  classical rw [vars_def, degrees_zero, Multiset.toFinset_zero]

@[simp]

中文:
定理 vars_0
  结论: (0 : 多元多项式 σ R).vars = ∅
  证明: by
  classical rw [vars_def, degrees_zero, Multiset.toFinset_zero]

@[simp]

Depends on / 依赖: Multiset, Multiset.toFinset_zero, classical, degrees_zero, toFinset_zero, vars_def
-/
theorem vars_0 : (0 : MvPolynomial σ R).vars = ∅ := by
  classical rw [vars_def, degrees_zero, Multiset.toFinset_zero]

@[simp]
/--
theorem `vars_monomial` / 定理 `vars_monomial`

English:
theorem vars_monomial
  given: (h : r != 0)
  statement: (monomial s r).vars = s.support
  proof: by
  classical rw [vars_def, degrees_monomial_eq _ _ h, Finsupp.toFinset_toMultiset]

@[simp]

中文:
定理 vars_monomial
  条件: (h : r != 0)
  结论: (monomial s r).vars = s.support
  证明: by
  classical rw [vars_def, degrees_monomial_eq _ _ h, Finsupp.toFinset_toMultiset]

@[simp]

Depends on / 依赖: Finsupp, Finsupp.toFinset_toMultiset, classical, degrees_monomial_eq, toFinset_toMultiset, vars_def
-/
theorem vars_monomial (h : r != 0) : (monomial s r).vars = s.support := by
  classical rw [vars_def, degrees_monomial_eq _ _ h, Finsupp.toFinset_toMultiset]

@[simp]
/--
theorem `vars_C` / 定理 `vars_C`

English:
theorem vars_C
  statement: (C r : MvPolynomial σ R).vars = ∅
  proof: by
  classical rw [vars_def, degrees_C, Multiset.toFinset_zero]

@[simp]

中文:
定理 vars_C
  结论: (C r : 多元多项式 σ R).vars = ∅
  证明: by
  classical rw [vars_def, degrees_C, Multiset.toFinset_zero]

@[simp]

Depends on / 依赖: Multiset, Multiset.toFinset_zero, classical, degrees_C, toFinset_zero, vars_def
-/
theorem vars_C : (C r : MvPolynomial σ R).vars = ∅ := by
  classical rw [vars_def, degrees_C, Multiset.toFinset_zero]

@[simp]
/--
theorem `vars_X` / 定理 `vars_X`

English:
theorem vars_X
  given: [Nontrivial R]
  statement: (X n : MvPolynomial σ R).vars = {n}
  proof: by
  rw [X]; rw [vars_monomial (one_ne_zero' R)]; rw [Finsupp.support_single _ (one_ne_zero' Nat)]

中文:
定理 vars_X
  条件: [非平凡 R]
  结论: (X n : 多元多项式 σ R).vars = {n}
  证明: by
  rw [X]; rw [vars_monomial (one_ne_zero' R)]; rw [Finsupp.support_single _ (one_ne_zero' Nat)]

Depends on / 依赖: Finsupp, Finsupp.support_single, one_ne_zero, support_single, vars_monomial
-/
theorem vars_X [Nontrivial R] : (X n : MvPolynomial σ R).vars = {n} := by
  rw [X]; rw [vars_monomial (one_ne_zero' R)]; rw [Finsupp.support_single _ (one_ne_zero' Nat)]

/--
theorem `mem_vars_iff_mem_support` / 定理 `mem_vars_iff_mem_support`

English:
theorem mem_vars_iff_mem_support
  given: (i : σ)
  statement: i in p.vars ↔ exists d in p.support, i in d.support
  proof: by
  classical simp only [vars_def, Multiset.mem_toFinset, mem_degrees, mem_support_iff]

@[deprecated (since := "2026-04-24")] alias mem_vars := mem_vars_iff_mem_support

中文:
定理 mem_vars_iff_mem_support
  条件: (i : σ)
  结论: i in p.vars ↔ 存在 d in p.support, i in d.support
  证明: by
  classical simp only [vars_def, Multiset.mem_toFinset, mem_degrees, mem_support_iff]

@[deprecated (since := "2026-04-24")] alias mem_vars := mem_vars_iff_mem_support

Depends on / 依赖: Multiset, Multiset.mem_toFinset, classical, mem_degrees, mem_support_iff, mem_toFinset, vars_def
-/
theorem mem_vars_iff_mem_support (i : σ) : i in p.vars ↔ exists d in p.support, i in d.support := by
  classical simp only [vars_def, Multiset.mem_toFinset, mem_degrees, mem_support_iff]

@[deprecated (since := "2026-04-24")] alias mem_vars := mem_vars_iff_mem_support

/--
theorem `mem_vars_iff_degreeOf_ne_zero` / 定理 `mem_vars_iff_degreeOf_ne_zero`

English:
theorem mem_vars_iff_degreeOf_ne_zero
  given: {i : σ}
  statement: i in p.vars ↔ p.degreeOf i != 0
  proof: by
  classical simp [degreeOf, vars_def]

中文:
定理 mem_vars_iff_degreeOf_ne_zero
  条件: {i : σ}
  结论: i in p.vars ↔ p.degreeOf i != 0
  证明: by
  classical simp [degreeOf, vars_def]

Depends on / 依赖: classical, degreeOf, vars_def
-/
theorem mem_vars_iff_degreeOf_ne_zero {i : σ} : i in p.vars ↔ p.degreeOf i != 0 := by
  classical simp [degreeOf, vars_def]

/--
theorem `mem_support_notMem_vars_zero` / 定理 `mem_support_notMem_vars_zero`

English:
theorem mem_support_notMem_vars_zero
  statement: {f : MvPolynomial σ R} {x : σ ->₀ Nat} (H : x in f.support)
  proof: by
  contrapose! h
  exact (mem_vars_iff_mem_support v).mpr ⟨x, H, Finsupp.mem_support_iff.mpr h⟩

中文:
定理 mem_support_notMem_vars_zero
  结论: {f : 多元多项式 σ R} {x : σ ->₀ 自然数} (H : x in f.support)
  证明: by
  contrapose! h
  exact (mem_vars_iff_mem_support v).mpr ⟨x, H, Finsupp.mem_support_iff.mpr h⟩

Depends on / 依赖: Finsupp, Finsupp.mem_support_iff.mpr, contrapose, mem_support_iff, mem_vars_iff_mem_support
-/
theorem mem_support_notMem_vars_zero {f : MvPolynomial σ R} {x : σ ->₀ Nat} (H : x in f.support)
    {v : σ} (h : v ∉ vars f) : x v = 0 := by
  contrapose! h
  exact (mem_vars_iff_mem_support v).mpr ⟨x, H, Finsupp.mem_support_iff.mpr h⟩

/--
theorem `support_subset_vars_of_mem_support` / 定理 `support_subset_vars_of_mem_support`

English:
theorem support_subset_vars_of_mem_support
  given: {s : σ ->₀ Nat} (h : s in p.support)
  proof: fun i hi => by
  contrapose! hi
  simp [mem_support_notMem_vars_zero h hi]

中文:
定理 support_subset_vars_of_mem_support
  条件: {s : σ ->₀ 自然数} (h : s in p.support)
  证明: fun i hi => by
  contrapose! hi
  simp [mem_support_notMem_vars_zero h hi]

Depends on / 依赖: contrapose, mem_support_notMem_vars_zero
-/
theorem support_subset_vars_of_mem_support {s : σ ->₀ Nat} (h : s in p.support) :
    s.support subseteq p.vars := fun i hi => by
  contrapose! hi
  simp [mem_support_notMem_vars_zero h hi]

/--
theorem `vars_eq_empty_iff_eq_C` / 定理 `vars_eq_empty_iff_eq_C`

English:
theorem vars_eq_empty_iff_eq_C
  statement: p.vars = ∅ ↔ p = C (p.coeff 0)
  proof: by
  refine ⟨fun h => ?_, fun h => by rw [h]; simp⟩
  rw [← totalDegree_eq_zero_iff_eq_C]
  suffices p.degrees.card = 0 by grind [totalDegree_le_degrees_card p]
  classical rw [vars_def, Multiset.toFinset_eq_empty] at h
  simp_all

中文:
定理 vars_eq_empty_iff_eq_C
  结论: p.vars = ∅ ↔ p = C (p.coeff 0)
  证明: by
  refine ⟨fun h => ?_, fun h => by rw [h]; simp⟩
  rw [← totalDegree_eq_zero_iff_eq_C]
  suffices p.degrees.card = 0 by grind [totalDegree_le_degrees_card p]
  classical rw [vars_def, Multiset.toFinset_eq_empty] at h
  simp_all

Depends on / 依赖: Multiset, Multiset.toFinset_eq_empty, classical, degrees, p.degrees.card, toFinset_eq_empty, totalDegree_eq_zero_iff_eq_C, totalDegree_le_degrees_card, vars_def
-/
theorem vars_eq_empty_iff_eq_C : p.vars = ∅ ↔ p = C (p.coeff 0) := by
  refine ⟨fun h => ?_, fun h => by rw [h]; simp⟩
  rw [← totalDegree_eq_zero_iff_eq_C]
  suffices p.degrees.card = 0 by grind [totalDegree_le_degrees_card p]
  classical rw [vars_def, Multiset.toFinset_eq_empty] at h
  simp_all

/--
theorem `vars_add_subset` / 定理 `vars_add_subset`

English:
theorem vars_add_subset
  given: [DecidableEq σ] (p q : MvPolynomial σ R)
  proof: by
  intro x hx
  simp only [vars_def, Finset.mem_union, Multiset.mem_toFinset] at hx ⊢
  simpa using Multiset.mem_of_le degrees_add_le hx

中文:
定理 vars_add_subset
  条件: [DecidableEq σ] (p q : 多元多项式 σ R)
  证明: by
  intro x hx
  simp only [vars_def, Finset.mem_union, Multiset.mem_toFinset] at hx ⊢
  simpa using Multiset.mem_of_le degrees_add_le hx

Depends on / 依赖: Finset, Finset.mem_union, Multiset, Multiset.mem_of_le, Multiset.mem_toFinset, degrees_add_le, mem_of_le, mem_toFinset, mem_union, vars_def
-/
theorem vars_add_subset [DecidableEq σ] (p q : MvPolynomial σ R) :
    (p + q).vars subseteq p.vars union q.vars := by
  intro x hx
  simp only [vars_def, Finset.mem_union, Multiset.mem_toFinset] at hx ⊢
  simpa using Multiset.mem_of_le degrees_add_le hx

/--
theorem `vars_add_of_disjoint` / 定理 `vars_add_of_disjoint`

English:
theorem vars_add_of_disjoint
  given: [DecidableEq σ] (h : Disjoint p.vars q.vars)
  proof: by
  refine (vars_add_subset p q).antisymm fun x hx => ?_
  simp only [vars_def, Multiset.disjoint_toFinset] at h hx ⊢
  rwa [degrees_add_of_disjoint h, Multiset.toFinset_union]

中文:
定理 vars_add_of_disjoint
  条件: [DecidableEq σ] (h : Disjoint p.vars q.vars)
  证明: by
  refine (vars_add_subset p q).antisymm fun x hx => ?_
  simp only [vars_def, Multiset.disjoint_toFinset] at h hx ⊢
  rwa [degrees_add_of_disjoint h, Multiset.toFinset_union]

Depends on / 依赖: Multiset, Multiset.disjoint_toFinset, Multiset.toFinset_union, antisymm, degrees_add_of_disjoint, disjoint_toFinset, toFinset_union, vars_add_subset, vars_def
-/
theorem vars_add_of_disjoint [DecidableEq σ] (h : Disjoint p.vars q.vars) :
    (p + q).vars = p.vars union q.vars := by
  refine (vars_add_subset p q).antisymm fun x hx => ?_
  simp only [vars_def, Multiset.disjoint_toFinset] at h hx ⊢
  rwa [degrees_add_of_disjoint h, Multiset.toFinset_union]

section Mul

/--
theorem `vars_mul` / 定理 `vars_mul`

English:
theorem vars_mul
  given: [DecidableEq σ] (φ ψ : MvPolynomial σ R)
  statement: (φ * ψ).vars subseteq φ.vars union ψ.vars
  proof: by
  simp_rw [vars_def, ← Multiset.toFinset_add, Multiset.toFinset_subset]
  exact Multiset.subset_of_le degrees_mul_le

@[simp]

中文:
定理 vars_mul
  条件: [DecidableEq σ] (φ ψ : 多元多项式 σ R)
  结论: (φ * ψ).vars subseteq φ.vars union ψ.vars
  证明: by
  simp_rw [vars_def, ← Multiset.toFinset_add, Multiset.toFinset_subset]
  exact Multiset.subset_of_le degrees_mul_le

@[simp]

Depends on / 依赖: Multiset, Multiset.subset_of_le, Multiset.toFinset_add, Multiset.toFinset_subset, degrees_mul_le, simp_rw, subset_of_le, toFinset_add, toFinset_subset, vars_def
-/
theorem vars_mul [DecidableEq σ] (φ ψ : MvPolynomial σ R) : (φ * ψ).vars subseteq φ.vars union ψ.vars := by
  simp_rw [vars_def, ← Multiset.toFinset_add, Multiset.toFinset_subset]
  exact Multiset.subset_of_le degrees_mul_le

@[simp]
/--
theorem `vars_one` / 定理 `vars_one`

English:
theorem vars_one
  statement: (1 : MvPolynomial σ R).vars = ∅
  proof: vars_C

中文:
定理 vars_one
  结论: (1 : 多元多项式 σ R).vars = ∅
  证明: vars_C

Depends on / 依赖: vars_C
-/
theorem vars_one : (1 : MvPolynomial σ R).vars = ∅ :=
  vars_C

/--
theorem `vars_pow` / 定理 `vars_pow`

English:
theorem vars_pow
  given: (φ : MvPolynomial σ R) (n : Nat)
  statement: (φ ^ n).vars subseteq φ.vars
  proof: by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    apply Finset.Subset.trans (vars_mul _ _)
    exact Finset.union_subset (Finset.Subset.refl _) ih

中文:
定理 vars_pow
  条件: (φ : 多元多项式 σ R) (n : 自然数)
  结论: (φ ^ n).vars subseteq φ.vars
  证明: by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    apply Finset.Subset.trans (vars_mul _ _)
    exact Finset.union_subset (Finset.Subset.refl _) ih

Depends on / 依赖: Finset, Finset.Subset.refl, Finset.Subset.trans, Finset.union_subset, Subset, classical, pow_succ, union_subset, vars_mul
-/
theorem vars_pow (φ : MvPolynomial σ R) (n : Nat) : (φ ^ n).vars subseteq φ.vars := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    apply Finset.Subset.trans (vars_mul _ _)
    exact Finset.union_subset (Finset.Subset.refl _) ih

/--
theorem `vars_prod` / 定理 `vars_prod`

English:
theorem vars_prod
  given: {ι : Type*} [DecidableEq σ] {s : Finset ι} (f : ι -> MvPolynomial σ R)
  proof: by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert _ _ hs hsub =>
    simp only [hs, Finset.biUnion_insert, Finset.prod_insert, not_false_iff]
    apply Finset.Subset.trans (vars_mul _ _)
    exact Finset.union_subset_union (Finset.Subset.refl _) hsub

中文:
定理 vars_prod
  条件: {ι : 类型} [DecidableEq σ] {s : 有限集 ι} (f : ι -> 多元多项式 σ R)
  证明: by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert _ _ hs hsub =>
    simp only [hs, Finset.biUnion_insert, Finset.prod_insert, not_false_iff]
    apply Finset.Subset.trans (vars_mul _ _)
    exact Finset.union_subset_union (Finset.Subset.refl _) hsub

Depends on / 依赖: Finset, Finset.Subset.refl, Finset.Subset.trans, Finset.biUnion_insert, Finset.induction_on, Finset.prod_insert, Finset.union_subset_union, Subset, biUnion_insert, classical, induction_on, insert, not_false_iff, prod_insert, union_subset_union, vars_mul
-/
theorem vars_prod {ι : Type*} [DecidableEq σ] {s : Finset ι} (f : ι -> MvPolynomial σ R) :
    (∏ i in s, f i).vars subseteq s.biUnion fun i => (f i).vars := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert _ _ hs hsub =>
    simp only [hs, Finset.biUnion_insert, Finset.prod_insert, not_false_iff]
    apply Finset.Subset.trans (vars_mul _ _)
    exact Finset.union_subset_union (Finset.Subset.refl _) hsub

section IsDomain

variable {A : Type*} [CommRing A] [NoZeroDivisors A]

/--
theorem `vars_C_mul` / 定理 `vars_C_mul`

English:
theorem vars_C_mul
  given: (a : A) (ha : a != 0) (φ : MvPolynomial σ A)
  proof: by
  ext1 i
  simp only [mem_vars_iff_mem_support, mem_support_iff]
  apply exists_congr
  intro d
  rw [coeff_C_mul]; rw [mul_ne_zero_iff]; rw [eq_true ha]; rw [true_and]

中文:
定理 vars_C_mul
  条件: (a : A) (ha : a != 0) (φ : 多元多项式 σ A)
  证明: by
  ext1 i
  simp only [mem_vars_iff_mem_support, mem_support_iff]
  apply exists_congr
  intro d
  rw [coeff_C_mul]; rw [mul_ne_zero_iff]; rw [eq_true ha]; rw [true_and]

Depends on / 依赖: coeff_C_mul, eq_true, exists_congr, mem_support_iff, mem_vars_iff_mem_support, mul_ne_zero_iff, true_and
-/
theorem vars_C_mul (a : A) (ha : a != 0) (φ : MvPolynomial σ A) :
    (C a * φ : MvPolynomial σ A).vars = φ.vars := by
  ext1 i
  simp only [mem_vars_iff_mem_support, mem_support_iff]
  apply exists_congr
  intro d
  rw [coeff_C_mul]; rw [mul_ne_zero_iff]; rw [eq_true ha]; rw [true_and]

end IsDomain

end Mul

section Sum

variable {ι : Type*} (t : Finset ι) (φ : ι -> MvPolynomial σ R)

/--
theorem `vars_sum_subset` / 定理 `vars_sum_subset`

English:
theorem vars_sum_subset
  given: [DecidableEq σ]
  proof: by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert _ _ has hsum =>
    rw [Finset.biUnion_insert]; rw [Finset.sum_insert has]
    refine Finset.Subset.trans
      (vars_add_subset _ _) (Finset.union_subset_union (Finset.Subset.refl _) ?_)
    assumption

中文:
定理 vars_sum_subset
  条件: [DecidableEq σ]
  证明: by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert _ _ has hsum =>
    rw [Finset.biUnion_insert]; rw [Finset.sum_insert has]
    refine Finset.Subset.trans
      (vars_add_subset _ _) (Finset.union_subset_union (Finset.Subset.refl _) ?_)
    assumption

Depends on / 依赖: Finset, Finset.Subset.refl, Finset.Subset.trans, Finset.biUnion_insert, Finset.induction_on, Finset.sum_insert, Finset.union_subset_union, Subset, biUnion_insert, classical, induction_on, insert, sum_insert, union_subset_union, vars_add_subset
-/
theorem vars_sum_subset [DecidableEq σ] :
    (∑ i in t, φ i).vars subseteq Finset.biUnion t fun i => (φ i).vars := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert _ _ has hsum =>
    rw [Finset.biUnion_insert]; rw [Finset.sum_insert has]
    refine Finset.Subset.trans
      (vars_add_subset _ _) (Finset.union_subset_union (Finset.Subset.refl _) ?_)
    assumption

/--
theorem `vars_sum_of_disjoint` / 定理 `vars_sum_of_disjoint`

English:
theorem vars_sum_of_disjoint
  given: [DecidableEq σ] (h : Pairwise <| (Disjoint on fun i => (φ i).vars))
  proof: by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert _ _ has hsum =>
    rw [Finset.biUnion_insert]; rw [Finset.sum_insert has]; rw [vars_add_of_disjoint]; rw [hsum]
    unfold Pairwise onFun at h
    simp only [Finset.disjoint_iff_ne] at h ⊢
    grind

中文:
定理 vars_sum_of_disjoint
  条件: [DecidableEq σ] (h : 两两 <| (Disjoint on fun i => (φ i).vars))
  证明: by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert _ _ has hsum =>
    rw [Finset.biUnion_insert]; rw [Finset.sum_insert has]; rw [vars_add_of_disjoint]; rw [hsum]
    unfold Pairwise onFun at h
    simp only [Finset.disjoint_iff_ne] at h ⊢
    grind

Depends on / 依赖: Finset, Finset.biUnion_insert, Finset.disjoint_iff_ne, Finset.induction_on, Finset.sum_insert, Pairwise, biUnion_insert, classical, disjoint_iff_ne, induction_on, insert, sum_insert, vars_add_of_disjoint
-/
theorem vars_sum_of_disjoint [DecidableEq σ] (h : Pairwise <| (Disjoint on fun i => (φ i).vars)) :
    (∑ i in t, φ i).vars = Finset.biUnion t fun i => (φ i).vars := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert _ _ has hsum =>
    rw [Finset.biUnion_insert]; rw [Finset.sum_insert has]; rw [vars_add_of_disjoint]; rw [hsum]
    unfold Pairwise onFun at h
    simp only [Finset.disjoint_iff_ne] at h ⊢
    grind

end Sum

section Map

variable [CommSemiring S] (f : R ->+* S)
variable (p)

/--
theorem `vars_map` / 定理 `vars_map`

English:
theorem vars_map
  statement: (map f p).vars subseteq p.vars
  proof: by
  classical simp [vars_def, Multiset.subset_of_le degrees_map_le]

中文:
定理 vars_map
  结论: (map f p).vars subseteq p.vars
  证明: by
  classical simp [vars_def, Multiset.subset_of_le degrees_map_le]

Depends on / 依赖: Multiset, Multiset.subset_of_le, classical, degrees_map_le, subset_of_le, vars_def
-/
theorem vars_map : (map f p).vars subseteq p.vars := by
  classical simp [vars_def, Multiset.subset_of_le degrees_map_le]

variable {f}

/--
theorem `vars_map_of_injective` / 定理 `vars_map_of_injective`

English:
theorem vars_map_of_injective
  given: (hf : Injective f)
  statement: (map f p).vars = p.vars
  proof: by
  simp [vars, degrees_map_of_injective _ hf]

中文:
定理 vars_map_of_injective
  条件: (hf : 单射 f)
  结论: (map f p).vars = p.vars
  证明: by
  simp [vars, degrees_map_of_injective _ hf]

Depends on / 依赖: degrees_map_of_injective
-/
theorem vars_map_of_injective (hf : Injective f) : (map f p).vars = p.vars := by
  simp [vars, degrees_map_of_injective _ hf]

/--
theorem `vars_monomial_single` / 定理 `vars_monomial_single`

English:
theorem vars_monomial_single
  given: (i : σ) {e : Nat} {r : R} (he : e != 0) (hr : r != 0)
  proof: by
  rw [vars_monomial hr]; rw [Finsupp.support_single _ he]

中文:
定理 vars_monomial_single
  条件: (i : σ) {e : 自然数} {r : R} (he : e != 0) (hr : r != 0)
  证明: by
  rw [vars_monomial hr]; rw [Finsupp.support_single _ he]

Depends on / 依赖: Finsupp, Finsupp.support_single, support_single, vars_monomial
-/
theorem vars_monomial_single (i : σ) {e : Nat} {r : R} (he : e != 0) (hr : r != 0) :
    (monomial (Finsupp.single i e) r).vars = {i} := by
  rw [vars_monomial hr]; rw [Finsupp.support_single _ he]

/--
theorem `vars_eq_support_biUnion_support` / 定理 `vars_eq_support_biUnion_support`

English:
theorem vars_eq_support_biUnion_support
  given: [DecidableEq σ]
  proof: by
  ext i
  rw [mem_vars_iff_mem_support]; rw [Finset.mem_biUnion]

中文:
定理 vars_eq_support_biUnion_support
  条件: [DecidableEq σ]
  证明: by
  ext i
  rw [mem_vars_iff_mem_support]; rw [Finset.mem_biUnion]

Depends on / 依赖: Finset, Finset.mem_biUnion, mem_biUnion, mem_vars_iff_mem_support
-/
theorem vars_eq_support_biUnion_support [DecidableEq σ] :
    p.vars = p.support.biUnion Finsupp.support := by
  ext i
  rw [mem_vars_iff_mem_support]; rw [Finset.mem_biUnion]

end Map

end Vars

section EvalVars

/-! ### `vars` and `eval` -/


variable [CommSemiring S]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `eval₂Hom_eq_constantCoeff_of_vars` / 定理 `eval₂Hom_eq_constantCoeff_of_vars`

English:
theorem eval₂Hom_eq_constantCoeff_of_vars
  statement: (f : R ->+* S) {g : σ -> S} {p : MvPolynomial σ R}
  proof: by
  conv_lhs => rw [p.as_sum]
  simp only [map_sum, eval₂Hom_monomial]
  by_cases h0 : constantCoeff p = 0
  on_goal 1 =>
    rw [h0]; rw [f.map_zero]; rw [Finset.sum_eq_zero]
    intro d hd
  on_goal 2 =>
    rw [Finset.sum_eq_single (0 : σ ->₀ Nat)]
    · rw [Finsupp.prod_zero_index, mul_one]
   

中文:
定理 eval₂Hom_eq_constantCoeff_of_vars
  结论: (f : R ->+* S) {g : σ -> S} {p : 多元多项式 σ R}
  证明: by
  conv_lhs => rw [p.as_sum]
  simp only [map_sum, eval₂Hom_monomial]
  by_cases h0 : constantCoeff p = 0
  on_goal 1 =>
    rw [h0]; rw [f.map_zero]; rw [Finset.sum_eq_zero]
    intro d hd
  on_goal 2 =>
    rw [Finset.sum_eq_single (0 : σ ->₀ Nat)]
    · rw [Finsupp.prod_zero_index, mul_one]
   

Depends on / 依赖: Finset, Finset.Nonempty, Finset.sum_eq_single, Finset.sum_eq_zero, Finsupp, Finsupp.mem_support_iff, Finsupp.prod_zero_index, Finsupp.support, Nonempty, as_sum, constantCo, constantCoeff, constantCoeff_eq, conv_lhs, f.map_zero, map_sum, map_zero, mem_support_iff, mul_one, on_goal
-/
theorem eval₂Hom_eq_constantCoeff_of_vars (f : R ->+* S) {g : σ -> S} {p : MvPolynomial σ R}
    (hp : forall i in p.vars, g i = 0) : eval₂Hom f g p = f (constantCoeff p) := by
  conv_lhs => rw [p.as_sum]
  simp only [map_sum, eval₂Hom_monomial]
  by_cases h0 : constantCoeff p = 0
  on_goal 1 =>
    rw [h0]; rw [f.map_zero]; rw [Finset.sum_eq_zero]
    intro d hd
  on_goal 2 =>
    rw [Finset.sum_eq_single (0 : σ ->₀ Nat)]
    · rw [Finsupp.prod_zero_index, mul_one]
      rfl
    on_goal 1 => intro d hd hd0
  on_goal 3 =>
    rw [constantCoeff_eq]; rw [coeff]; rw [← Ne]; rw [← Finsupp.mem_support_iff] at h0
    intro
    contradiction
  repeat'
    obtain ⟨i, hi⟩ : Finset.Nonempty (Finsupp.support d) := by
      rw [constantCoeff_eq]; rw [coeff]; rw [← Finsupp.notMem_support_iff] at h0
      rw [Finset.nonempty_iff_ne_empty]; rw [Ne]; rw [Finsupp.support_eq_empty]
      rintro rfl
      contradiction
    rw [Finsupp.prod]; rw [Finset.prod_eq_zero hi]; rw [mul_zero]
    rw [hp]; rw [zero_pow (Finsupp.mem_support_iff.1 hi)]
    rw [mem_vars_iff_mem_support]
    exact ⟨d, hd, hi⟩

/--
theorem `aeval_eq_constantCoeff_of_vars` / 定理 `aeval_eq_constantCoeff_of_vars`

English:
theorem aeval_eq_constantCoeff_of_vars
  statement: [Algebra R S] {g : σ -> S} {p : MvPolynomial σ R}
  proof: eval₂Hom_eq_constantCoeff_of_vars _ hp

中文:
定理 aeval_eq_constantCoeff_of_vars
  结论: [代数 R S] {g : σ -> S} {p : 多元多项式 σ R}
  证明: eval₂Hom_eq_constantCoeff_of_vars _ hp
-/
theorem aeval_eq_constantCoeff_of_vars [Algebra R S] {g : σ -> S} {p : MvPolynomial σ R}
    (hp : forall i in p.vars, g i = 0) : aeval g p = algebraMap _ _ (constantCoeff p) :=
  eval₂Hom_eq_constantCoeff_of_vars _ hp

/--
theorem `eval₂Hom_congr'` / 定理 `eval₂Hom_congr'`

English:
theorem eval₂Hom_congr'
  given: {f₁ f₂ : R ->+* S} {g₁ g₂ : σ -> S} {p₁ p₂ : MvPolynomial σ R}
  proof: by
  rintro rfl h rfl
  rw [p₁.as_sum]
  simp only [map_sum, eval₂Hom_monomial]
  apply Finset.sum_congr rfl
  intro d hd
  congr 1
  simp only [Finsupp.prod]
  apply Finset.prod_congr rfl
  intro i hi
  have : i in p₁.vars := by
    rw [mem_vars_iff_mem_support]
    exact ⟨d, hd, hi⟩
  rw [h i this

中文:
定理 eval₂Hom_congr'
  条件: {f₁ f₂ : R ->+* S} {g₁ g₂ : σ -> S} {p₁ p₂ : 多元多项式 σ R}
  证明: by
  rintro rfl h rfl
  rw [p₁.as_sum]
  simp only [map_sum, eval₂Hom_monomial]
  apply Finset.sum_congr rfl
  intro d hd
  congr 1
  simp only [Finsupp.prod]
  apply Finset.prod_congr rfl
  intro i hi
  have : i in p₁.vars := by
    rw [mem_vars_iff_mem_support]
    exact ⟨d, hd, hi⟩
  rw [h i this

Depends on / 依赖: Finset, Finset.prod_congr, Finset.sum_congr, Finsupp, Finsupp.prod, as_sum, map_sum, mem_vars_iff_mem_support, prod_congr, sum_congr
-/
theorem eval₂Hom_congr' {f₁ f₂ : R ->+* S} {g₁ g₂ : σ -> S} {p₁ p₂ : MvPolynomial σ R} :
    f₁ = f₂ ->
      (forall i, i in p₁.vars -> i in p₂.vars -> g₁ i = g₂ i) ->
        p₁ = p₂ -> eval₂Hom f₁ g₁ p₁ = eval₂Hom f₂ g₂ p₂ := by
  rintro rfl h rfl
  rw [p₁.as_sum]
  simp only [map_sum, eval₂Hom_monomial]
  apply Finset.sum_congr rfl
  intro d hd
  congr 1
  simp only [Finsupp.prod]
  apply Finset.prod_congr rfl
  intro i hi
  have : i in p₁.vars := by
    rw [mem_vars_iff_mem_support]
    exact ⟨d, hd, hi⟩
  rw [h i this this]

/--
theorem `hom_congr_vars` / 定理 `hom_congr_vars`

English:
theorem hom_congr_vars
  statement: {f₁ f₂ : MvPolynomial σ R ->+* S} {p₁ p₂ : MvPolynomial σ R}
  proof: calc
    f₁ p₁ = eval₂Hom (f₁.comp C) (f₁ ∘ X) p₁ := RingHom.congr_fun (by ext <;> simp) _
    _ = eval₂Hom (f₂.comp C) (f₂ ∘ X) p₂ := eval₂Hom_congr' hC hv hp
    _ = f₂ p₂ := RingHom.congr_fun (by ext <;> simp) _

中文:
定理 hom_congr_vars
  结论: {f₁ f₂ : 多元多项式 σ R ->+* S} {p₁ p₂ : 多元多项式 σ R}
  证明: calc
    f₁ p₁ = eval₂Hom (f₁.comp C) (f₁ ∘ X) p₁ := RingHom.congr_fun (by ext <;> simp) _
    _ = eval₂Hom (f₂.comp C) (f₂ ∘ X) p₂ := eval₂Hom_congr' hC hv hp
    _ = f₂ p₂ := RingHom.congr_fun (by ext <;> simp) _

Depends on / 依赖: RingHom, RingHom.congr_fun, congr_fun
-/
theorem hom_congr_vars {f₁ f₂ : MvPolynomial σ R ->+* S} {p₁ p₂ : MvPolynomial σ R}
    (hC : f₁.comp C = f₂.comp C) (hv : forall i, i in p₁.vars -> i in p₂.vars -> f₁ (X i) = f₂ (X i))
    (hp : p₁ = p₂) : f₁ p₁ = f₂ p₂ :=
  calc
    f₁ p₁ = eval₂Hom (f₁.comp C) (f₁ ∘ X) p₁ := RingHom.congr_fun (by ext <;> simp) _
    _ = eval₂Hom (f₂.comp C) (f₂ ∘ X) p₂ := eval₂Hom_congr' hC hv hp
    _ = f₂ p₂ := RingHom.congr_fun (by ext <;> simp) _

/--
theorem `exists_rename_eq_of_vars_subset_range` / 定理 `exists_rename_eq_of_vars_subset_range`

English:
theorem exists_rename_eq_of_vars_subset_range
  statement: (p : MvPolynomial σ R) (f : τ -> σ) (hfi : Injective f)
  proof: ⟨aeval (fun i : σ => Option.elim' 0 X <| partialInv f i) p,
    by
      change (rename f).toRingHom.comp _ p = RingHom.id _ p
      refine hom_congr_vars ?_ ?_ ?_
      · ext1
        simp [algebraMap_eq]
      · intro i hip _
        rcases hf hip with ⟨i, rfl⟩
        simp [partialInv_left hfi]
 

中文:
定理 存在_rename_eq_of_vars_subset_range
  结论: (p : 多元多项式 σ R) (f : τ -> σ) (hfi : 单射 f)
  证明: ⟨aeval (fun i : σ => Option.elim' 0 X <| partialInv f i) p,
    by
      change (rename f).toRingHom.comp _ p = RingHom.id _ p
      refine hom_congr_vars ?_ ?_ ?_
      · ext1
        simp [algebraMap_eq]
      · intro i hip _
        rcases hf hip with ⟨i, rfl⟩
        simp [partialInv_left hfi]
 

Depends on / 依赖: Option.elim, RingHom, RingHom.id, algebraMap_eq, hom_congr_vars, partialInv, partialInv_left, toRingHom, toRingHom.comp
-/
theorem exists_rename_eq_of_vars_subset_range (p : MvPolynomial σ R) (f : τ -> σ) (hfi : Injective f)
    (hf : ↑p.vars subseteq Set.range f) : exists q : MvPolynomial τ R, rename f q = p :=
  ⟨aeval (fun i : σ => Option.elim' 0 X <| partialInv f i) p,
    by
      change (rename f).toRingHom.comp _ p = RingHom.id _ p
      refine hom_congr_vars ?_ ?_ ?_
      · ext1
        simp [algebraMap_eq]
      · intro i hip _
        rcases hf hip with ⟨i, rfl⟩
        simp [partialInv_left hfi]
      · rfl⟩

/--
theorem `vars_rename` / 定理 `vars_rename`

English:
theorem vars_rename
  given: [DecidableEq τ] (f : σ -> τ) (φ : MvPolynomial σ R)
  proof: by
  classical
  intro i hi
  simp only [vars_def, Multiset.mem_toFinset, Finset.mem_image] at hi ⊢
  simpa only [Multiset.mem_map] using degrees_rename _ _ hi

中文:
定理 vars_rename
  条件: [DecidableEq τ] (f : σ -> τ) (φ : 多元多项式 σ R)
  证明: by
  classical
  intro i hi
  simp only [vars_def, Multiset.mem_toFinset, Finset.mem_image] at hi ⊢
  simpa only [Multiset.mem_map] using degrees_rename _ _ hi

Depends on / 依赖: Finset, Finset.mem_image, Multiset, Multiset.mem_map, Multiset.mem_toFinset, classical, degrees_rename, mem_image, mem_map, mem_toFinset, vars_def
-/
theorem vars_rename [DecidableEq τ] (f : σ -> τ) (φ : MvPolynomial σ R) :
    (rename f φ).vars subseteq φ.vars.image f := by
  classical
  intro i hi
  simp only [vars_def, Multiset.mem_toFinset, Finset.mem_image] at hi ⊢
  simpa only [Multiset.mem_map] using degrees_rename _ _ hi

/--
theorem `mem_vars_rename` / 定理 `mem_vars_rename`

English:
theorem mem_vars_rename
  given: (f : σ -> τ) (φ : MvPolynomial σ R) {j : τ} (h : j in (rename f φ).vars)
  proof: by
  classical
  simpa only [exists_prop, Finset.mem_image] using vars_rename f φ h

中文:
定理 mem_vars_rename
  条件: (f : σ -> τ) (φ : 多元多项式 σ R) {j : τ} (h : j in (rename f φ).vars)
  证明: by
  classical
  simpa only [exists_prop, Finset.mem_image] using vars_rename f φ h

Depends on / 依赖: Finset, Finset.mem_image, classical, exists_prop, mem_image, vars_rename
-/
theorem mem_vars_rename (f : σ -> τ) (φ : MvPolynomial σ R) {j : τ} (h : j in (rename f φ).vars) :
    exists i : σ, i in φ.vars ∧ f i = j := by
  classical
  simpa only [exists_prop, Finset.mem_image] using vars_rename f φ h

/--
lemma `aeval_ite_mem_eq_self` / 引理 `aeval_ite_mem_eq_self`

English:
lemma aeval_ite_mem_eq_self
  statement: (q : MvPolynomial σ R) {s : Set σ} (hs : (q.vars : Set σ) subseteq s)
  proof: by
  rw [MvPolynomial.as_sum q]; rw [MvPolynomial.aeval_sum]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [MvPolynomial.aeval_monomial]; rw [MvPolynomial.monomial_eq]
  congr 1
  exact Finsupp.prod_congr (fun i hi => by simp [hs ((mem_vars_iff_mem_support _).mpr ⟨u, hu, hi⟩)])

中文:
引理 aeval_ite_mem_eq_self
  结论: (q : 多元多项式 σ R) {s : 集合 σ} (hs : (q.vars : 集合 σ) subseteq s)
  证明: by
  rw [MvPolynomial.as_sum q]; rw [MvPolynomial.aeval_sum]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [MvPolynomial.aeval_monomial]; rw [MvPolynomial.monomial_eq]
  congr 1
  exact Finsupp.prod_congr (fun i hi => by simp [hs ((mem_vars_iff_mem_support _).mpr ⟨u, hu, hi⟩)])

Depends on / 依赖: Finset, Finset.sum_congr, Finsupp, Finsupp.prod_congr, MvPolynomial, MvPolynomial.aeval_monomial, MvPolynomial.aeval_sum, MvPolynomial.as_sum, MvPolynomial.monomial_eq, aeval_monomial, aeval_sum, as_sum, mem_vars_iff_mem_support, monomial_eq, prod_congr, sum_congr
-/
lemma aeval_ite_mem_eq_self (q : MvPolynomial σ R) {s : Set σ} (hs : (q.vars : Set σ) subseteq s)
    [forall i, Decidable (i in s)] :
    MvPolynomial.aeval (fun i => if i in s then .X i else 0) q = q := by
  rw [MvPolynomial.as_sum q]; rw [MvPolynomial.aeval_sum]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [MvPolynomial.aeval_monomial]; rw [MvPolynomial.monomial_eq]
  congr 1
  exact Finsupp.prod_congr (fun i hi => by simp [hs ((mem_vars_iff_mem_support _).mpr ⟨u, hu, hi⟩)])

end EvalVars

section Lex

variable [LinearOrder σ]

/--
lemma `leadingCoeff_toLex` / 引理 `leadingCoeff_toLex`

English:
lemma leadingCoeff_toLex
  statement: p.leadingCoeff toLex = p.coeff (ofLex <| p.supDegree toLex)
  proof: by
  rw [leadingCoeff]
  apply congr_arg p.coeff
  apply toLex.injective
  rw [Function.rightInverse_invFun toLex.surjective]; rw [toLex_ofLex]

中文:
引理 leadingCoeff_toLex
  结论: p.leadingCoeff toLex = p.coeff (ofLex <| p.supDegree toLex)
  证明: by
  rw [leadingCoeff]
  apply congr_arg p.coeff
  apply toLex.injective
  rw [Function.rightInverse_invFun toLex.surjective]; rw [toLex_ofLex]

Depends on / 依赖: Function, Function.rightInverse_invFun, congr_arg, injective, leadingCoeff, p.coeff, rightInverse_invFun, surjective, toLex.injective, toLex.surjective, toLex_ofLex
-/
lemma leadingCoeff_toLex : p.leadingCoeff toLex = p.coeff (ofLex <| p.supDegree toLex) := by
  rw [leadingCoeff]
  apply congr_arg p.coeff
  apply toLex.injective
  rw [Function.rightInverse_invFun toLex.surjective]; rw [toLex_ofLex]

/--
lemma `supDegree_toLex_C` / 引理 `supDegree_toLex_C`

English:
lemma supDegree_toLex_C
  given: (r : R)
  statement: supDegree toLex (C (σ := σ) r) = 0
  proof: by
  classical
    exact (supDegree_single _ r).trans (ite_eq_iff'.mpr ⟨fun _ => rfl, fun _ => rfl⟩)

中文:
引理 supDegree_toLex_C
  条件: (r : R)
  结论: supDegree toLex (C (σ := σ) r) = 0
  证明: by
  classical
    exact (supDegree_single _ r).trans (ite_eq_iff'.mpr ⟨fun _ => rfl, fun _ => rfl⟩)

Depends on / 依赖: classical, ite_eq_iff, supDegree_single
-/
lemma supDegree_toLex_C (r : R) : supDegree toLex (C (σ := σ) r) = 0 := by
  classical
    exact (supDegree_single _ r).trans (ite_eq_iff'.mpr ⟨fun _ => rfl, fun _ => rfl⟩)

/--
lemma `leadingCoeff_toLex_C` / 引理 `leadingCoeff_toLex_C`

English:
lemma leadingCoeff_toLex_C
  given: (r : R)
  statement: leadingCoeff toLex (C (σ := σ) r) = r
  proof: leadingCoeff_single toLex.injective _ r

中文:
引理 leadingCoeff_toLex_C
  条件: (r : R)
  结论: leadingCoeff toLex (C (σ := σ) r) = r
  证明: leadingCoeff_single toLex.injective _ r
-/
lemma leadingCoeff_toLex_C (r : R) : leadingCoeff toLex (C (σ := σ) r) = r :=
  leadingCoeff_single toLex.injective _ r

end Lex

end CommSemiring

end MvPolynomial
