/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Johan Commelin, Mario Carneiro
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Degree
public import Mathlib.Algebra.MvPolynomial.Rename

/-!
# Degrees of polynomials

This file establishes many results about the degree of a multivariate polynomial.

The *degree set* of a polynomial $P \in R[X]$ is a `Multiset` containing, for each $x$ in the
variable set, $n$ copies of $x$, where $n$ is the maximum number of copies of $x$ appearing in a
monomial of $P$.

## Main declarations

* `MvPolynomial.degrees p` : the multiset of variables representing the union of the multisets
  corresponding to each non-zero monomial in `p`.
  For example if `7 ≠ 0` in `R` and `p = x²y+7y³` then `degrees p = {x, x, y, y, y}`

* `MvPolynomial.degreeOf n p : ℕ` : the total degree of `p` with respect to the variable `n`.
  For example if `p = x⁴y+yz` then `degreeOf y p = 1`.

* `MvPolynomial.totalDegree p : ℕ` :
  the max of the sizes of the multisets `s` whose monomials `X^s` occur in `p`.
  For example if `p = x⁴y+yz` then `totalDegree p = 5`.

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

section Degrees

/-! ### `degrees` -/


/--
Definition of `degrees` / `degrees` 的定义

English:
definition degrees
  signature: (p : MvPolynomial σ R)
  body: letI := Classical.decEq σ
  p.support.sup fun s : σ ->₀ Nat => toMultiset s

中文:
定义 degrees
  签名: (p : 多元多项式 σ R)
  定义体: letI := Classical.decEq σ
  p.support.sup fun s : σ ->₀ Nat => toMultiset s

Depends on / 依赖: Classical, Classical.decEq, p.support.sup, support, toMultiset
-/
def degrees (p : MvPolynomial σ R) : Multiset σ :=
  letI := Classical.decEq σ
  p.support.sup fun s : σ ->₀ Nat => toMultiset s

/--
theorem `degrees_def` / 定理 `degrees_def`

English:
theorem degrees_def
  given: [DecidableEq σ] (p : MvPolynomial σ R)
  proof: by rw [degrees]; convert!
      rfl

中文:
定理 degrees_def
  条件: [DecidableEq σ] (p : 多元多项式 σ R)
  证明: by rw [degrees]; convert!
      rfl

Depends on / 依赖: convert, degrees
-/
theorem degrees_def [DecidableEq σ] (p : MvPolynomial σ R) :
    p.degrees = p.support.sup fun s : σ ->₀ Nat => Finsupp.toMultiset s := by rw [degrees]; convert!
      rfl

/--
theorem `degrees_monomial` / 定理 `degrees_monomial`

English:
theorem degrees_monomial
  given: (s : σ ->₀ Nat) (a : R)
  statement: degrees (monomial s a) <= toMultiset s
  proof: by
  classical
    refine (supDegree_single s a).trans_le ?_
    split_ifs
    exacts [bot_le, le_rfl]

中文:
定理 degrees_monomial
  条件: (s : σ ->₀ 自然数) (a : R)
  结论: degrees (monomial s a) <= toMultiset s
  证明: by
  classical
    refine (supDegree_single s a).trans_le ?_
    split_ifs
    exacts [bot_le, le_rfl]

Depends on / 依赖: bot_le, classical, exacts, le_rfl, split_ifs, supDegree_single, trans_le
-/
theorem degrees_monomial (s : σ ->₀ Nat) (a : R) : degrees (monomial s a) <= toMultiset s := by
  classical
    refine (supDegree_single s a).trans_le ?_
    split_ifs
    exacts [bot_le, le_rfl]

/--
theorem `degrees_monomial_eq` / 定理 `degrees_monomial_eq`

English:
theorem degrees_monomial_eq
  given: (s : σ ->₀ Nat) (a : R) (ha : a != 0)
  proof: by
  classical
    exact (supDegree_single s a).trans (if_neg ha)

中文:
定理 degrees_monomial_eq
  条件: (s : σ ->₀ 自然数) (a : R) (ha : a != 0)
  证明: by
  classical
    exact (supDegree_single s a).trans (if_neg ha)

Depends on / 依赖: classical, if_neg, supDegree_single
-/
theorem degrees_monomial_eq (s : σ ->₀ Nat) (a : R) (ha : a != 0) :
    degrees (monomial s a) = toMultiset s := by
  classical
    exact (supDegree_single s a).trans (if_neg ha)

/--
theorem `degrees_C` / 定理 `degrees_C`

English:
theorem degrees_C
  given: (a : R)
  statement: degrees (C a : MvPolynomial σ R) = 0
  proof: Multiset.le_zero.1 degrees_monomial _ _

中文:
定理 degrees_C
  条件: (a : R)
  结论: degrees (C a : 多元多项式 σ R) = 0
  证明: Multiset.le_zero.1 degrees_monomial _ _

Depends on / 依赖: Multiset, Multiset.le_zero, degrees_monomial, le_zero
-/
theorem degrees_C (a : R) : degrees (C a : MvPolynomial σ R) = 0 :=
Multiset.le_zero.1 degrees_monomial _ _

/--
theorem `degrees_X'` / 定理 `degrees_X'`

English:
theorem degrees_X'
  given: (n : σ)
  statement: degrees (X n : MvPolynomial σ R) <= {n}
  proof: le_trans (degrees_monomial _ _) le_of_eq toMultiset_single _ _

@[simp]

中文:
定理 degrees_X'
  条件: (n : σ)
  结论: degrees (X n : 多元多项式 σ R) <= {n}
  证明: le_trans (degrees_monomial _ _) le_of_eq toMultiset_single _ _

@[simp]

Depends on / 依赖: degrees_monomial, le_of_eq, le_trans, toMultiset_single
-/
theorem degrees_X' (n : σ) : degrees (X n : MvPolynomial σ R) <= {n} :=
le_trans (degrees_monomial _ _) le_of_eq toMultiset_single _ _

@[simp]
/--
theorem `degrees_X` / 定理 `degrees_X`

English:
theorem degrees_X
  given: [Nontrivial R] (n : σ)
  statement: degrees (X n : MvPolynomial σ R) = {n}
  proof: (degrees_monomial_eq _ (1 : R) one_ne_zero).trans (toMultiset_single _ _)

@[simp]

中文:
定理 degrees_X
  条件: [非平凡 R] (n : σ)
  结论: degrees (X n : 多元多项式 σ R) = {n}
  证明: (degrees_monomial_eq _ (1 : R) one_ne_zero).trans (toMultiset_single _ _)

@[simp]

Depends on / 依赖: degrees_monomial_eq, one_ne_zero, toMultiset_single
-/
theorem degrees_X [Nontrivial R] (n : σ) : degrees (X n : MvPolynomial σ R) = {n} :=
  (degrees_monomial_eq _ (1 : R) one_ne_zero).trans (toMultiset_single _ _)

@[simp]
/--
theorem `degrees_zero` / 定理 `degrees_zero`

English:
theorem degrees_zero
  statement: degrees (0 : MvPolynomial σ R) = 0
  proof: by
  rw [← C_0]
  exact degrees_C 0

@[simp]

中文:
定理 degrees_zero
  结论: degrees (0 : 多元多项式 σ R) = 0
  证明: by
  rw [← C_0]
  exact degrees_C 0

@[simp]

Depends on / 依赖: degrees_C
-/
theorem degrees_zero : degrees (0 : MvPolynomial σ R) = 0 := by
  rw [← C_0]
  exact degrees_C 0

@[simp]
/--
theorem `degrees_one` / 定理 `degrees_one`

English:
theorem degrees_one
  statement: degrees (1 : MvPolynomial σ R) = 0
  proof: degrees_C 1

中文:
定理 degrees_one
  结论: degrees (1 : 多元多项式 σ R) = 0
  证明: degrees_C 1

Depends on / 依赖: degrees_C
-/
theorem degrees_one : degrees (1 : MvPolynomial σ R) = 0 :=
  degrees_C 1

/--
theorem `degrees_add_le` / 定理 `degrees_add_le`

English:
theorem degrees_add_le
  given: [DecidableEq σ] {p q : MvPolynomial σ R}
  proof: by
  simp_rw [degrees_def]; exact supDegree_add_le

中文:
定理 degrees_add_le
  条件: [DecidableEq σ] {p q : 多元多项式 σ R}
  证明: by
  simp_rw [degrees_def]; exact supDegree_add_le

Depends on / 依赖: degrees_def, simp_rw, supDegree_add_le
-/
theorem degrees_add_le [DecidableEq σ] {p q : MvPolynomial σ R} :
    (p + q).degrees <= p.degrees ⊔ q.degrees := by
  simp_rw [degrees_def]; exact supDegree_add_le

/--
theorem `degrees_sum_le` / 定理 `degrees_sum_le`

English:
theorem degrees_sum_le
  given: {ι : Type*} [DecidableEq σ] (s : Finset ι) (f : ι -> MvPolynomial σ R)
  proof: by
  simp_rw [degrees_def]; exact supDegree_sum_le

中文:
定理 degrees_sum_le
  条件: {ι : 类型} [DecidableEq σ] (s : 有限集 ι) (f : ι -> 多元多项式 σ R)
  证明: by
  simp_rw [degrees_def]; exact supDegree_sum_le

Depends on / 依赖: degrees_def, simp_rw, supDegree_sum_le
-/
theorem degrees_sum_le {ι : Type*} [DecidableEq σ] (s : Finset ι) (f : ι -> MvPolynomial σ R) :
    (∑ i in s, f i).degrees <= s.sup fun i => (f i).degrees := by
  simp_rw [degrees_def]; exact supDegree_sum_le

/--
theorem `degrees_mul_le` / 定理 `degrees_mul_le`

English:
theorem degrees_mul_le
  given: {p q : MvPolynomial σ R}
  statement: (p * q).degrees <= p.degrees + q.degrees
  proof: by
  classical
  simp_rw [degrees_def]
  exact supDegree_mul_le (map_add _)

中文:
定理 degrees_mul_le
  条件: {p q : 多元多项式 σ R}
  结论: (p * q).degrees <= p.degrees + q.degrees
  证明: by
  classical
  simp_rw [degrees_def]
  exact supDegree_mul_le (map_add _)

Depends on / 依赖: classical, degrees_def, map_add, simp_rw, supDegree_mul_le
-/
theorem degrees_mul_le {p q : MvPolynomial σ R} : (p * q).degrees <= p.degrees + q.degrees := by
  classical
  simp_rw [degrees_def]
  exact supDegree_mul_le (map_add _)

/--
theorem `degrees_prod_le` / 定理 `degrees_prod_le`

English:
theorem degrees_prod_le
  given: {ι : Type*} {s : Finset ι} {f : ι -> MvPolynomial σ R}
  proof: by
  classical exact supDegree_prod_le (map_zero _) (map_add _)

中文:
定理 degrees_prod_le
  条件: {ι : 类型} {s : 有限集 ι} {f : ι -> 多元多项式 σ R}
  证明: by
  classical exact supDegree_prod_le (map_zero _) (map_add _)

Depends on / 依赖: classical, map_add, map_zero, supDegree_prod_le
-/
theorem degrees_prod_le {ι : Type*} {s : Finset ι} {f : ι -> MvPolynomial σ R} :
    (∏ i in s, f i).degrees <= ∑ i in s, (f i).degrees := by
  classical exact supDegree_prod_le (map_zero _) (map_add _)

/--
theorem `degrees_pow_le` / 定理 `degrees_pow_le`

English:
theorem degrees_pow_le
  given: {p : MvPolynomial σ R} {n : Nat}
  statement: (p ^ n).degrees <= n • p.degrees
  proof: by
  simpa using degrees_prod_le (s := .range n) (f := fun _ => p)

中文:
定理 degrees_pow_le
  条件: {p : 多元多项式 σ R} {n : 自然数}
  结论: (p ^ n).degrees <= n • p.degrees
  证明: by
  simpa using degrees_prod_le (s := .range n) (f := fun _ => p)

Depends on / 依赖: degrees_prod_le
-/
theorem degrees_pow_le {p : MvPolynomial σ R} {n : Nat} : (p ^ n).degrees <= n • p.degrees := by
  simpa using degrees_prod_le (s := .range n) (f := fun _ => p)

/--
theorem `mem_degrees` / 定理 `mem_degrees`

English:
theorem mem_degrees
  given: {p : MvPolynomial σ R} {i : σ}
  proof: by
  classical
  simp only [degrees_def, Multiset.mem_sup, ← mem_support_iff, Finsupp.mem_toMultiset]

中文:
定理 mem_degrees
  条件: {p : 多元多项式 σ R} {i : σ}
  证明: by
  classical
  simp only [degrees_def, Multiset.mem_sup, ← mem_support_iff, Finsupp.mem_toMultiset]

Depends on / 依赖: Finsupp, Finsupp.mem_toMultiset, Multiset, Multiset.mem_sup, classical, degrees_def, mem_sup, mem_support_iff, mem_toMultiset
-/
theorem mem_degrees {p : MvPolynomial σ R} {i : σ} :
    i in p.degrees ↔ exists d, p.coeff d != 0 ∧ i in d.support := by
  classical
  simp only [degrees_def, Multiset.mem_sup, ← mem_support_iff, Finsupp.mem_toMultiset]

/--
theorem `degrees_eq_zero_iff_support_subset_zero` / 定理 `degrees_eq_zero_iff_support_subset_zero`

English:
theorem degrees_eq_zero_iff_support_subset_zero
  statement: p.degrees = 0 ↔ p.support subseteq {0}
  proof: by
  rw [Finset.subset_singleton_iff']; rw [Multiset.eq_zero_iff_forall_notMem]
  refine ⟨fun h s hs => ?_, fun h i hi => ?_⟩
  · rw [← Finsupp.support_eq_empty]
    simp only [mem_degrees] at h
    grind
  rcases mem_degrees.mp hi with ⟨s, hs1, hs2⟩
  have := Finsupp.support_eq_empty.mpr (h s <| mem_support_iff.mpr hs1) ▸ hs2
  grind

中文:
定理 degrees_eq_zero_iff_support_subset_zero
  结论: p.degrees = 0 ↔ p.support subseteq {0}
  证明: by
  rw [Finset.subset_singleton_iff']; rw [Multiset.eq_zero_iff_forall_notMem]
  refine ⟨fun h s hs => ?_, fun h i hi => ?_⟩
  · rw [← Finsupp.support_eq_empty]
    simp only [mem_degrees] at h
    grind
  rcases mem_degrees.mp hi with ⟨s, hs1, hs2⟩
  have := Finsupp.support_eq_empty.mpr (h s <| mem_support_iff.mpr hs1) ▸ hs2
  grind

Depends on / 依赖: Finset, Finset.subset_singleton_iff, Finsupp, Finsupp.support_eq_empty, Finsupp.support_eq_empty.mpr, Multiset, Multiset.eq_zero_iff_forall_notMem, eq_zero_iff_forall_notMem, mem_degrees, mem_degrees.mp, mem_support_iff, mem_support_iff.mpr, subset_singleton_iff, support_eq_empty
-/
theorem degrees_eq_zero_iff_support_subset_zero : p.degrees = 0 ↔ p.support subseteq {0} := by
  rw [Finset.subset_singleton_iff']; rw [Multiset.eq_zero_iff_forall_notMem]
  refine ⟨fun h s hs => ?_, fun h i hi => ?_⟩
  · rw [← Finsupp.support_eq_empty]
    simp only [mem_degrees] at h
    grind
  rcases mem_degrees.mp hi with ⟨s, hs1, hs2⟩
  have := Finsupp.support_eq_empty.mpr (h s <| mem_support_iff.mpr hs1) ▸ hs2
  grind

set_option backward.isDefEq.respectTransparency false in
/--
theorem `le_degrees_add_left` / 定理 `le_degrees_add_left`

English:
theorem le_degrees_add_left
  given: (h : Disjoint p.degrees q.degrees)
  statement: p.degrees <= (p + q).degrees
  proof: by
  classical
  apply Finset.sup_le
  intro d hd
  rw [Multiset.disjoint_iff_ne] at h
  obtain rfl | h0 := eq_or_ne d 0
  · rw [toMultiset_zero]; apply Multiset.zero_le
  · refine Finset.le_sup_of_le (b := d) ?_ le_rfl
    rw [mem_support_iff]; rw [coeff_add]
    suffices q.coeff d = 0 by rwa [this, add_zero, coeff, ← Finsupp.mem_support_iff]
    rw [Ne]; rw [← Finsupp.support_eq_empty]; rw [← Ne]; rw [← Finset.nonempty_iff_ne_empty] at h0
    obtain ⟨j, hj⟩ := h0
    contrapose! h
    rw [mem_support_iff] at hd
    refine ⟨j, ?_, j, ?_, rfl⟩
    all_goals rw [mem_degrees]; refine ⟨d, ?_, hj⟩; assumption

中文:
定理 le_degrees_add_left
  条件: (h : Disjoint p.degrees q.degrees)
  结论: p.degrees <= (p + q).degrees
  证明: by
  classical
  apply Finset.sup_le
  intro d hd
  rw [Multiset.disjoint_iff_ne] at h
  obtain rfl | h0 := eq_or_ne d 0
  · rw [toMultiset_zero]; apply Multiset.zero_le
  · refine Finset.le_sup_of_le (b := d) ?_ le_rfl
    rw [mem_support_iff]; rw [coeff_add]
    suffices q.coeff d = 0 by rwa [this, add_zero, coeff, ← Finsupp.mem_support_iff]
    rw [Ne]; rw [← Finsupp.support_eq_empty]; rw [← Ne]; rw [← Finset.nonempty_iff_ne_empty] at h0
    obtain ⟨j, hj⟩ := h0
    contrapose! h
    rw [mem_support_iff] at hd
    refine ⟨j, ?_, j, ?_, rfl⟩
    all_goals rw [mem_degrees]; refine ⟨d, ?_, hj⟩; assumption

Depends on / 依赖: Finset, Finset.le_sup_of_le, Finset.nonempty_iff_ne_empty, Finset.sup_le, Finsupp, Finsupp.mem_support_iff, Finsupp.support_eq_empty, Multiset, Multiset.disjoint_iff_ne, Multiset.zero_le, add_zero, classical, coeff_add, contrapose, disjoint_iff_ne, eq_or_ne, le_rfl, le_sup_of_le, mem_support_iff, nonempty_iff_ne_empty
-/
theorem le_degrees_add_left (h : Disjoint p.degrees q.degrees) : p.degrees <= (p + q).degrees := by
  classical
  apply Finset.sup_le
  intro d hd
  rw [Multiset.disjoint_iff_ne] at h
  obtain rfl | h0 := eq_or_ne d 0
  · rw [toMultiset_zero]; apply Multiset.zero_le
  · refine Finset.le_sup_of_le (b := d) ?_ le_rfl
    rw [mem_support_iff]; rw [coeff_add]
    suffices q.coeff d = 0 by rwa [this, add_zero, coeff, ← Finsupp.mem_support_iff]
    rw [Ne]; rw [← Finsupp.support_eq_empty]; rw [← Ne]; rw [← Finset.nonempty_iff_ne_empty] at h0
    obtain ⟨j, hj⟩ := h0
    contrapose! h
    rw [mem_support_iff] at hd
    refine ⟨j, ?_, j, ?_, rfl⟩
    all_goals rw [mem_degrees]; refine ⟨d, ?_, hj⟩; assumption

/--
lemma `le_degrees_add_right` / 引理 `le_degrees_add_right`

English:
lemma le_degrees_add_right
  given: (h : Disjoint p.degrees q.degrees)
  statement: q.degrees <= (p + q).degrees
  proof: by
  simpa [add_comm] using le_degrees_add_left h.symm

中文:
引理 le_degrees_add_right
  条件: (h : Disjoint p.degrees q.degrees)
  结论: q.degrees <= (p + q).degrees
  证明: by
  simpa [add_comm] using le_degrees_add_left h.symm

Depends on / 依赖: add_comm, h.symm, le_degrees_add_left
-/
lemma le_degrees_add_right (h : Disjoint p.degrees q.degrees) : q.degrees <= (p + q).degrees := by
  simpa [add_comm] using le_degrees_add_left h.symm

/--
theorem `degrees_add_of_disjoint` / 定理 `degrees_add_of_disjoint`

English:
theorem degrees_add_of_disjoint
  given: [DecidableEq σ] (h : Disjoint p.degrees q.degrees)
  proof: degrees_add_le.antisymm Multiset.union_le (le_degrees_add_left h) (le_degrees_add_right h)

中文:
定理 degrees_add_of_disjoint
  条件: [DecidableEq σ] (h : Disjoint p.degrees q.degrees)
  证明: degrees_add_le.antisymm Multiset.union_le (le_degrees_add_left h) (le_degrees_add_right h)

Depends on / 依赖: Multiset, Multiset.union_le, antisymm, degrees_add_le, degrees_add_le.antisymm, le_degrees_add_left, le_degrees_add_right, union_le
-/
theorem degrees_add_of_disjoint [DecidableEq σ] (h : Disjoint p.degrees q.degrees) :
    (p + q).degrees = p.degrees union q.degrees :=
degrees_add_le.antisymm Multiset.union_le (le_degrees_add_left h) (le_degrees_add_right h)

/--
lemma `degrees_map_le` / 引理 `degrees_map_le`

English:
lemma degrees_map_le
  given: [CommSemiring S] {f : R ->+* S}
  statement: (map f p).degrees <= p.degrees
  proof: by
classical exact Finset.sup_mono support_map_subset ..

中文:
引理 degrees_map_le
  条件: [交换半环 S] {f : R ->+* S}
  结论: (map f p).degrees <= p.degrees
  证明: by
classical exact Finset.sup_mono support_map_subset ..

Depends on / 依赖: Finset, Finset.sup_mono, classical, sup_mono, support_map_subset
-/
lemma degrees_map_le [CommSemiring S] {f : R ->+* S} : (map f p).degrees <= p.degrees := by
classical exact Finset.sup_mono support_map_subset ..

/--
theorem `degrees_rename` / 定理 `degrees_rename`

English:
theorem degrees_rename
  given: (f : σ -> τ) (φ : MvPolynomial σ R)
  proof: by
  classical
  intro i
  rw [mem_degrees]; rw [Multiset.mem_map]
  rintro ⟨d, hd, hi⟩
  obtain ⟨x, rfl, hx⟩ := coeff_rename_ne_zero _ _ _ hd
  simp only [Finsupp.mapDomain, Finsupp.mem_support_iff] at hi
  rw [sum_apply]; rw [Finsupp.sum] at hi
  contrapose! hi
  rw [Finset.sum_eq_zero]
  intro j hj
  simp only [mem_degrees] at hi
  specialize hi j ⟨x, hx, hj⟩
  rw [Finsupp.single_apply]; rw [if_neg hi]

中文:
定理 degrees_rename
  条件: (f : σ -> τ) (φ : 多元多项式 σ R)
  证明: by
  classical
  intro i
  rw [mem_degrees]; rw [Multiset.mem_map]
  rintro ⟨d, hd, hi⟩
  obtain ⟨x, rfl, hx⟩ := coeff_rename_ne_zero _ _ _ hd
  simp only [Finsupp.mapDomain, Finsupp.mem_support_iff] at hi
  rw [sum_apply]; rw [Finsupp.sum] at hi
  contrapose! hi
  rw [Finset.sum_eq_zero]
  intro j hj
  simp only [mem_degrees] at hi
  specialize hi j ⟨x, hx, hj⟩
  rw [Finsupp.single_apply]; rw [if_neg hi]

Depends on / 依赖: Finset, Finset.sum_eq_zero, Finsupp, Finsupp.mapDomain, Finsupp.mem_support_iff, Finsupp.single_apply, Finsupp.sum, Multiset, Multiset.mem_map, classical, coeff_rename_ne_zero, contrapose, if_neg, mapDomain, mem_degrees, mem_map, mem_support_iff, single_apply, specialize, sum_apply
-/
theorem degrees_rename (f : σ -> τ) (φ : MvPolynomial σ R) :
    (rename f φ).degrees subseteq φ.degrees.map f := by
  classical
  intro i
  rw [mem_degrees]; rw [Multiset.mem_map]
  rintro ⟨d, hd, hi⟩
  obtain ⟨x, rfl, hx⟩ := coeff_rename_ne_zero _ _ _ hd
  simp only [Finsupp.mapDomain, Finsupp.mem_support_iff] at hi
  rw [sum_apply]; rw [Finsupp.sum] at hi
  contrapose! hi
  rw [Finset.sum_eq_zero]
  intro j hj
  simp only [mem_degrees] at hi
  specialize hi j ⟨x, hx, hj⟩
  rw [Finsupp.single_apply]; rw [if_neg hi]

/--
theorem `degrees_map_of_injective` / 定理 `degrees_map_of_injective`

English:
theorem degrees_map_of_injective
  statement: [CommSemiring S] (p : MvPolynomial σ R) {f : R ->+* S}
  proof: by
  simp only [degrees, MvPolynomial.support_map_of_injective _ hf]

中文:
定理 degrees_map_of_injective
  结论: [交换半环 S] (p : 多元多项式 σ R) {f : R ->+* S}
  证明: by
  simp only [degrees, MvPolynomial.support_map_of_injective _ hf]

Depends on / 依赖: MvPolynomial, MvPolynomial.support_map_of_injective, degrees, support_map_of_injective
-/
theorem degrees_map_of_injective [CommSemiring S] (p : MvPolynomial σ R) {f : R ->+* S}
    (hf : Injective f) : (map f p).degrees = p.degrees := by
  simp only [degrees, MvPolynomial.support_map_of_injective _ hf]

/--
theorem `degrees_rename_of_injective` / 定理 `degrees_rename_of_injective`

English:
theorem degrees_rename_of_injective
  given: {p : MvPolynomial σ R} {f : σ -> τ} (h : Function.Injective f)
  proof: by
  classical
  simp only [degrees, Multiset.map_finset_sup p.support Finsupp.toMultiset f h,
    support_rename_of_injective h, Finset.sup_image]
  refine Finset.sup_congr rfl fun x _ => ?_
  exact (Finsupp.toMultiset_map _ _).symm

中文:
定理 degrees_rename_of_injective
  条件: {p : 多元多项式 σ R} {f : σ -> τ} (h : 函数.单射 f)
  证明: by
  classical
  simp only [degrees, Multiset.map_finset_sup p.support Finsupp.toMultiset f h,
    support_rename_of_injective h, Finset.sup_image]
  refine Finset.sup_congr rfl fun x _ => ?_
  exact (Finsupp.toMultiset_map _ _).symm

Depends on / 依赖: Finset, Finset.sup_congr, Finset.sup_image, Finsupp, Finsupp.toMultiset, Finsupp.toMultiset_map, Multiset, Multiset.map_finset_sup, classical, degrees, map_finset_sup, p.support, sup_congr, sup_image, support, support_rename_of_injective, toMultiset, toMultiset_map
-/
theorem degrees_rename_of_injective {p : MvPolynomial σ R} {f : σ -> τ} (h : Function.Injective f) :
    degrees (rename f p) = (degrees p).map f := by
  classical
  simp only [degrees, Multiset.map_finset_sup p.support Finsupp.toMultiset f h,
    support_rename_of_injective h, Finset.sup_image]
  refine Finset.sup_congr rfl fun x _ => ?_
  exact (Finsupp.toMultiset_map _ _).symm

end Degrees

section DegreeOf

/-! ### `degreeOf` -/


/--
Definition of `degreeOf` / `degreeOf` 的定义

English:
definition degreeOf
  signature: (n : σ) (p : MvPolynomial σ R)
  body: letI := Classical.decEq σ
  p.degrees.count n

中文:
定义 degreeOf
  签名: (n : σ) (p : 多元多项式 σ R)
  定义体: letI := Classical.decEq σ
  p.degrees.count n

Depends on / 依赖: Classical, Classical.decEq, degrees, p.degrees.count
-/
def degreeOf (n : σ) (p : MvPolynomial σ R) : Nat :=
  letI := Classical.decEq σ
  p.degrees.count n

/--
theorem `degreeOf_def` / 定理 `degreeOf_def`

English:
theorem degreeOf_def
  given: [DecidableEq σ] (n : σ) (p : MvPolynomial σ R)
  proof: by rw [degreeOf]; convert! rfl

中文:
定理 degreeOf_def
  条件: [DecidableEq σ] (n : σ) (p : 多元多项式 σ R)
  证明: by rw [degreeOf]; convert! rfl

Depends on / 依赖: convert, degreeOf
-/
theorem degreeOf_def [DecidableEq σ] (n : σ) (p : MvPolynomial σ R) :
    p.degreeOf n = p.degrees.count n := by rw [degreeOf]; convert! rfl

/--
theorem `degreeOf_eq_sup` / 定理 `degreeOf_eq_sup`

English:
theorem degreeOf_eq_sup
  given: (n : σ) (f : MvPolynomial σ R)
  proof: by
  classical
  rw [degreeOf_def]; rw [degrees]; rw [Multiset.count_finset_sup]
  congr
  ext
  simp only [count_toMultiset]

中文:
定理 degreeOf_eq_sup
  条件: (n : σ) (f : 多元多项式 σ R)
  证明: by
  classical
  rw [degreeOf_def]; rw [degrees]; rw [Multiset.count_finset_sup]
  congr
  ext
  simp only [count_toMultiset]

Depends on / 依赖: Multiset, Multiset.count_finset_sup, classical, count_finset_sup, count_toMultiset, degreeOf_def, degrees
-/
theorem degreeOf_eq_sup (n : σ) (f : MvPolynomial σ R) :
    degreeOf n f = f.support.sup fun m => m n := by
  classical
  rw [degreeOf_def]; rw [degrees]; rw [Multiset.count_finset_sup]
  congr
  ext
  simp only [count_toMultiset]

/--
theorem `degreeOf_lt_iff` / 定理 `degreeOf_lt_iff`

English:
theorem degreeOf_lt_iff
  given: {n : σ} {f : MvPolynomial σ R} {d : Nat} (h : 0 < d)
  proof: by
  rwa [degreeOf_eq_sup, Finset.sup_lt_iff]

中文:
定理 degreeOf_lt_iff
  条件: {n : σ} {f : 多元多项式 σ R} {d : 自然数} (h : 0 < d)
  证明: by
  rwa [degreeOf_eq_sup, Finset.sup_lt_iff]

Depends on / 依赖: Finset, Finset.sup_lt_iff, degreeOf_eq_sup, sup_lt_iff
-/
theorem degreeOf_lt_iff {n : σ} {f : MvPolynomial σ R} {d : Nat} (h : 0 < d) :
    degreeOf n f < d ↔ forall m : σ ->₀ Nat, m in f.support -> m n < d := by
  rwa [degreeOf_eq_sup, Finset.sup_lt_iff]

/--
lemma `degreeOf_le_iff` / 引理 `degreeOf_le_iff`

English:
lemma degreeOf_le_iff
  given: {n : σ} {f : MvPolynomial σ R} {d : Nat}
  proof: by
  rw [degreeOf_eq_sup]; rw [Finset.sup_le_iff]

@[simp]

中文:
引理 degreeOf_le_iff
  条件: {n : σ} {f : 多元多项式 σ R} {d : 自然数}
  证明: by
  rw [degreeOf_eq_sup]; rw [Finset.sup_le_iff]

@[simp]

Depends on / 依赖: Finset, Finset.sup_le_iff, degreeOf_eq_sup, sup_le_iff
-/
lemma degreeOf_le_iff {n : σ} {f : MvPolynomial σ R} {d : Nat} :
    degreeOf n f <= d ↔ forall m in support f, m n <= d := by
  rw [degreeOf_eq_sup]; rw [Finset.sup_le_iff]

@[simp]
/--
theorem `degreeOf_zero` / 定理 `degreeOf_zero`

English:
theorem degreeOf_zero
  given: (n : σ)
  statement: degreeOf n (0 : MvPolynomial σ R) = 0
  proof: by
  classical simp only [degreeOf_def, degrees_zero, Multiset.count_zero]

@[simp]

中文:
定理 degreeOf_zero
  条件: (n : σ)
  结论: degreeOf n (0 : 多元多项式 σ R) = 0
  证明: by
  classical simp only [degreeOf_def, degrees_zero, Multiset.count_zero]

@[simp]

Depends on / 依赖: Multiset, Multiset.count_zero, classical, count_zero, degreeOf_def, degrees_zero
-/
theorem degreeOf_zero (n : σ) : degreeOf n (0 : MvPolynomial σ R) = 0 := by
  classical simp only [degreeOf_def, degrees_zero, Multiset.count_zero]

@[simp]
/--
theorem `degreeOf_one` / 定理 `degreeOf_one`

English:
theorem degreeOf_one
  given: (n : σ)
  statement: degreeOf n (1 : MvPolynomial σ R) = 0
  proof: by
  classical simp [degreeOf_def, degrees_one]

@[simp]

中文:
定理 degreeOf_one
  条件: (n : σ)
  结论: degreeOf n (1 : 多元多项式 σ R) = 0
  证明: by
  classical simp [degreeOf_def, degrees_one]

@[simp]

Depends on / 依赖: classical, degreeOf_def, degrees_one
-/
theorem degreeOf_one (n : σ) : degreeOf n (1 : MvPolynomial σ R) = 0 := by
  classical simp [degreeOf_def, degrees_one]

@[simp]
/--
theorem `degreeOf_C` / 定理 `degreeOf_C`

English:
theorem degreeOf_C
  given: (a : R) (x : σ)
  statement: degreeOf x (C a : MvPolynomial σ R) = 0
  proof: by
  classical simp [degreeOf_def, degrees_C]

中文:
定理 degreeOf_C
  条件: (a : R) (x : σ)
  结论: degreeOf x (C a : 多元多项式 σ R) = 0
  证明: by
  classical simp [degreeOf_def, degrees_C]

Depends on / 依赖: classical, degreeOf_def, degrees_C
-/
theorem degreeOf_C (a : R) (x : σ) : degreeOf x (C a : MvPolynomial σ R) = 0 := by
  classical simp [degreeOf_def, degrees_C]

/--
theorem `degreeOf_X` / 定理 `degreeOf_X`

English:
theorem degreeOf_X
  given: [DecidableEq σ] (i j : σ) [Nontrivial R]
  proof: by
  by_cases c : i = j
  · simp only [c, if_true, degreeOf_def, degrees_X, Multiset.count_singleton]
  simp [c, degreeOf_def, degrees_X]

中文:
定理 degreeOf_X
  条件: [DecidableEq σ] (i j : σ) [非平凡 R]
  证明: by
  by_cases c : i = j
  · simp only [c, if_true, degreeOf_def, degrees_X, Multiset.count_singleton]
  simp [c, degreeOf_def, degrees_X]

Depends on / 依赖: Multiset, Multiset.count_singleton, count_singleton, degreeOf_def, degrees_X, if_true
-/
theorem degreeOf_X [DecidableEq σ] (i j : σ) [Nontrivial R] :
    degreeOf i (X j : MvPolynomial σ R) = if i = j then 1 else 0 := by
  by_cases c : i = j
  · simp only [c, if_true, degreeOf_def, degrees_X, Multiset.count_singleton]
  simp [c, degreeOf_def, degrees_X]

/--
theorem `degreeOf_X_self` / 定理 `degreeOf_X_self`

English:
theorem degreeOf_X_self
  given: [Nontrivial R] (i : σ)
  proof: by
  classical simp [degreeOf_X]

中文:
定理 degreeOf_X_self
  条件: [非平凡 R] (i : σ)
  证明: by
  classical simp [degreeOf_X]
-/
@[simp] theorem degreeOf_X_self [Nontrivial R] (i : σ) :
    (X i : MvPolynomial σ R).degreeOf i = 1 := by
  classical simp [degreeOf_X]

/--
lemma `ne_zero_of_degreeOf_ne_zero` / 引理 `ne_zero_of_degreeOf_ne_zero`

English:
lemma ne_zero_of_degreeOf_ne_zero
  given: {i : σ}
  statement: p.degreeOf i != 0 -> p != 0
  proof: by
  aesop

中文:
引理 ne_zero_of_degreeOf_ne_zero
  条件: {i : σ}
  结论: p.degreeOf i != 0 -> p != 0
  证明: by
  aesop
-/
lemma ne_zero_of_degreeOf_ne_zero {i : σ} : p.degreeOf i != 0 -> p != 0 := by
  aesop

/--
theorem `degreeOf_add_le` / 定理 `degreeOf_add_le`

English:
theorem degreeOf_add_le
  given: (n : σ) (f g : MvPolynomial σ R)
  proof: by
  simp_rw [degreeOf_eq_sup]; exact supDegree_add_le

中文:
定理 degreeOf_add_le
  条件: (n : σ) (f g : 多元多项式 σ R)
  证明: by
  simp_rw [degreeOf_eq_sup]; exact supDegree_add_le

Depends on / 依赖: degreeOf_eq_sup, simp_rw, supDegree_add_le
-/
theorem degreeOf_add_le (n : σ) (f g : MvPolynomial σ R) :
    degreeOf n (f + g) <= max (degreeOf n f) (degreeOf n g) := by
  simp_rw [degreeOf_eq_sup]; exact supDegree_add_le

/--
theorem `monomial_le_degreeOf` / 定理 `monomial_le_degreeOf`

English:
theorem monomial_le_degreeOf
  given: (i : σ) {f : MvPolynomial σ R} {m : σ ->₀ Nat} (h_m : m in f.support)
  proof: by
  rw [degreeOf_eq_sup i]
  apply Finset.le_sup h_m

中文:
定理 monomial_le_degreeOf
  条件: (i : σ) {f : 多元多项式 σ R} {m : σ ->₀ 自然数} (h_m : m in f.support)
  证明: by
  rw [degreeOf_eq_sup i]
  apply Finset.le_sup h_m

Depends on / 依赖: Finset, Finset.le_sup, degreeOf_eq_sup, le_sup
-/
theorem monomial_le_degreeOf (i : σ) {f : MvPolynomial σ R} {m : σ ->₀ Nat} (h_m : m in f.support) :
    m i <= degreeOf i f := by
  rw [degreeOf_eq_sup i]
  apply Finset.le_sup h_m

/--
lemma `degreeOf_monomial_eq` / 引理 `degreeOf_monomial_eq`

English:
lemma degreeOf_monomial_eq
  given: (s : σ ->₀ Nat) (i : σ) {a : R} (ha : a != 0)
  proof: by
  classical rw [degreeOf_def, degrees_monomial_eq _ _ ha, Finsupp.count_toMultiset]

中文:
引理 degreeOf_monomial_eq
  条件: (s : σ ->₀ 自然数) (i : σ) {a : R} (ha : a != 0)
  证明: by
  classical rw [degreeOf_def, degrees_monomial_eq _ _ ha, Finsupp.count_toMultiset]

Depends on / 依赖: Finsupp, Finsupp.count_toMultiset, classical, count_toMultiset, degreeOf_def, degrees_monomial_eq
-/
lemma degreeOf_monomial_eq (s : σ ->₀ Nat) (i : σ) {a : R} (ha : a != 0) :
    (monomial s a).degreeOf i = s i := by
  classical rw [degreeOf_def, degrees_monomial_eq _ _ ha, Finsupp.count_toMultiset]

/--
theorem `degreeOf_X_self_pow` / 定理 `degreeOf_X_self_pow`

English:
theorem degreeOf_X_self_pow
  given: [Nontrivial R] (i : σ) (k : Nat)
  proof: by
  rw [X_pow_eq_monomial]; rw [degreeOf_monomial_eq _ _ one_ne_zero]; rw [Finsupp.single_eq_same]

中文:
定理 degreeOf_X_self_pow
  条件: [非平凡 R] (i : σ) (k : 自然数)
  证明: by
  rw [X_pow_eq_monomial]; rw [degreeOf_monomial_eq _ _ one_ne_zero]; rw [Finsupp.single_eq_same]
-/
@[simp] theorem degreeOf_X_self_pow [Nontrivial R] (i : σ) (k : Nat) :
    ((X i : MvPolynomial σ R) ^ k).degreeOf i = k := by
  rw [X_pow_eq_monomial]; rw [degreeOf_monomial_eq _ _ one_ne_zero]; rw [Finsupp.single_eq_same]

/--
lemma `le_degreeOf_of_mem_support` / 引理 `le_degreeOf_of_mem_support`

English:
lemma le_degreeOf_of_mem_support
  given: (i : σ) {s : σ ->₀ Nat}
  proof: fun h => by
obtain si | si := eq_or_lt_of_le Nat.zero_le (s i)
  · simp [← si]
  rw [degreeOf_eq_sup]; rw [Finset.le_sup_iff si]
  use s

中文:
引理 le_degreeOf_of_mem_support
  条件: (i : σ) {s : σ ->₀ 自然数}
  证明: fun h => by
obtain si | si := eq_or_lt_of_le Nat.zero_le (s i)
  · simp [← si]
  rw [degreeOf_eq_sup]; rw [Finset.le_sup_iff si]
  use s

Depends on / 依赖: Finset, Finset.le_sup_iff, Nat.zero_le, degreeOf_eq_sup, eq_or_lt_of_le, le_sup_iff, zero_le
-/
lemma le_degreeOf_of_mem_support (i : σ) {s : σ ->₀ Nat} :
    s in p.support -> s i <= p.degreeOf i := fun h => by
obtain si | si := eq_or_lt_of_le Nat.zero_le (s i)
  · simp [← si]
  rw [degreeOf_eq_sup]; rw [Finset.le_sup_iff si]
  use s

/--
lemma `notMem_support_of_degreeOf_lt` / 引理 `notMem_support_of_degreeOf_lt`

English:
lemma notMem_support_of_degreeOf_lt
  given: (i : σ) {s : σ ->₀ Nat}
  proof: fun h => by
  contrapose! h
  exact le_degreeOf_of_mem_support i h

中文:
引理 notMem_support_of_degreeOf_lt
  条件: (i : σ) {s : σ ->₀ 自然数}
  证明: fun h => by
  contrapose! h
  exact le_degreeOf_of_mem_support i h

Depends on / 依赖: contrapose, le_degreeOf_of_mem_support
-/
lemma notMem_support_of_degreeOf_lt (i : σ) {s : σ ->₀ Nat} :
    p.degreeOf i < s i -> s ∉ p.support := fun h => by
  contrapose! h
  exact le_degreeOf_of_mem_support i h

/--
theorem `degreeOf_mul_le` / 定理 `degreeOf_mul_le`

English:
theorem degreeOf_mul_le
  given: (i : σ) (f g : MvPolynomial σ R)
  proof: by
  classical
  simp only [degreeOf]
  convert! Multiset.count_le_of_le i degrees_mul_le
  rw [Multiset.count_add]

中文:
定理 degreeOf_mul_le
  条件: (i : σ) (f g : 多元多项式 σ R)
  证明: by
  classical
  simp only [degreeOf]
  convert! Multiset.count_le_of_le i degrees_mul_le
  rw [Multiset.count_add]

Depends on / 依赖: Multiset, Multiset.count_add, Multiset.count_le_of_le, classical, convert, count_add, count_le_of_le, degreeOf, degrees_mul_le
-/
theorem degreeOf_mul_le (i : σ) (f g : MvPolynomial σ R) :
    degreeOf i (f * g) <= degreeOf i f + degreeOf i g := by
  classical
  simp only [degreeOf]
  convert! Multiset.count_le_of_le i degrees_mul_le
  rw [Multiset.count_add]

/--
theorem `degreeOf_sum_le` / 定理 `degreeOf_sum_le`

English:
theorem degreeOf_sum_le
  given: {ι : Type*} (i : σ) (s : Finset ι) (f : ι -> MvPolynomial σ R)
  proof: by
  simp_rw [degreeOf_eq_sup]
  exact supDegree_sum_le

中文:
定理 degreeOf_sum_le
  条件: {ι : 类型} (i : σ) (s : 有限集 ι) (f : ι -> 多元多项式 σ R)
  证明: by
  simp_rw [degreeOf_eq_sup]
  exact supDegree_sum_le

Depends on / 依赖: degreeOf_eq_sup, simp_rw, supDegree_sum_le
-/
theorem degreeOf_sum_le {ι : Type*} (i : σ) (s : Finset ι) (f : ι -> MvPolynomial σ R) :
    degreeOf i (∑ j in s, f j) <= s.sup fun j => degreeOf i (f j) := by
  simp_rw [degreeOf_eq_sup]
  exact supDegree_sum_le

/--
theorem `degreeOf_prod_le` / 定理 `degreeOf_prod_le`

English:
theorem degreeOf_prod_le
  given: {ι : Type*} (i : σ) (s : Finset ι) (f : ι -> MvPolynomial σ R)
  proof: by
  simp_rw [degreeOf_eq_sup]
  exact supDegree_prod_le (by simp only [coe_zero, Pi.zero_apply]) (by simp)

中文:
定理 degreeOf_prod_le
  条件: {ι : 类型} (i : σ) (s : 有限集 ι) (f : ι -> 多元多项式 σ R)
  证明: by
  simp_rw [degreeOf_eq_sup]
  exact supDegree_prod_le (by simp only [coe_zero, Pi.zero_apply]) (by simp)

Depends on / 依赖: Pi.zero_apply, coe_zero, degreeOf_eq_sup, simp_rw, supDegree_prod_le, zero_apply
-/
theorem degreeOf_prod_le {ι : Type*} (i : σ) (s : Finset ι) (f : ι -> MvPolynomial σ R) :
    degreeOf i (∏ j in s, f j) <= ∑ j in s, (f j).degreeOf i := by
  simp_rw [degreeOf_eq_sup]
  exact supDegree_prod_le (by simp only [coe_zero, Pi.zero_apply]) (by simp)

/--
theorem `degreeOf_pow_le` / 定理 `degreeOf_pow_le`

English:
theorem degreeOf_pow_le
  given: (i : σ) (p : MvPolynomial σ R) (n : Nat)
  proof: by
  simpa using degreeOf_prod_le i (Finset.range n) (fun _ => p)

中文:
定理 degreeOf_pow_le
  条件: (i : σ) (p : 多元多项式 σ R) (n : 自然数)
  证明: by
  simpa using degreeOf_prod_le i (Finset.range n) (fun _ => p)

Depends on / 依赖: Finset, Finset.range, degreeOf_prod_le
-/
theorem degreeOf_pow_le (i : σ) (p : MvPolynomial σ R) (n : Nat) :
    degreeOf i (p ^ n) <= n * degreeOf i p := by
  simpa using degreeOf_prod_le i (Finset.range n) (fun _ => p)

/--
theorem `degreeOf_mul_X_of_ne` / 定理 `degreeOf_mul_X_of_ne`

English:
theorem degreeOf_mul_X_of_ne
  given: {i j : σ} (f : MvPolynomial σ R) (h : i != j)
  proof: by
  classical
  simp only [degreeOf_eq_sup i, support_mul_X, Finset.sup_map]
  congr
  ext
  simp only [Finsupp.single, addRightEmbedding_apply, coe_mk,
    Pi.add_apply, comp_apply, Finsupp.coe_add, Pi.single_eq_of_ne h, add_zero]

中文:
定理 degreeOf_mul_X_of_ne
  条件: {i j : σ} (f : 多元多项式 σ R) (h : i != j)
  证明: by
  classical
  simp only [degreeOf_eq_sup i, support_mul_X, Finset.sup_map]
  congr
  ext
  simp only [Finsupp.single, addRightEmbedding_apply, coe_mk,
    Pi.add_apply, comp_apply, Finsupp.coe_add, Pi.single_eq_of_ne h, add_zero]

Depends on / 依赖: Finset, Finset.sup_map, Finsupp, Finsupp.coe_add, Finsupp.single, Pi.add_apply, Pi.single_eq_of_ne, addRightEmbedding_apply, add_apply, add_zero, classical, coe_add, coe_mk, comp_apply, degreeOf_eq_sup, single, single_eq_of_ne, sup_map, support_mul_X
-/
theorem degreeOf_mul_X_of_ne {i j : σ} (f : MvPolynomial σ R) (h : i != j) :
    degreeOf i (f * X j) = degreeOf i f := by
  classical
  simp only [degreeOf_eq_sup i, support_mul_X, Finset.sup_map]
  congr
  ext
  simp only [Finsupp.single, addRightEmbedding_apply, coe_mk,
    Pi.add_apply, comp_apply, Finsupp.coe_add, Pi.single_eq_of_ne h, add_zero]

/--
theorem `degreeOf_mul_X_self` / 定理 `degreeOf_mul_X_self`

English:
theorem degreeOf_mul_X_self
  given: (j : σ) (f : MvPolynomial σ R)
  proof: by
  classical
  simp only [degreeOf]
  apply (Multiset.count_le_of_le j degrees_mul_le).trans
  simp only [Multiset.count_add, add_le_add_iff_left]
convert! Multiset.count_le_of_le j degrees_X' j
  rw [Multiset.count_singleton_self]

中文:
定理 degreeOf_mul_X_self
  条件: (j : σ) (f : 多元多项式 σ R)
  证明: by
  classical
  simp only [degreeOf]
  apply (Multiset.count_le_of_le j degrees_mul_le).trans
  simp only [Multiset.count_add, add_le_add_iff_left]
convert! Multiset.count_le_of_le j degrees_X' j
  rw [Multiset.count_singleton_self]

Depends on / 依赖: Multiset, Multiset.count_add, Multiset.count_le_of_le, Multiset.count_singleton_self, add_le_add_iff_left, classical, convert, count_add, count_le_of_le, count_singleton_self, degreeOf, degrees_X, degrees_mul_le
-/
theorem degreeOf_mul_X_self (j : σ) (f : MvPolynomial σ R) :
    degreeOf j (f * X j) <= degreeOf j f + 1 := by
  classical
  simp only [degreeOf]
  apply (Multiset.count_le_of_le j degrees_mul_le).trans
  simp only [Multiset.count_add, add_le_add_iff_left]
convert! Multiset.count_le_of_le j degrees_X' j
  rw [Multiset.count_singleton_self]

/--
theorem `degreeOf_X_pow_of_ne` / 定理 `degreeOf_X_pow_of_ne`

English:
theorem degreeOf_X_pow_of_ne
  given: {i j : σ} (k : Nat) (h : i != j)
  proof: by
  induction k with
  | zero => rw [pow_zero, ← C_1, degreeOf_C]
  | succ k hk => rw [pow_add, pow_one, degreeOf_mul_X_of_ne _ h, hk]

中文:
定理 degreeOf_X_pow_of_ne
  条件: {i j : σ} (k : 自然数) (h : i != j)
  证明: by
  induction k with
  | zero => rw [pow_zero, ← C_1, degreeOf_C]
  | succ k hk => rw [pow_add, pow_one, degreeOf_mul_X_of_ne _ h, hk]

Depends on / 依赖: degreeOf_C, degreeOf_mul_X_of_ne, pow_add, pow_one, pow_zero
-/
theorem degreeOf_X_pow_of_ne {i j : σ} (k : Nat) (h : i != j) :
    ((X j : MvPolynomial σ R) ^ k).degreeOf i = 0 := by
  induction k with
  | zero => rw [pow_zero, ← C_1, degreeOf_C]
  | succ k hk => rw [pow_add, pow_one, degreeOf_mul_X_of_ne _ h, hk]

/--
theorem `degreeOf_X_of_ne` / 定理 `degreeOf_X_of_ne`

English:
theorem degreeOf_X_of_ne
  given: {i j : σ} (h : i != j)
  statement: (X j : MvPolynomial σ R).degreeOf i = 0
  proof: pow_one (X j : MvPolynomial σ R) ▸ degreeOf_X_pow_of_ne 1 h

中文:
定理 degreeOf_X_of_ne
  条件: {i j : σ} (h : i != j)
  结论: (X j : 多元多项式 σ R).degreeOf i = 0
  证明: pow_one (X j : MvPolynomial σ R) ▸ degreeOf_X_pow_of_ne 1 h

Depends on / 依赖: MvPolynomial, degreeOf_X_pow_of_ne, pow_one
-/
theorem degreeOf_X_of_ne {i j : σ} (h : i != j) : (X j : MvPolynomial σ R).degreeOf i = 0 :=
  pow_one (X j : MvPolynomial σ R) ▸ degreeOf_X_pow_of_ne 1 h

/--
theorem `degreeOf_mul_X_eq_degreeOf_add_one_iff` / 定理 `degreeOf_mul_X_eq_degreeOf_add_one_iff`

English:
theorem degreeOf_mul_X_eq_degreeOf_add_one_iff
  given: (j : σ) (f : MvPolynomial σ R)
  proof: by
  refine ⟨fun h => by by_contra ha; simp [ha] at h, fun h => ?_⟩
  apply Nat.le_antisymm (degreeOf_mul_X_self j f)
  have : (f.support.sup fun m => m j) + 1 = (f.support.sup fun m => (m j + 1)) :=
    Finset.apply_sup_eq_sup_comp_of_nonempty @Nat.succ_le_succ (support_nonempty.mpr h)
  simp only [degreeOf_eq_sup, support_mul_X, this]
  apply Finset.sup_le
  intro x hx
  simp only [Finset.sup_map, bot_eq_zero', add_pos_iff, zero_lt_one, or_true, Finset.le_sup_iff]
  use x
  simpa using mem_support_iff.mp hx

中文:
定理 degreeOf_mul_X_eq_degreeOf_add_one_iff
  条件: (j : σ) (f : 多元多项式 σ R)
  证明: by
  refine ⟨fun h => by by_contra ha; simp [ha] at h, fun h => ?_⟩
  apply Nat.le_antisymm (degreeOf_mul_X_self j f)
  have : (f.support.sup fun m => m j) + 1 = (f.support.sup fun m => (m j + 1)) :=
    Finset.apply_sup_eq_sup_comp_of_nonempty @Nat.succ_le_succ (support_nonempty.mpr h)
  simp only [degreeOf_eq_sup, support_mul_X, this]
  apply Finset.sup_le
  intro x hx
  simp only [Finset.sup_map, bot_eq_zero', add_pos_iff, zero_lt_one, or_true, Finset.le_sup_iff]
  use x
  simpa using mem_support_iff.mp hx

Depends on / 依赖: Finset, Finset.apply_sup_eq_sup_comp_of_nonempty, Finset.le_sup_iff, Finset.sup_le, Finset.sup_map, Nat.le_antisymm, Nat.succ_le_succ, add_pos_iff, apply_sup_eq_sup_comp_of_nonempty, bot_eq_zero, degreeOf_eq_sup, degreeOf_mul_X_self, f.support.sup, le_antisymm, le_sup_iff, mem_support_iff, mem_support_iff.mp, or_true, succ_le_succ, sup_le
-/
theorem degreeOf_mul_X_eq_degreeOf_add_one_iff (j : σ) (f : MvPolynomial σ R) :
    degreeOf j (f * X j) = degreeOf j f + 1 ↔ f != 0 := by
  refine ⟨fun h => by by_contra ha; simp [ha] at h, fun h => ?_⟩
  apply Nat.le_antisymm (degreeOf_mul_X_self j f)
  have : (f.support.sup fun m => m j) + 1 = (f.support.sup fun m => (m j + 1)) :=
    Finset.apply_sup_eq_sup_comp_of_nonempty @Nat.succ_le_succ (support_nonempty.mpr h)
  simp only [degreeOf_eq_sup, support_mul_X, this]
  apply Finset.sup_le
  intro x hx
  simp only [Finset.sup_map, bot_eq_zero', add_pos_iff, zero_lt_one, or_true, Finset.le_sup_iff]
  use x
  simpa using mem_support_iff.mp hx

/--
theorem `degreeOf_mul_X_self_pow_eq_add_of_ne_zero` / 定理 `degreeOf_mul_X_self_pow_eq_add_of_ne_zero`

English:
theorem degreeOf_mul_X_self_pow_eq_add_of_ne_zero
  given: (i : σ) (k : Nat) (h : p != 0)
  proof: by
  induction k with
  | zero => rw [pow_zero, mul_one, add_zero]
  | succ k hk =>
    have : p * X i ^ k != 0 := by
      rcases ne_zero_iff.mp h with ⟨s, hs⟩
      refine ne_zero_iff.mpr ⟨s + Finsupp.single i k, ?_⟩
      rwa [X_pow_eq_monomial, coeff_mul_monomial, mul_one]
    rw [pow_add]; rw [pow_one]; rw [← mul_assoc]; rw [(degreeOf_mul_X_eq_degreeOf_add_one_iff i _).mpr this]; rw [hk]; rw [add_assoc]

中文:
定理 degreeOf_mul_X_self_pow_eq_add_of_ne_zero
  条件: (i : σ) (k : 自然数) (h : p != 0)
  证明: by
  induction k with
  | zero => rw [pow_zero, mul_one, add_zero]
  | succ k hk =>
    have : p * X i ^ k != 0 := by
      rcases ne_zero_iff.mp h with ⟨s, hs⟩
      refine ne_zero_iff.mpr ⟨s + Finsupp.single i k, ?_⟩
      rwa [X_pow_eq_monomial, coeff_mul_monomial, mul_one]
    rw [pow_add]; rw [pow_one]; rw [← mul_assoc]; rw [(degreeOf_mul_X_eq_degreeOf_add_one_iff i _).mpr this]; rw [hk]; rw [add_assoc]

Depends on / 依赖: Finsupp, Finsupp.single, X_pow_eq_monomial, add_assoc, add_zero, coeff_mul_monomial, degreeOf_mul_X_eq_degreeOf_add_one_iff, mul_assoc, mul_one, ne_zero_iff, ne_zero_iff.mp, ne_zero_iff.mpr, pow_add, pow_one, pow_zero, single
-/
theorem degreeOf_mul_X_self_pow_eq_add_of_ne_zero (i : σ) (k : Nat) (h : p != 0) :
    (p * X i ^ k).degreeOf i = p.degreeOf i + k := by
  induction k with
  | zero => rw [pow_zero, mul_one, add_zero]
  | succ k hk =>
    have : p * X i ^ k != 0 := by
      rcases ne_zero_iff.mp h with ⟨s, hs⟩
      refine ne_zero_iff.mpr ⟨s + Finsupp.single i k, ?_⟩
      rwa [X_pow_eq_monomial, coeff_mul_monomial, mul_one]
    rw [pow_add]; rw [pow_one]; rw [← mul_assoc]; rw [(degreeOf_mul_X_eq_degreeOf_add_one_iff i _).mpr this]; rw [hk]; rw [add_assoc]

/--
theorem `degreeOf_mul_X_pow_of_ne` / 定理 `degreeOf_mul_X_pow_of_ne`

English:
theorem degreeOf_mul_X_pow_of_ne
  given: {i j : σ} (k : Nat) (h : i != j)
  proof: by
  induction k with
  | zero => rw [pow_zero, mul_one]
  | succ k hk => rw [pow_add, pow_one, ← mul_assoc, degreeOf_mul_X_of_ne _ h, hk]

中文:
定理 degreeOf_mul_X_pow_of_ne
  条件: {i j : σ} (k : 自然数) (h : i != j)
  证明: by
  induction k with
  | zero => rw [pow_zero, mul_one]
  | succ k hk => rw [pow_add, pow_one, ← mul_assoc, degreeOf_mul_X_of_ne _ h, hk]

Depends on / 依赖: degreeOf_mul_X_of_ne, mul_assoc, mul_one, pow_add, pow_one, pow_zero
-/
theorem degreeOf_mul_X_pow_of_ne {i j : σ} (k : Nat) (h : i != j) :
    (p * X j ^ k).degreeOf i = p.degreeOf i := by
  induction k with
  | zero => rw [pow_zero, mul_one]
  | succ k hk => rw [pow_add, pow_one, ← mul_assoc, degreeOf_mul_X_of_ne _ h, hk]

/--
theorem `degreeOf_add_eq_of_degreeOf_lt` / 定理 `degreeOf_add_eq_of_degreeOf_lt`

English:
theorem degreeOf_add_eq_of_degreeOf_lt
  given: {i : σ} (h : q.degreeOf i < p.degreeOf i)
  proof: by
  apply le_antisymm
  · rw [← max_eq_left_of_lt h]
    exact degreeOf_add_le i p q
  nth_rw 2 [degreeOf_eq_sup]
  apply (Finset.le_sup_iff <| Nat.zero_lt_of_lt h).mpr
  have : p.support.Nonempty := by aesop
  have ⟨s, hs1, hs2⟩ := Finset.exists_mem_eq_sup _ this (fun s => s i)
  rw [← degreeOf_eq_sup i p] at hs2
  refine ⟨s, ?_, by rw [hs2]⟩
  have : s ∉ q.support := by
    contrapose! h
    rw [hs2]
    exact le_degreeOf_of_mem_support i h
  simp only [mem_support_iff, ne_eq, coeff_add, not_not] at hs1 ⊢ this
  rwa [this, add_zero]

中文:
定理 degreeOf_add_eq_of_degreeOf_lt
  条件: {i : σ} (h : q.degreeOf i < p.degreeOf i)
  证明: by
  apply le_antisymm
  · rw [← max_eq_left_of_lt h]
    exact degreeOf_add_le i p q
  nth_rw 2 [degreeOf_eq_sup]
  apply (Finset.le_sup_iff <| Nat.zero_lt_of_lt h).mpr
  have : p.support.Nonempty := by aesop
  have ⟨s, hs1, hs2⟩ := Finset.exists_mem_eq_sup _ this (fun s => s i)
  rw [← degreeOf_eq_sup i p] at hs2
  refine ⟨s, ?_, by rw [hs2]⟩
  have : s ∉ q.support := by
    contrapose! h
    rw [hs2]
    exact le_degreeOf_of_mem_support i h
  simp only [mem_support_iff, ne_eq, coeff_add, not_not] at hs1 ⊢ this
  rwa [this, add_zero]

Depends on / 依赖: Finset, Finset.exists_mem_eq_sup, Finset.le_sup_iff, Nat.zero_lt_of_lt, Nonempty, add_ze, coeff_add, contrapose, degreeOf_add_le, degreeOf_eq_sup, exists_mem_eq_sup, le_antisymm, le_degreeOf_of_mem_support, le_sup_iff, max_eq_left_of_lt, mem_support_iff, ne_eq, not_not, nth_rw, p.support.Nonempty
-/
theorem degreeOf_add_eq_of_degreeOf_lt {i : σ} (h : q.degreeOf i < p.degreeOf i) :
    (p + q).degreeOf i = p.degreeOf i := by
  apply le_antisymm
  · rw [← max_eq_left_of_lt h]
    exact degreeOf_add_le i p q
  nth_rw 2 [degreeOf_eq_sup]
  apply (Finset.le_sup_iff <| Nat.zero_lt_of_lt h).mpr
  have : p.support.Nonempty := by aesop
  have ⟨s, hs1, hs2⟩ := Finset.exists_mem_eq_sup _ this (fun s => s i)
  rw [← degreeOf_eq_sup i p] at hs2
  refine ⟨s, ?_, by rw [hs2]⟩
  have : s ∉ q.support := by
    contrapose! h
    rw [hs2]
    exact le_degreeOf_of_mem_support i h
  simp only [mem_support_iff, ne_eq, coeff_add, not_not] at hs1 ⊢ this
  rwa [this, add_zero]

/--
theorem `degreeOf_eq_of_degreeOf_add_lt` / 定理 `degreeOf_eq_of_degreeOf_add_lt`

English:
theorem degreeOf_eq_of_degreeOf_add_lt
  given: {i : σ} (h : (p + q).degreeOf i < p.degreeOf i)
  proof: by
  contrapose! h
  apply le_trans (Nat.le_max_left _ (q.degreeOf i))
  rcases Nat.lt_or_lt_of_ne h with h | h
  · simp [add_comm p q, degreeOf_add_eq_of_degreeOf_lt h, max_eq_right_of_lt h]
  · simp [degreeOf_add_eq_of_degreeOf_lt h, max_eq_left_of_lt h]

中文:
定理 degreeOf_eq_of_degreeOf_add_lt
  条件: {i : σ} (h : (p + q).degreeOf i < p.degreeOf i)
  证明: by
  contrapose! h
  apply le_trans (Nat.le_max_left _ (q.degreeOf i))
  rcases Nat.lt_or_lt_of_ne h with h | h
  · simp [add_comm p q, degreeOf_add_eq_of_degreeOf_lt h, max_eq_right_of_lt h]
  · simp [degreeOf_add_eq_of_degreeOf_lt h, max_eq_left_of_lt h]

Depends on / 依赖: Nat.le_max_left, Nat.lt_or_lt_of_ne, add_comm, contrapose, degreeOf, degreeOf_add_eq_of_degreeOf_lt, le_max_left, le_trans, lt_or_lt_of_ne, max_eq_left_of_lt, max_eq_right_of_lt, q.degreeOf
-/
theorem degreeOf_eq_of_degreeOf_add_lt {i : σ} (h : (p + q).degreeOf i < p.degreeOf i) :
    p.degreeOf i = q.degreeOf i := by
  contrapose! h
  apply le_trans (Nat.le_max_left _ (q.degreeOf i))
  rcases Nat.lt_or_lt_of_ne h with h | h
  · simp [add_comm p q, degreeOf_add_eq_of_degreeOf_lt h, max_eq_right_of_lt h]
  · simp [degreeOf_add_eq_of_degreeOf_lt h, max_eq_left_of_lt h]

/--
theorem `degreeOf_C_mul_le` / 定理 `degreeOf_C_mul_le`

English:
theorem degreeOf_C_mul_le
  given: (p : MvPolynomial σ R) (i : σ) (c : R)
  proof: by
  unfold degreeOf
  convert! Multiset.count_le_of_le i degrees_mul_le
  simp only [degrees_C, zero_add]

中文:
定理 degreeOf_C_mul_le
  条件: (p : 多元多项式 σ R) (i : σ) (c : R)
  证明: by
  unfold degreeOf
  convert! Multiset.count_le_of_le i degrees_mul_le
  simp only [degrees_C, zero_add]

Depends on / 依赖: Multiset, Multiset.count_le_of_le, convert, count_le_of_le, degreeOf, degrees_C, degrees_mul_le, zero_add
-/
theorem degreeOf_C_mul_le (p : MvPolynomial σ R) (i : σ) (c : R) :
    (C c * p).degreeOf i <= p.degreeOf i := by
  unfold degreeOf
  convert! Multiset.count_le_of_le i degrees_mul_le
  simp only [degrees_C, zero_add]

/--
theorem `degreeOf_mul_C_le` / 定理 `degreeOf_mul_C_le`

English:
theorem degreeOf_mul_C_le
  given: (p : MvPolynomial σ R) (i : σ) (c : R)
  proof: by
  unfold degreeOf
  convert! Multiset.count_le_of_le i degrees_mul_le
  simp only [degrees_C, add_zero]

中文:
定理 degreeOf_mul_C_le
  条件: (p : 多元多项式 σ R) (i : σ) (c : R)
  证明: by
  unfold degreeOf
  convert! Multiset.count_le_of_le i degrees_mul_le
  simp only [degrees_C, add_zero]

Depends on / 依赖: Multiset, Multiset.count_le_of_le, add_zero, convert, count_le_of_le, degreeOf, degrees_C, degrees_mul_le
-/
theorem degreeOf_mul_C_le (p : MvPolynomial σ R) (i : σ) (c : R) :
    (p * C c).degreeOf i <= p.degreeOf i := by
  unfold degreeOf
  convert! Multiset.count_le_of_le i degrees_mul_le
  simp only [degrees_C, add_zero]

/--
theorem `degreeOf_rename_of_injective` / 定理 `degreeOf_rename_of_injective`

English:
theorem degreeOf_rename_of_injective
  statement: {p : MvPolynomial σ R} {f : σ -> τ} (h : Function.Injective f)
  proof: by
  classical
  simp only [degreeOf, degrees_rename_of_injective h, Multiset.count_map_eq_count' f p.degrees h]

中文:
定理 degreeOf_rename_of_injective
  结论: {p : 多元多项式 σ R} {f : σ -> τ} (h : 函数.单射 f)
  证明: by
  classical
  simp only [degreeOf, degrees_rename_of_injective h, Multiset.count_map_eq_count' f p.degrees h]

Depends on / 依赖: Multiset, Multiset.count_map_eq_count, classical, count_map_eq_count, degreeOf, degrees, degrees_rename_of_injective, p.degrees
-/
theorem degreeOf_rename_of_injective {p : MvPolynomial σ R} {f : σ -> τ} (h : Function.Injective f)
    (i : σ) : degreeOf (f i) (rename f p) = degreeOf i p := by
  classical
  simp only [degreeOf, degrees_rename_of_injective h, Multiset.count_map_eq_count' f p.degrees h]

end DegreeOf

section TotalDegree

/-! ### `totalDegree` -/


/--
Definition of `totalDegree` / `totalDegree` 的定义

English:
definition totalDegree
  signature: (p : MvPolynomial σ R)
  body: p.support.sup fun s => s.sum fun _ e => e

中文:
定义 totalDegree
  签名: (p : 多元多项式 σ R)
  定义体: p.support.sup fun s => s.sum fun _ e => e

Depends on / 依赖: p.support.sup, s.sum, support
-/
def totalDegree (p : MvPolynomial σ R) : Nat :=
  p.support.sup fun s => s.sum fun _ e => e

/--
theorem `totalDegree_eq` / 定理 `totalDegree_eq`

English:
theorem totalDegree_eq
  given: (p : MvPolynomial σ R)
  proof: by
  rw [totalDegree]
  congr; funext m
  exact (Finsupp.card_toMultiset _).symm

中文:
定理 totalDegree_eq
  条件: (p : 多元多项式 σ R)
  证明: by
  rw [totalDegree]
  congr; funext m
  exact (Finsupp.card_toMultiset _).symm

Depends on / 依赖: Finsupp, Finsupp.card_toMultiset, card_toMultiset, totalDegree
-/
theorem totalDegree_eq (p : MvPolynomial σ R) :
    p.totalDegree = p.support.sup fun m => Multiset.card (toMultiset m) := by
  rw [totalDegree]
  congr; funext m
  exact (Finsupp.card_toMultiset _).symm

/--
theorem `le_totalDegree` / 定理 `le_totalDegree`

English:
theorem le_totalDegree
  given: {p : MvPolynomial σ R} {s : σ ->₀ Nat} (h : s in p.support)
  proof: Finset.le_sup (α := Nat) (f := fun s => sum s fun _ e => e) h

中文:
定理 le_totalDegree
  条件: {p : 多元多项式 σ R} {s : σ ->₀ 自然数} (h : s in p.support)
  证明: Finset.le_sup (α := Nat) (f := fun s => sum s fun _ e => e) h

Depends on / 依赖: Finset, Finset.le_sup, le_sup
-/
theorem le_totalDegree {p : MvPolynomial σ R} {s : σ ->₀ Nat} (h : s in p.support) :
    (s.sum fun _ e => e) <= totalDegree p :=
  Finset.le_sup (α := Nat) (f := fun s => sum s fun _ e => e) h

/--
theorem `totalDegree_le_degrees_card` / 定理 `totalDegree_le_degrees_card`

English:
theorem totalDegree_le_degrees_card
  given: (p : MvPolynomial σ R)
  proof: by
  classical
  rw [totalDegree_eq]
exact Finset.sup_le fun s hs => Multiset.card_le_card Finset.le_sup hs

中文:
定理 totalDegree_le_degrees_card
  条件: (p : 多元多项式 σ R)
  证明: by
  classical
  rw [totalDegree_eq]
exact Finset.sup_le fun s hs => Multiset.card_le_card Finset.le_sup hs

Depends on / 依赖: Finset, Finset.le_sup, Finset.sup_le, Multiset, Multiset.card_le_card, card_le_card, classical, le_sup, sup_le, totalDegree_eq
-/
theorem totalDegree_le_degrees_card (p : MvPolynomial σ R) :
    p.totalDegree <= Multiset.card p.degrees := by
  classical
  rw [totalDegree_eq]
exact Finset.sup_le fun s hs => Multiset.card_le_card Finset.le_sup hs

/--
theorem `totalDegree_le_of_support_subset` / 定理 `totalDegree_le_of_support_subset`

English:
theorem totalDegree_le_of_support_subset
  given: (h : p.support subseteq q.support)
  proof: Finset.sup_mono h

@[simp]

中文:
定理 totalDegree_le_of_support_subset
  条件: (h : p.support subseteq q.support)
  证明: Finset.sup_mono h

@[simp]

Depends on / 依赖: Finset, Finset.sup_mono, sup_mono
-/
theorem totalDegree_le_of_support_subset (h : p.support subseteq q.support) :
    totalDegree p <= totalDegree q :=
  Finset.sup_mono h

@[simp]
/--
theorem `totalDegree_C` / 定理 `totalDegree_C`

English:
theorem totalDegree_C
  given: (a : R)
  statement: (C a : MvPolynomial σ R).totalDegree = 0
  proof: (supDegree_single 0 a).trans by rw [sum_zero_index, bot_eq_zero', ite_self]

@[simp]

中文:
定理 totalDegree_C
  条件: (a : R)
  结论: (C a : 多元多项式 σ R).totalDegree = 0
  证明: (supDegree_single 0 a).trans by rw [sum_zero_index, bot_eq_zero', ite_self]

@[simp]

Depends on / 依赖: bot_eq_zero, ite_self, sum_zero_index, supDegree_single
-/
theorem totalDegree_C (a : R) : (C a : MvPolynomial σ R).totalDegree = 0 :=
(supDegree_single 0 a).trans by rw [sum_zero_index, bot_eq_zero', ite_self]

@[simp]
/--
theorem `totalDegree_zero` / 定理 `totalDegree_zero`

English:
theorem totalDegree_zero
  statement: (0 : MvPolynomial σ R).totalDegree = 0
  proof: by
  rw [← C_0]; exact totalDegree_C (0 : R)

@[simp]

中文:
定理 totalDegree_zero
  结论: (0 : 多元多项式 σ R).totalDegree = 0
  证明: by
  rw [← C_0]; exact totalDegree_C (0 : R)

@[simp]

Depends on / 依赖: totalDegree_C
-/
theorem totalDegree_zero : (0 : MvPolynomial σ R).totalDegree = 0 := by
  rw [← C_0]; exact totalDegree_C (0 : R)

@[simp]
/--
theorem `totalDegree_one` / 定理 `totalDegree_one`

English:
theorem totalDegree_one
  statement: (1 : MvPolynomial σ R).totalDegree = 0
  proof: totalDegree_C (1 : R)

@[simp]

中文:
定理 totalDegree_one
  结论: (1 : 多元多项式 σ R).totalDegree = 0
  证明: totalDegree_C (1 : R)

@[simp]

Depends on / 依赖: totalDegree_C
-/
theorem totalDegree_one : (1 : MvPolynomial σ R).totalDegree = 0 :=
  totalDegree_C (1 : R)

@[simp]
/--
theorem `totalDegree_X` / 定理 `totalDegree_X`

English:
theorem totalDegree_X
  given: {R} [CommSemiring R] [Nontrivial R] (s : σ)
  proof: by
  rw [totalDegree]; rw [support_X]
  simp only [Finset.sup, Finsupp.sum_single_index, Finset.fold_singleton, sup_bot_eq]

中文:
定理 totalDegree_X
  条件: {R} [交换半环 R] [非平凡 R] (s : σ)
  证明: by
  rw [totalDegree]; rw [support_X]
  simp only [Finset.sup, Finsupp.sum_single_index, Finset.fold_singleton, sup_bot_eq]

Depends on / 依赖: Finset, Finset.fold_singleton, Finset.sup, Finsupp, Finsupp.sum_single_index, fold_singleton, sum_single_index, sup_bot_eq, support_X, totalDegree
-/
theorem totalDegree_X {R} [CommSemiring R] [Nontrivial R] (s : σ) :
    (X s : MvPolynomial σ R).totalDegree = 1 := by
  rw [totalDegree]; rw [support_X]
  simp only [Finset.sup, Finsupp.sum_single_index, Finset.fold_singleton, sup_bot_eq]

/--
theorem `totalDegree_add` / 定理 `totalDegree_add`

English:
theorem totalDegree_add
  given: (a b : MvPolynomial σ R)
  proof: sup_support_coeff_add_le _ _ _

中文:
定理 totalDegree_add
  条件: (a b : 多元多项式 σ R)
  证明: sup_support_coeff_add_le _ _ _

Depends on / 依赖: sup_support_coeff_add_le
-/
theorem totalDegree_add (a b : MvPolynomial σ R) :
    (a + b).totalDegree <= max a.totalDegree b.totalDegree :=
  sup_support_coeff_add_le _ _ _

/--
theorem `totalDegree_add_eq_left_of_totalDegree_lt` / 定理 `totalDegree_add_eq_left_of_totalDegree_lt`

English:
theorem totalDegree_add_eq_left_of_totalDegree_lt
  statement: {p q : MvPolynomial σ R}
  proof: by
  classical
    apply le_antisymm
    · rw [← max_eq_left_of_lt h]
      exact totalDegree_add p q
    by_cases hp : p = 0
    · simp [hp]
    obtain ⟨b, hb₁, hb₂⟩ :=
      p.support.exists_mem_eq_sup (by simpa) fun m : σ ->₀ Nat => Multiset.card (toMultiset m)
    have hb : b ∉ q.support := by
      contrapose! h
      rw [totalDegree_eq p]; rw [hb₂]; rw [totalDegree_eq]
      apply Finset.le_sup h
    have hbb : b in (p + q).support := by
      apply support_sdiff_support_subset_support_add
      rw [Finset.mem_sdiff]
      exact ⟨hb₁, hb⟩
    rw [totalDegree_eq]; rw [hb₂]; rw [totalDegree_eq]
    exact Finset.le_sup (f := fun m => Multiset.card (Finsupp.toMultiset m)) hbb

中文:
定理 totalDegree_add_eq_left_of_totalDegree_lt
  结论: {p q : 多元多项式 σ R}
  证明: by
  classical
    apply le_antisymm
    · rw [← max_eq_left_of_lt h]
      exact totalDegree_add p q
    by_cases hp : p = 0
    · simp [hp]
    obtain ⟨b, hb₁, hb₂⟩ :=
      p.support.exists_mem_eq_sup (by simpa) fun m : σ ->₀ Nat => Multiset.card (toMultiset m)
    have hb : b ∉ q.support := by
      contrapose! h
      rw [totalDegree_eq p]; rw [hb₂]; rw [totalDegree_eq]
      apply Finset.le_sup h
    have hbb : b in (p + q).support := by
      apply support_sdiff_support_subset_support_add
      rw [Finset.mem_sdiff]
      exact ⟨hb₁, hb⟩
    rw [totalDegree_eq]; rw [hb₂]; rw [totalDegree_eq]
    exact Finset.le_sup (f := fun m => Multiset.card (Finsupp.toMultiset m)) hbb

Depends on / 依赖: Finset, Finset.le_sup, Finset.mem_sdiff, Multiset, Multiset.card, classical, contrapose, exists_mem_eq_sup, le_antisymm, le_sup, max_eq_left_of_lt, mem_sdiff, p.support.exists_mem_eq_sup, q.support, support, support_sdiff_support_subset_support_add, toMultiset, totalDegree_add, totalDegree_eq
-/
theorem totalDegree_add_eq_left_of_totalDegree_lt {p q : MvPolynomial σ R}
    (h : q.totalDegree < p.totalDegree) : (p + q).totalDegree = p.totalDegree := by
  classical
    apply le_antisymm
    · rw [← max_eq_left_of_lt h]
      exact totalDegree_add p q
    by_cases hp : p = 0
    · simp [hp]
    obtain ⟨b, hb₁, hb₂⟩ :=
      p.support.exists_mem_eq_sup (by simpa) fun m : σ ->₀ Nat => Multiset.card (toMultiset m)
    have hb : b ∉ q.support := by
      contrapose! h
      rw [totalDegree_eq p]; rw [hb₂]; rw [totalDegree_eq]
      apply Finset.le_sup h
    have hbb : b in (p + q).support := by
      apply support_sdiff_support_subset_support_add
      rw [Finset.mem_sdiff]
      exact ⟨hb₁, hb⟩
    rw [totalDegree_eq]; rw [hb₂]; rw [totalDegree_eq]
    exact Finset.le_sup (f := fun m => Multiset.card (Finsupp.toMultiset m)) hbb

/--
theorem `totalDegree_add_eq_right_of_totalDegree_lt` / 定理 `totalDegree_add_eq_right_of_totalDegree_lt`

English:
theorem totalDegree_add_eq_right_of_totalDegree_lt
  statement: {p q : MvPolynomial σ R}
  proof: by
  rw [add_comm]; rw [totalDegree_add_eq_left_of_totalDegree_lt h]

中文:
定理 totalDegree_add_eq_right_of_totalDegree_lt
  结论: {p q : 多元多项式 σ R}
  证明: by
  rw [add_comm]; rw [totalDegree_add_eq_left_of_totalDegree_lt h]

Depends on / 依赖: add_comm, totalDegree_add_eq_left_of_totalDegree_lt
-/
theorem totalDegree_add_eq_right_of_totalDegree_lt {p q : MvPolynomial σ R}
    (h : q.totalDegree < p.totalDegree) : (q + p).totalDegree = p.totalDegree := by
  rw [add_comm]; rw [totalDegree_add_eq_left_of_totalDegree_lt h]

/--
theorem `totalDegree_mul` / 定理 `totalDegree_mul`

English:
theorem totalDegree_mul
  given: (a b : MvPolynomial σ R)
  proof: sup_support_coeff_mul_le (fun _ _ => by simp [Finsupp.sum_add_index']) _ _

中文:
定理 totalDegree_mul
  条件: (a b : 多元多项式 σ R)
  证明: sup_support_coeff_mul_le (fun _ _ => by simp [Finsupp.sum_add_index']) _ _

Depends on / 依赖: Finsupp, Finsupp.sum_add_index, sum_add_index, sup_support_coeff_mul_le
-/
theorem totalDegree_mul (a b : MvPolynomial σ R) :
    (a * b).totalDegree <= a.totalDegree + b.totalDegree :=
  sup_support_coeff_mul_le (fun _ _ => by simp [Finsupp.sum_add_index']) _ _

/--
theorem `totalDegree_smul_le` / 定理 `totalDegree_smul_le`

English:
theorem totalDegree_smul_le
  given: [CommSemiring S] [DistribMulAction R S] (a : R) (f : MvPolynomial σ S)
  proof: Finset.sup_mono support_smul

中文:
定理 totalDegree_smul_le
  条件: [交换半环 S] [分配乘法作用 R S] (a : R) (f : 多元多项式 σ S)
  证明: Finset.sup_mono support_smul

Depends on / 依赖: Finset, Finset.sup_mono, sup_mono, support_smul
-/
theorem totalDegree_smul_le [CommSemiring S] [DistribMulAction R S] (a : R) (f : MvPolynomial σ S) :
    (a • f).totalDegree <= f.totalDegree :=
  Finset.sup_mono support_smul

/--
theorem `totalDegree_pow` / 定理 `totalDegree_pow`

English:
theorem totalDegree_pow
  given: (a : MvPolynomial σ R) (n : Nat)
  proof: by
  rw [Finset.pow_eq_prod_const]; rw [← Nat.nsmul_eq_mul]; rw [Finset.nsmul_eq_sum_const]
  refine supDegree_prod_le rfl (fun _ _ => ?_)
  exact Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

@[simp]

中文:
定理 totalDegree_pow
  条件: (a : 多元多项式 σ R) (n : 自然数)
  证明: by
  rw [Finset.pow_eq_prod_const]; rw [← Nat.nsmul_eq_mul]; rw [Finset.nsmul_eq_sum_const]
  refine supDegree_prod_le rfl (fun _ _ => ?_)
  exact Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

@[simp]

Depends on / 依赖: Finset, Finset.nsmul_eq_sum_const, Finset.pow_eq_prod_const, Finsupp, Finsupp.sum_add_index, Nat.nsmul_eq_mul, nsmul_eq_mul, nsmul_eq_sum_const, pow_eq_prod_const, sum_add_index, supDegree_prod_le
-/
theorem totalDegree_pow (a : MvPolynomial σ R) (n : Nat) :
    (a ^ n).totalDegree <= n * a.totalDegree := by
  rw [Finset.pow_eq_prod_const]; rw [← Nat.nsmul_eq_mul]; rw [Finset.nsmul_eq_sum_const]
  refine supDegree_prod_le rfl (fun _ _ => ?_)
  exact Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

@[simp]
/--
theorem `totalDegree_monomial` / 定理 `totalDegree_monomial`

English:
theorem totalDegree_monomial
  given: (s : σ ->₀ Nat) {c : R} (hc : c != 0)
  proof: by
  classical simp [totalDegree, support_monomial, if_neg hc]

中文:
定理 totalDegree_monomial
  条件: (s : σ ->₀ 自然数) {c : R} (hc : c != 0)
  证明: by
  classical simp [totalDegree, support_monomial, if_neg hc]

Depends on / 依赖: classical, if_neg, support_monomial, totalDegree
-/
theorem totalDegree_monomial (s : σ ->₀ Nat) {c : R} (hc : c != 0) :
    (monomial s c : MvPolynomial σ R).totalDegree = s.sum fun _ e => e := by
  classical simp [totalDegree, support_monomial, if_neg hc]

/--
theorem `totalDegree_monomial_le` / 定理 `totalDegree_monomial_le`

English:
theorem totalDegree_monomial_le
  given: (s : σ ->₀ Nat) (c : R)
  proof: by
  if hc : c = 0 then
    simp only [hc, map_zero, totalDegree_zero, zero_le]
  else
    rw [totalDegree_monomial _ hc]; rw [Function.id_def]

@[simp]

中文:
定理 totalDegree_monomial_le
  条件: (s : σ ->₀ 自然数) (c : R)
  证明: by
  if hc : c = 0 then
    simp only [hc, map_zero, totalDegree_zero, zero_le]
  else
    rw [totalDegree_monomial _ hc]; rw [Function.id_def]

@[simp]

Depends on / 依赖: Function, Function.id_def, id_def, map_zero, totalDegree_monomial, totalDegree_zero, zero_le
-/
theorem totalDegree_monomial_le (s : σ ->₀ Nat) (c : R) :
    (monomial s c).totalDegree <= s.sum fun _ => id := by
  if hc : c = 0 then
    simp only [hc, map_zero, totalDegree_zero, zero_le]
  else
    rw [totalDegree_monomial _ hc]; rw [Function.id_def]

@[simp]
/--
theorem `totalDegree_X_pow` / 定理 `totalDegree_X_pow`

English:
theorem totalDegree_X_pow
  given: [Nontrivial R] (s : σ) (n : Nat)
  proof: by simp [X_pow_eq_monomial, one_ne_zero]

中文:
定理 totalDegree_X_pow
  条件: [非平凡 R] (s : σ) (n : 自然数)
  证明: by simp [X_pow_eq_monomial, one_ne_zero]

Depends on / 依赖: X_pow_eq_monomial, one_ne_zero
-/
theorem totalDegree_X_pow [Nontrivial R] (s : σ) (n : Nat) :
    (X s ^ n : MvPolynomial σ R).totalDegree = n := by simp [X_pow_eq_monomial, one_ne_zero]

/--
theorem `totalDegree_list_prod` / 定理 `totalDegree_list_prod`

English:
theorem totalDegree_list_prod
  given: (l : List (MvPolynomial σ R))
  proof: l.apply_prod_le_sum_map _ totalDegree_one.le totalDegree_mul

中文:
定理 totalDegree_list_prod
  条件: (l : 列表 (多元多项式 σ R))
  证明: l.apply_prod_le_sum_map _ totalDegree_one.le totalDegree_mul

Depends on / 依赖: apply_prod_le_sum_map, l.apply_prod_le_sum_map, totalDegree_mul, totalDegree_one, totalDegree_one.le
-/
theorem totalDegree_list_prod (l : List (MvPolynomial σ R)) :
    l.prod.totalDegree <= (l.map MvPolynomial.totalDegree).sum :=
  l.apply_prod_le_sum_map _ totalDegree_one.le totalDegree_mul

/--
theorem `totalDegree_multiset_prod` / 定理 `totalDegree_multiset_prod`

English:
theorem totalDegree_multiset_prod
  given: (s : Multiset (MvPolynomial σ R))
  proof: s.apply_prod_le_sum_map _ totalDegree_one.le totalDegree_mul

中文:
定理 totalDegree_multiset_prod
  条件: (s : Multiset (多元多项式 σ R))
  证明: s.apply_prod_le_sum_map _ totalDegree_one.le totalDegree_mul

Depends on / 依赖: apply_prod_le_sum_map, s.apply_prod_le_sum_map, totalDegree_mul, totalDegree_one, totalDegree_one.le
-/
theorem totalDegree_multiset_prod (s : Multiset (MvPolynomial σ R)) :
    s.prod.totalDegree <= (s.map MvPolynomial.totalDegree).sum :=
  s.apply_prod_le_sum_map _ totalDegree_one.le totalDegree_mul

/--
theorem `totalDegree_finsetProd` / 定理 `totalDegree_finsetProd`

English:
theorem totalDegree_finsetProd
  given: {ι : Type*} (s : Finset ι) (f : ι -> MvPolynomial σ R)
  proof: s.apply_prod_le_sum_apply _ totalDegree_one.le totalDegree_mul

@[deprecated (since := "2026-04-08")] alias totalDegree_finset_prod := totalDegree_finsetProd

中文:
定理 totalDegree_finsetProd
  条件: {ι : 类型} (s : 有限集 ι) (f : ι -> 多元多项式 σ R)
  证明: s.apply_prod_le_sum_apply _ totalDegree_one.le totalDegree_mul

@[deprecated (since := "2026-04-08")] alias totalDegree_finset_prod := totalDegree_finsetProd

Depends on / 依赖: apply_prod_le_sum_apply, s.apply_prod_le_sum_apply, totalDegree_mul, totalDegree_one, totalDegree_one.le
-/
theorem totalDegree_finsetProd {ι : Type*} (s : Finset ι) (f : ι -> MvPolynomial σ R) :
    (s.prod f).totalDegree <= ∑ i in s, (f i).totalDegree :=
  s.apply_prod_le_sum_apply _ totalDegree_one.le totalDegree_mul

@[deprecated (since := "2026-04-08")] alias totalDegree_finset_prod := totalDegree_finsetProd

/--
theorem `totalDegree_finsetSum` / 定理 `totalDegree_finsetSum`

English:
theorem totalDegree_finsetSum
  given: {ι : Type*} (s : Finset ι) (f : ι -> MvPolynomial σ R)
  proof: by
  induction s using Finset.cons_induction with
  | empty => exact zero_le
  | cons a s has hind =>
    rw [Finset.sum_cons]; rw [Finset.sup_cons]
    exact (MvPolynomial.totalDegree_add _ _).trans (max_le_max le_rfl hind)

@[deprecated (since := "2026-04-08")] alias totalDegree_finset_sum := totalDegree_finsetSum

中文:
定理 totalDegree_finsetSum
  条件: {ι : 类型} (s : 有限集 ι) (f : ι -> 多元多项式 σ R)
  证明: by
  induction s using Finset.cons_induction with
  | empty => exact zero_le
  | cons a s has hind =>
    rw [Finset.sum_cons]; rw [Finset.sup_cons]
    exact (MvPolynomial.totalDegree_add _ _).trans (max_le_max le_rfl hind)

@[deprecated (since := "2026-04-08")] alias totalDegree_finset_sum := totalDegree_finsetSum

Depends on / 依赖: Finset, Finset.cons_induction, Finset.sum_cons, Finset.sup_cons, MvPolynomial, MvPolynomial.totalDegree_add, cons_induction, le_rfl, max_le_max, sum_cons, sup_cons, totalDegree_add, zero_le
-/
theorem totalDegree_finsetSum {ι : Type*} (s : Finset ι) (f : ι -> MvPolynomial σ R) :
    (s.sum f).totalDegree <= Finset.sup s fun i => (f i).totalDegree := by
  induction s using Finset.cons_induction with
  | empty => exact zero_le
  | cons a s has hind =>
    rw [Finset.sum_cons]; rw [Finset.sup_cons]
    exact (MvPolynomial.totalDegree_add _ _).trans (max_le_max le_rfl hind)

@[deprecated (since := "2026-04-08")] alias totalDegree_finset_sum := totalDegree_finsetSum

/--
lemma `totalDegree_finsetSum_le` / 引理 `totalDegree_finsetSum_le`

English:
lemma totalDegree_finsetSum_le
  statement: {ι : Type*} {s : Finset ι} {f : ι -> MvPolynomial σ R} {d : Nat}
  proof: (totalDegree_finsetSum ..).trans Finset.sup_le hf

中文:
引理 totalDegree_finsetSum_le
  结论: {ι : 类型} {s : 有限集 ι} {f : ι -> 多元多项式 σ R} {d : 自然数}
  证明: (totalDegree_finsetSum ..).trans Finset.sup_le hf

Depends on / 依赖: Finset, Finset.sup_le, sup_le, totalDegree_finsetSum
-/
lemma totalDegree_finsetSum_le {ι : Type*} {s : Finset ι} {f : ι -> MvPolynomial σ R} {d : Nat}
    (hf : forall i in s, (f i).totalDegree <= d) : (s.sum f).totalDegree <= d :=
(totalDegree_finsetSum ..).trans Finset.sup_le hf

/--
lemma `degreeOf_le_totalDegree` / 引理 `degreeOf_le_totalDegree`

English:
lemma degreeOf_le_totalDegree
  given: (f : MvPolynomial σ R) (i : σ)
  statement: f.degreeOf i <= f.totalDegree
  proof: degreeOf_le_iff.mpr fun d hd => (eq_or_ne (d i) 0).elim (by lia) fun h =>
    (Finset.single_le_sum (by lia) <| Finsupp.mem_support_iff.mpr h).trans
    (le_totalDegree hd)

中文:
引理 degreeOf_le_totalDegree
  条件: (f : 多元多项式 σ R) (i : σ)
  结论: f.degreeOf i <= f.totalDegree
  证明: degreeOf_le_iff.mpr fun d hd => (eq_or_ne (d i) 0).elim (by lia) fun h =>
    (Finset.single_le_sum (by lia) <| Finsupp.mem_support_iff.mpr h).trans
    (le_totalDegree hd)

Depends on / 依赖: Finset, Finset.single_le_sum, Finsupp, Finsupp.mem_support_iff.mpr, degreeOf_le_iff, degreeOf_le_iff.mpr, eq_or_ne, le_totalDegree, mem_support_iff, single_le_sum
-/
lemma degreeOf_le_totalDegree (f : MvPolynomial σ R) (i : σ) : f.degreeOf i <= f.totalDegree :=
  degreeOf_le_iff.mpr fun d hd => (eq_or_ne (d i) 0).elim (by lia) fun h =>
    (Finset.single_le_sum (by lia) <| Finsupp.mem_support_iff.mpr h).trans
    (le_totalDegree hd)

/--
theorem `exists_degree_lt` / 定理 `exists_degree_lt`

English:
theorem exists_degree_lt
  statement: [Fintype σ] (f : MvPolynomial σ R) (n : Nat)
  proof: by
  contrapose! h
  calc
    n * Fintype.card σ = ∑ _s : σ, n := by
      rw [Finset.sum_const]; rw [Nat.nsmul_eq_mul]; rw [mul_comm]; rw [Finset.card_univ]
    _ <= ∑ s, d s := Finset.sum_le_sum fun s _ => h s
    _ <= d.sum fun _ e => e := by
      rw [Finsupp.sum_fintype]
      intros
      rfl
    _ <= f.totalDegree := le_totalDegree hd

中文:
定理 存在_degree_lt
  结论: [有限类型 σ] (f : 多元多项式 σ R) (n : 自然数)
  证明: by
  contrapose! h
  calc
    n * Fintype.card σ = ∑ _s : σ, n := by
      rw [Finset.sum_const]; rw [Nat.nsmul_eq_mul]; rw [mul_comm]; rw [Finset.card_univ]
    _ <= ∑ s, d s := Finset.sum_le_sum fun s _ => h s
    _ <= d.sum fun _ e => e := by
      rw [Finsupp.sum_fintype]
      intros
      rfl
    _ <= f.totalDegree := le_totalDegree hd

Depends on / 依赖: Finset, Finset.card_univ, Finset.sum_const, Finset.sum_le_sum, Finsupp, Finsupp.sum_fintype, Fintype, Fintype.card, Nat.nsmul_eq_mul, card_univ, contrapose, d.sum, f.totalDegree, intros, le_totalDegree, mul_comm, nsmul_eq_mul, sum_const, sum_fintype, sum_le_sum
-/
theorem exists_degree_lt [Fintype σ] (f : MvPolynomial σ R) (n : Nat)
    (h : f.totalDegree < n * Fintype.card σ) {d : σ ->₀ Nat} (hd : d in f.support) : exists i, d i < n := by
  contrapose! h
  calc
    n * Fintype.card σ = ∑ _s : σ, n := by
      rw [Finset.sum_const]; rw [Nat.nsmul_eq_mul]; rw [mul_comm]; rw [Finset.card_univ]
    _ <= ∑ s, d s := Finset.sum_le_sum fun s _ => h s
    _ <= d.sum fun _ e => e := by
      rw [Finsupp.sum_fintype]
      intros
      rfl
    _ <= f.totalDegree := le_totalDegree hd

/--
theorem `coeff_eq_zero_of_totalDegree_lt` / 定理 `coeff_eq_zero_of_totalDegree_lt`

English:
theorem coeff_eq_zero_of_totalDegree_lt
  statement: {f : MvPolynomial σ R} {d : σ ->₀ Nat}
  proof: by
  rw [totalDegree]; rw [Finset.sup_lt_iff] at h
  · specialize h d
    rw [mem_support_iff] at h
    refine not_not.mp (mt h ?_)
    exact lt_irrefl _
  · exact lt_of_le_of_lt (Nat.zero_le _) h

中文:
定理 coeff_eq_zero_of_totalDegree_lt
  结论: {f : 多元多项式 σ R} {d : σ ->₀ 自然数}
  证明: by
  rw [totalDegree]; rw [Finset.sup_lt_iff] at h
  · specialize h d
    rw [mem_support_iff] at h
    refine not_not.mp (mt h ?_)
    exact lt_irrefl _
  · exact lt_of_le_of_lt (Nat.zero_le _) h

Depends on / 依赖: Finset, Finset.sup_lt_iff, Nat.zero_le, lt_irrefl, lt_of_le_of_lt, mem_support_iff, not_not, not_not.mp, specialize, sup_lt_iff, totalDegree, zero_le
-/
theorem coeff_eq_zero_of_totalDegree_lt {f : MvPolynomial σ R} {d : σ ->₀ Nat}
    (h : f.totalDegree < ∑ i in d.support, d i) : coeff d f = 0 := by
  rw [totalDegree]; rw [Finset.sup_lt_iff] at h
  · specialize h d
    rw [mem_support_iff] at h
    refine not_not.mp (mt h ?_)
    exact lt_irrefl _
  · exact lt_of_le_of_lt (Nat.zero_le _) h

/--
theorem `totalDegree_eq_zero_iff_eq_C` / 定理 `totalDegree_eq_zero_iff_eq_C`

English:
theorem totalDegree_eq_zero_iff_eq_C
  given: {p : MvPolynomial σ R}
  proof: by
  constructor <;> intro h
  · ext m; classical rw [coeff_C]; split_ifs with hm; · rw [← hm]
    apply coeff_eq_zero_of_totalDegree_lt; rw [h]
    exact Finset.sum_pos (fun i hi => Nat.pos_of_ne_zero <| Finsupp.mem_support_iff.mp hi)
      (Finsupp.support_nonempty_iff.mpr <| Ne.symm hm)
  · rw [h, totalDegree_C]

中文:
定理 totalDegree_eq_zero_iff_eq_C
  条件: {p : 多元多项式 σ R}
  证明: by
  constructor <;> intro h
  · ext m; classical rw [coeff_C]; split_ifs with hm; · rw [← hm]
    apply coeff_eq_zero_of_totalDegree_lt; rw [h]
    exact Finset.sum_pos (fun i hi => Nat.pos_of_ne_zero <| Finsupp.mem_support_iff.mp hi)
      (Finsupp.support_nonempty_iff.mpr <| Ne.symm hm)
  · rw [h, totalDegree_C]

Depends on / 依赖: Finset, Finset.sum_pos, Finsupp, Finsupp.mem_support_iff.mp, Finsupp.support_nonempty_iff.mpr, Nat.pos_of_ne_zero, Ne.symm, classical, coeff_C, coeff_eq_zero_of_totalDegree_lt, mem_support_iff, pos_of_ne_zero, split_ifs, sum_pos, support_nonempty_iff, totalDegree_C
-/
theorem totalDegree_eq_zero_iff_eq_C {p : MvPolynomial σ R} :
    p.totalDegree = 0 ↔ p = C (p.coeff 0) := by
  constructor <;> intro h
  · ext m; classical rw [coeff_C]; split_ifs with hm; · rw [← hm]
    apply coeff_eq_zero_of_totalDegree_lt; rw [h]
    exact Finset.sum_pos (fun i hi => Nat.pos_of_ne_zero <| Finsupp.mem_support_iff.mp hi)
      (Finsupp.support_nonempty_iff.mpr <| Ne.symm hm)
  · rw [h, totalDegree_C]

/--
theorem `totalDegree_rename_le` / 定理 `totalDegree_rename_le`

English:
theorem totalDegree_rename_le
  given: (f : σ -> τ) (p : MvPolynomial σ R)
  proof: Finset.sup_le fun b h => by
    classical
    have h' := Finsupp.mapDomain_support h
    rw [Finset.mem_image] at h'
    rcases h' with ⟨s, hs, rfl⟩
    exact (sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)).trans_le (le_totalDegree hs)

中文:
定理 totalDegree_rename_le
  条件: (f : σ -> τ) (p : 多元多项式 σ R)
  证明: Finset.sup_le fun b h => by
    classical
    have h' := Finsupp.mapDomain_support h
    rw [Finset.mem_image] at h'
    rcases h' with ⟨s, hs, rfl⟩
    exact (sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)).trans_le (le_totalDegree hs)

Depends on / 依赖: Finset, Finset.mem_image, Finset.sup_le, Finsupp, Finsupp.mapDomain_support, classical, le_totalDegree, mapDomain_support, mem_image, sum_mapDomain_index, sup_le, trans_le
-/
theorem totalDegree_rename_le (f : σ -> τ) (p : MvPolynomial σ R) :
    (rename f p).totalDegree <= p.totalDegree :=
  Finset.sup_le fun b h => by
    classical
    have h' := Finsupp.mapDomain_support h
    rw [Finset.mem_image] at h'
    rcases h' with ⟨s, hs, rfl⟩
    exact (sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)).trans_le (le_totalDegree hs)

/--
lemma `totalDegree_renameEquiv` / 引理 `totalDegree_renameEquiv`

English:
lemma totalDegree_renameEquiv
  given: (f : σ ≃ τ) (p : MvPolynomial σ R)
  proof: (totalDegree_rename_le f p).antisymm (le_trans (by simp) (totalDegree_rename_le f.symm _))

中文:
引理 totalDegree_renameEquiv
  条件: (f : σ ≃ τ) (p : 多元多项式 σ R)
  证明: (totalDegree_rename_le f p).antisymm (le_trans (by simp) (totalDegree_rename_le f.symm _))

Depends on / 依赖: antisymm, f.symm, le_trans, totalDegree_rename_le
-/
lemma totalDegree_renameEquiv (f : σ ≃ τ) (p : MvPolynomial σ R) :
    (renameEquiv R f p).totalDegree = p.totalDegree :=
  (totalDegree_rename_le f p).antisymm (le_trans (by simp) (totalDegree_rename_le f.symm _))

end TotalDegree

section degreesLE
variable {s t : Multiset σ}

variable (R σ s) in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `degreesLE` / `degreesLE` 的定义

English:
definition degreesLE
  signature: : Submodule R (MvPolynomial σ R) where
  body: {p | p.degrees <= s}
  add_mem' {a b} ha hb := by classical exact degrees_add_le.trans (sup_le ha hb)
  zero_mem' := by simp
  smul_mem' c {x} hx := by
    dsimp
    rw [Algebra.smul_def]
    refine degrees_mul_le.trans ?_
    simpa [degrees_C] using hx

中文:
定义 degreesLE
  签名: : 子模 R (多元多项式 σ R) where
  定义体: {p | p.degrees <= s}
  add_mem' {a b} ha hb := by classical exact degrees_add_le.trans (sup_le ha hb)
  zero_mem' := by simp
  smul_mem' c {x} hx := by
    dsimp
    rw [Algebra.smul_def]
    refine degrees_mul_le.trans ?_
    simpa [degrees_C] using hx

Depends on / 依赖: degrees, p.degrees
-/
def degreesLE : Submodule R (MvPolynomial σ R) where
  carrier := {p | p.degrees <= s}
  add_mem' {a b} ha hb := by classical exact degrees_add_le.trans (sup_le ha hb)
  zero_mem' := by simp
  smul_mem' c {x} hx := by
    dsimp
    rw [Algebra.smul_def]
    refine degrees_mul_le.trans ?_
    simpa [degrees_C] using hx

/--
lemma `mem_degreesLE` / 引理 `mem_degreesLE`

English:
lemma mem_degreesLE
  statement: p in degreesLE R σ s ↔ p.degrees <= s
  proof: Iff.rfl

中文:
引理 mem_degreesLE
  结论: p in degreesLE R σ s ↔ p.degrees <= s
  证明: Iff.rfl
-/
@[simp] lemma mem_degreesLE : p in degreesLE R σ s ↔ p.degrees <= s := Iff.rfl

variable (s t) in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `degreesLE_add` / 引理 `degreesLE_add`

English:
lemma degreesLE_add
  statement: degreesLE R σ (s + t) = degreesLE R σ s * degreesLE R σ t
  proof: by
  classical
  rw [le_antisymm_iff]; rw [Submodule.mul_le]
  refine ⟨fun x hx => x.as_sum ▸ sum_mem fun i hi => ?_,
    fun x hx y hy => degrees_mul_le.trans (add_le_add hx hy)⟩
  replace hi : i.toMultiset <= s + t := (Finset.le_sup hi).trans hx
  let a := (i.toMultiset - t).toFinsupp
  let b := (i.toMultiset ⊓ t).toFinsupp
  have : a + b = i := Multiset.toFinsupp.symm.injective (by simp [a, b, Multiset.sub_add_inter])
  have ha : a.toMultiset <= s := by simpa [a, add_comm (a := t)] using hi
  have hb : b.toMultiset <= t := by simp [b, Multiset.inter_le_right]
  rw [show monomial i (x.coeff i) = monomial a (x.coeff i) * monomial b 1 by simp [this]]
  exact Submodule.mul_mem_mul ((degrees_monomial _ _).trans ha) ((degrees_monomial _ _).trans hb)

中文:
引理 degreesLE_add
  结论: degreesLE R σ (s + t) = degreesLE R σ s * degreesLE R σ t
  证明: by
  classical
  rw [le_antisymm_iff]; rw [Submodule.mul_le]
  refine ⟨fun x hx => x.as_sum ▸ sum_mem fun i hi => ?_,
    fun x hx y hy => degrees_mul_le.trans (add_le_add hx hy)⟩
  replace hi : i.toMultiset <= s + t := (Finset.le_sup hi).trans hx
  let a := (i.toMultiset - t).toFinsupp
  let b := (i.toMultiset ⊓ t).toFinsupp
  have : a + b = i := Multiset.toFinsupp.symm.injective (by simp [a, b, Multiset.sub_add_inter])
  have ha : a.toMultiset <= s := by simpa [a, add_comm (a := t)] using hi
  have hb : b.toMultiset <= t := by simp [b, Multiset.inter_le_right]
  rw [show monomial i (x.coeff i) = monomial a (x.coeff i) * monomial b 1 by simp [this]]
  exact Submodule.mul_mem_mul ((degrees_monomial _ _).trans ha) ((degrees_monomial _ _).trans hb)

Depends on / 依赖: Finset, Finset.le_sup, Multiset, Multiset.sub_add_inter, Multiset.toFinsupp.symm.injective, Submodule, Submodule.mul_le, a.toMultiset, add_comm, add_le_add, as_sum, b.toMultise, classical, degrees_mul_le, degrees_mul_le.trans, i.toMultiset, injective, le_antisymm_iff, le_sup, mul_le
-/
lemma degreesLE_add : degreesLE R σ (s + t) = degreesLE R σ s * degreesLE R σ t := by
  classical
  rw [le_antisymm_iff]; rw [Submodule.mul_le]
  refine ⟨fun x hx => x.as_sum ▸ sum_mem fun i hi => ?_,
    fun x hx y hy => degrees_mul_le.trans (add_le_add hx hy)⟩
  replace hi : i.toMultiset <= s + t := (Finset.le_sup hi).trans hx
  let a := (i.toMultiset - t).toFinsupp
  let b := (i.toMultiset ⊓ t).toFinsupp
  have : a + b = i := Multiset.toFinsupp.symm.injective (by simp [a, b, Multiset.sub_add_inter])
  have ha : a.toMultiset <= s := by simpa [a, add_comm (a := t)] using hi
  have hb : b.toMultiset <= t := by simp [b, Multiset.inter_le_right]
  rw [show monomial i (x.coeff i) = monomial a (x.coeff i) * monomial b 1 by simp [this]]
  exact Submodule.mul_mem_mul ((degrees_monomial _ _).trans ha) ((degrees_monomial _ _).trans hb)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `degreesLE_zero` / 引理 `degreesLE_zero`

English:
lemma degreesLE_zero
  statement: degreesLE R σ 0 = 1
  proof: by
  refine le_antisymm (fun x hx => ?_) (by simp)
  simp only [mem_degreesLE, nonpos_iff_eq_zero] at hx
  have := (totalDegree_eq_zero_iff_eq_C (p := x)).mp
    (Nat.eq_zero_of_le_zero (x.totalDegree_le_degrees_card.trans (by simp [hx])))
  exact ⟨x.coeff 0, by simp [Algebra.smul_def, ← this]⟩

中文:
引理 degreesLE_zero
  结论: degreesLE R σ 0 = 1
  证明: by
  refine le_antisymm (fun x hx => ?_) (by simp)
  simp only [mem_degreesLE, nonpos_iff_eq_zero] at hx
  have := (totalDegree_eq_zero_iff_eq_C (p := x)).mp
    (Nat.eq_zero_of_le_zero (x.totalDegree_le_degrees_card.trans (by simp [hx])))
  exact ⟨x.coeff 0, by simp [Algebra.smul_def, ← this]⟩
-/
@[simp] lemma degreesLE_zero : degreesLE R σ 0 = 1 := by
  refine le_antisymm (fun x hx => ?_) (by simp)
  simp only [mem_degreesLE, nonpos_iff_eq_zero] at hx
  have := (totalDegree_eq_zero_iff_eq_C (p := x)).mp
    (Nat.eq_zero_of_le_zero (x.totalDegree_le_degrees_card.trans (by simp [hx])))
  exact ⟨x.coeff 0, by simp [Algebra.smul_def, ← this]⟩

variable (s) in
/--
lemma `degreesLE_nsmul` / 引理 `degreesLE_nsmul`

English:
lemma degreesLE_nsmul
  statement: forall n, degreesLE R σ (n • s) = degreesLE R σ s ^ n

中文:
引理 degreesLE_nsmul
  结论: 对任意 n, degreesLE R σ (n • s) = degreesLE R σ s ^ n
-/
lemma degreesLE_nsmul : forall n, degreesLE R σ (n • s) = degreesLE R σ s ^ n
  | 0 => by simp
  | k + 1 => by simp only [pow_succ, degreesLE_nsmul, degreesLE_add, add_smul, one_smul]

end degreesLE
end CommSemiring

end MvPolynomial
