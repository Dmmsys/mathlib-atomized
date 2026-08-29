/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Support
public import Mathlib.Algebra.Polynomial.Degree.Operations

/-!
# Degree and support of univariate polynomials

## Main results
* `Polynomial.as_sum_support`: write `p : R[X]` as a sum over its support
* `Polynomial.as_sum_range`: write `p : R[X]` as a sum over `{0, ..., natDegree p}`
* `Polynomial.natDegree_mem_support_of_nonzero`: `natDegree p ∈ support p` if `p ≠ 0`
-/

public section

noncomputable section

open Finsupp Finset

open Polynomial

namespace Polynomial

universe u v

variable {R : Type u} {S : Type v} {a b c d : R} {n m : Nat}

section Semiring

variable [Semiring R] {p q r : R[X]}

/--
theorem `supDegree_eq_natDegree` / 定理 `supDegree_eq_natDegree`

English:
theorem supDegree_eq_natDegree
  given: (p : R[X])
  statement: p.toFinsupp.supDegree id = p.natDegree
  proof: by
  obtain rfl | h := eq_or_ne p 0
  · simp
  apply WithBot.coe_injective
  rw [← AddMonoidAlgebra.supDegree_withBot_some_comp]; rw [Function.comp_id]; rw [supDegree_eq_degree]; rw [degree_eq_natDegree h]; rw [Nat.cast_withBot]
  rwa [support_toFinsupp, nonempty_iff_ne_empty, Ne, support_eq_empty]

中文:
定理 supDegree_eq_natDegree
  条件: (p : R[X])
  结论: p.toFinsupp.supDegree id = p.natDegree
  证明: by
  obtain rfl | h := eq_or_ne p 0
  · simp
  apply WithBot.coe_injective
  rw [← AddMonoidAlgebra.supDegree_withBot_some_comp]; rw [Function.comp_id]; rw [supDegree_eq_degree]; rw [degree_eq_natDegree h]; rw [Nat.cast_withBot]
  rwa [support_toFinsupp, nonempty_iff_ne_empty, Ne, support_eq_empty]

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.supDegree_withBot_some_comp, Function, Function.comp_id, Nat.cast_withBot, WithBot, WithBot.coe_injective, cast_withBot, coe_injective, comp_id, degree_eq_natDegree, eq_or_ne, nonempty_iff_ne_empty, supDegree_eq_degree, supDegree_withBot_some_comp, support_eq_empty, support_toFinsupp
-/
theorem supDegree_eq_natDegree (p : R[X]) : p.toFinsupp.supDegree id = p.natDegree := by
  obtain rfl | h := eq_or_ne p 0
  · simp
  apply WithBot.coe_injective
  rw [← AddMonoidAlgebra.supDegree_withBot_some_comp]; rw [Function.comp_id]; rw [supDegree_eq_degree]; rw [degree_eq_natDegree h]; rw [Nat.cast_withBot]
  rwa [support_toFinsupp, nonempty_iff_ne_empty, Ne, support_eq_empty]

/--
theorem `le_natDegree_of_mem_supp` / 定理 `le_natDegree_of_mem_supp`

English:
theorem le_natDegree_of_mem_supp
  given: (a : Nat)
  statement: a in p.support -> a <= natDegree p
  proof: le_natDegree_of_ne_zero ∘ mem_support_iff.mp

中文:
定理 le_natDegree_of_mem_supp
  条件: (a : 自然数)
  结论: a in p.support -> a <= natDegree p
  证明: le_natDegree_of_ne_zero ∘ mem_support_iff.mp

Depends on / 依赖: le_natDegree_of_ne_zero, mem_support_iff, mem_support_iff.mp
-/
theorem le_natDegree_of_mem_supp (a : Nat) : a in p.support -> a <= natDegree p :=
  le_natDegree_of_ne_zero ∘ mem_support_iff.mp

/--
theorem `supp_subset_range` / 定理 `supp_subset_range`

English:
theorem supp_subset_range
  given: (h : natDegree p < m)
  statement: p.support subseteq Finset.range m
  proof: fun _n hn =>
mem_range.2 (le_natDegree_of_mem_supp _ hn).trans_lt h

中文:
定理 supp_subset_range
  条件: (h : natDegree p < m)
  结论: p.support subseteq 有限集.range m
  证明: fun _n hn =>
mem_range.2 (le_natDegree_of_mem_supp _ hn).trans_lt h
-/
theorem supp_subset_range (h : natDegree p < m) : p.support subseteq Finset.range m := fun _n hn =>
mem_range.2 (le_natDegree_of_mem_supp _ hn).trans_lt h

/--
theorem `supp_subset_range_natDegree_succ` / 定理 `supp_subset_range_natDegree_succ`

English:
theorem supp_subset_range_natDegree_succ
  statement: p.support subseteq Finset.range (natDegree p + 1)
  proof: supp_subset_range (Nat.lt_succ_self _)

中文:
定理 supp_subset_range_natDegree_succ
  结论: p.support subseteq 有限集.range (natDegree p + 1)
  证明: supp_subset_range (Nat.lt_succ_self _)

Depends on / 依赖: Nat.lt_succ_self, lt_succ_self, supp_subset_range
-/
theorem supp_subset_range_natDegree_succ : p.support subseteq Finset.range (natDegree p + 1) :=
  supp_subset_range (Nat.lt_succ_self _)

/--
theorem `as_sum_support` / 定理 `as_sum_support`

English:
theorem as_sum_support
  given: (p : R[X])
  statement: p = ∑ i in p.support, monomial i (p.coeff i)
  proof: (sum_monomial_eq p).symm

中文:
定理 as_sum_support
  条件: (p : R[X])
  结论: p = ∑ i in p.support, monomial i (p.coeff i)
  证明: (sum_monomial_eq p).symm

Depends on / 依赖: sum_monomial_eq
-/
theorem as_sum_support (p : R[X]) : p = ∑ i in p.support, monomial i (p.coeff i) :=
  (sum_monomial_eq p).symm

/--
theorem `as_sum_support_C_mul_X_pow` / 定理 `as_sum_support_C_mul_X_pow`

English:
theorem as_sum_support_C_mul_X_pow
  given: (p : R[X])
  statement: p = ∑ i in p.support, C (p.coeff i) * X ^ i
  proof: _root_.trans p.as_sum_support by simp only [C_mul_X_pow_eq_monomial]

中文:
定理 as_sum_support_C_mul_X_pow
  条件: (p : R[X])
  结论: p = ∑ i in p.support, C (p.coeff i) * X ^ i
  证明: _root_.trans p.as_sum_support by simp only [C_mul_X_pow_eq_monomial]

Depends on / 依赖: C_mul_X_pow_eq_monomial, _root_, _root_.trans, as_sum_support, p.as_sum_support
-/
theorem as_sum_support_C_mul_X_pow (p : R[X]) : p = ∑ i in p.support, C (p.coeff i) * X ^ i :=
_root_.trans p.as_sum_support by simp only [C_mul_X_pow_eq_monomial]

/--
theorem `sum_over_range'` / 定理 `sum_over_range'`

English:
theorem sum_over_range'
  statement: [AddCommMonoid S] (p : R[X]) {f : Nat -> R -> S} (h : forall n, f n 0 = 0) (n : Nat)
  proof: by
  have := supp_subset_range hn
  simp only [Polynomial.sum, support, coeff] at this ⊢
  exact Finsupp.sum_of_support_subset _ this _ fun n _hn => h n

中文:
定理 sum_over_range'
  结论: [加法交换幺半群 S] (p : R[X]) {f : 自然数 -> R -> S} (h : 对任意 n, f n 0 = 0) (n : 自然数)
  证明: by
  have := supp_subset_range hn
  simp only [Polynomial.sum, support, coeff] at this ⊢
  exact Finsupp.sum_of_support_subset _ this _ fun n _hn => h n

Depends on / 依赖: Finsupp, Finsupp.sum_of_support_subset, Polynomial, Polynomial.sum, sum_of_support_subset, supp_subset_range, support
-/
theorem sum_over_range' [AddCommMonoid S] (p : R[X]) {f : Nat -> R -> S} (h : forall n, f n 0 = 0) (n : Nat)
    (hn : p.natDegree < n) : p.sum f = ∑ a in range n, f a (coeff p a) := by
  have := supp_subset_range hn
  simp only [Polynomial.sum, support, coeff] at this ⊢
  exact Finsupp.sum_of_support_subset _ this _ fun n _hn => h n

/--
theorem `sum_over_range` / 定理 `sum_over_range`

English:
theorem sum_over_range
  given: [AddCommMonoid S] (p : R[X]) {f : Nat -> R -> S} (h : forall n, f n 0 = 0)
  proof: sum_over_range' p h (p.natDegree + 1) (lt_add_one _)

中文:
定理 sum_over_range
  条件: [加法交换幺半群 S] (p : R[X]) {f : 自然数 -> R -> S} (h : 对任意 n, f n 0 = 0)
  证明: sum_over_range' p h (p.natDegree + 1) (lt_add_one _)

Depends on / 依赖: lt_add_one, natDegree, p.natDegree, sum_over_range
-/
theorem sum_over_range [AddCommMonoid S] (p : R[X]) {f : Nat -> R -> S} (h : forall n, f n 0 = 0) :
    p.sum f = ∑ a in range (p.natDegree + 1), f a (coeff p a) :=
  sum_over_range' p h (p.natDegree + 1) (lt_add_one _)

-- TODO this is essentially a duplicate of `sum_over_range`, and should be removed.
/--
theorem `sum_fin` / 定理 `sum_fin`

English:
theorem sum_fin
  statement: [AddCommMonoid S] (f : Nat -> R -> S) (hf : forall i, f i 0 = 0) {n : Nat} {p : R[X]}
  proof: by
  by_cases hp : p = 0
  · rw [hp, sum_zero_index, Finset.sum_eq_zero]
    intro i _
    exact hf i
  rw [sum_over_range' _ hf n ((natDegree_lt_iff_degree_lt hp).mpr hn)]; rw [Fin.sum_univ_eq_sum_range fun i => f i (p.coeff i)]

中文:
定理 sum_fin
  结论: [加法交换幺半群 S] (f : 自然数 -> R -> S) (hf : 对任意 i, f i 0 = 0) {n : 自然数} {p : R[X]}
  证明: by
  by_cases hp : p = 0
  · rw [hp, sum_zero_index, Finset.sum_eq_zero]
    intro i _
    exact hf i
  rw [sum_over_range' _ hf n ((natDegree_lt_iff_degree_lt hp).mpr hn)]; rw [Fin.sum_univ_eq_sum_range fun i => f i (p.coeff i)]

Depends on / 依赖: Fin.sum_univ_eq_sum_range, Finset, Finset.sum_eq_zero, natDegree_lt_iff_degree_lt, p.coeff, sum_eq_zero, sum_over_range, sum_univ_eq_sum_range, sum_zero_index
-/
theorem sum_fin [AddCommMonoid S] (f : Nat -> R -> S) (hf : forall i, f i 0 = 0) {n : Nat} {p : R[X]}
    (hn : p.degree < n) : (∑ i : Fin n, f i (p.coeff i)) = p.sum f := by
  by_cases hp : p = 0
  · rw [hp, sum_zero_index, Finset.sum_eq_zero]
    intro i _
    exact hf i
  rw [sum_over_range' _ hf n ((natDegree_lt_iff_degree_lt hp).mpr hn)]; rw [Fin.sum_univ_eq_sum_range fun i => f i (p.coeff i)]

/--
theorem `as_sum_range'` / 定理 `as_sum_range'`

English:
theorem as_sum_range'
  given: (p : R[X]) (n : Nat) (hn : p.natDegree < n)
  proof: p.sum_monomial_eq.symm.trans p.sum_over_range' monomial_zero_right _ hn

中文:
定理 as_sum_range'
  条件: (p : R[X]) (n : 自然数) (hn : p.natDegree < n)
  证明: p.sum_monomial_eq.symm.trans p.sum_over_range' monomial_zero_right _ hn

Depends on / 依赖: monomial_zero_right, p.sum_monomial_eq.symm.trans, p.sum_over_range, sum_monomial_eq, sum_over_range
-/
theorem as_sum_range' (p : R[X]) (n : Nat) (hn : p.natDegree < n) :
    p = ∑ i in range n, monomial i (coeff p i) :=
p.sum_monomial_eq.symm.trans p.sum_over_range' monomial_zero_right _ hn

/--
theorem `as_sum_range` / 定理 `as_sum_range`

English:
theorem as_sum_range
  given: (p : R[X])
  statement: p = ∑ i in range (p.natDegree + 1), monomial i (coeff p i)
  proof: p.as_sum_range' _ (lt_add_one _)

中文:
定理 as_sum_range
  条件: (p : R[X])
  结论: p = ∑ i in range (p.natDegree + 1), monomial i (coeff p i)
  证明: p.as_sum_range' _ (lt_add_one _)

Depends on / 依赖: as_sum_range, lt_add_one, p.as_sum_range
-/
theorem as_sum_range (p : R[X]) : p = ∑ i in range (p.natDegree + 1), monomial i (coeff p i) :=
  p.as_sum_range' _ (lt_add_one _)

/--
theorem `as_sum_range_C_mul_X_pow'` / 定理 `as_sum_range_C_mul_X_pow'`

English:
theorem as_sum_range_C_mul_X_pow'
  given: (p : R[X]) {n : Nat} (hn : p.natDegree < n)
  proof: (p.as_sum_range' _ hn).trans by simp only [C_mul_X_pow_eq_monomial]

中文:
定理 as_sum_range_C_mul_X_pow'
  条件: (p : R[X]) {n : 自然数} (hn : p.natDegree < n)
  证明: (p.as_sum_range' _ hn).trans by simp only [C_mul_X_pow_eq_monomial]

Depends on / 依赖: C_mul_X_pow_eq_monomial, as_sum_range, p.as_sum_range
-/
theorem as_sum_range_C_mul_X_pow' (p : R[X]) {n : Nat} (hn : p.natDegree < n) :
    p = ∑ i in range n, C (coeff p i) * X ^ i :=
(p.as_sum_range' _ hn).trans by simp only [C_mul_X_pow_eq_monomial]

/--
theorem `as_sum_range_C_mul_X_pow` / 定理 `as_sum_range_C_mul_X_pow`

English:
theorem as_sum_range_C_mul_X_pow
  given: (p : R[X])
  proof: p.as_sum_range_C_mul_X_pow' (lt_add_one _)

中文:
定理 as_sum_range_C_mul_X_pow
  条件: (p : R[X])
  证明: p.as_sum_range_C_mul_X_pow' (lt_add_one _)

Depends on / 依赖: as_sum_range_C_mul_X_pow, lt_add_one, p.as_sum_range_C_mul_X_pow
-/
theorem as_sum_range_C_mul_X_pow (p : R[X]) :
    p = ∑ i in range (p.natDegree + 1), C (coeff p i) * X ^ i :=
  p.as_sum_range_C_mul_X_pow' (lt_add_one _)

/--
theorem `mem_support_C_mul_X_pow` / 定理 `mem_support_C_mul_X_pow`

English:
theorem mem_support_C_mul_X_pow
  given: {n a : Nat} {c : R} (h : a in support (C c * X ^ n))
  statement: a = n
  proof: mem_singleton.1 support_C_mul_X_pow_subset n c h

中文:
定理 mem_support_C_mul_X_pow
  条件: {n a : 自然数} {c : R} (h : a in support (C c * X ^ n))
  结论: a = n
  证明: mem_singleton.1 support_C_mul_X_pow_subset n c h

Depends on / 依赖: equivShrink, mem_singleton, nonUnitalNonAssocSemiring, support_C_mul_X_pow_subset, symm.nonUnitalNonAssocSemiring
-/
theorem mem_support_C_mul_X_pow {n a : Nat} {c : R} (h : a in support (C c * X ^ n)) : a = n :=
mem_singleton.1 support_C_mul_X_pow_subset n c h

/--
theorem `card_support_C_mul_X_pow_le_one` / 定理 `card_support_C_mul_X_pow_le_one`

English:
theorem card_support_C_mul_X_pow_le_one
  given: {c : R} {n : Nat}
  statement: #(support (C c * X ^ n)) <= 1
  proof: by
  rw [← card_singleton n]
  apply card_le_card (support_C_mul_X_pow_subset n c)

中文:
定理 card_support_C_mul_X_pow_le_one
  条件: {c : R} {n : 自然数}
  结论: #(support (C c * X ^ n)) <= 1
  证明: by
  rw [← card_singleton n]
  apply card_le_card (support_C_mul_X_pow_subset n c)

Depends on / 依赖: card_le_card, card_singleton, support_C_mul_X_pow_subset
-/
theorem card_support_C_mul_X_pow_le_one {c : R} {n : Nat} : #(support (C c * X ^ n)) <= 1 := by
  rw [← card_singleton n]
  apply card_le_card (support_C_mul_X_pow_subset n c)

/--
theorem `card_supp_le_succ_natDegree` / 定理 `card_supp_le_succ_natDegree`

English:
theorem card_supp_le_succ_natDegree
  given: (p : R[X])
  statement: #p.support <= p.natDegree + 1
  proof: by
  rw [← Finset.card_range (p.natDegree + 1)]
  exact Finset.card_le_card supp_subset_range_natDegree_succ

中文:
定理 card_supp_le_succ_natDegree
  条件: (p : R[X])
  结论: #p.support <= p.natDegree + 1
  证明: by
  rw [← Finset.card_range (p.natDegree + 1)]
  exact Finset.card_le_card supp_subset_range_natDegree_succ

Depends on / 依赖: Finset, Finset.card_le_card, Finset.card_range, card_le_card, card_range, natDegree, p.natDegree, supp_subset_range_natDegree_succ
-/
theorem card_supp_le_succ_natDegree (p : R[X]) : #p.support <= p.natDegree + 1 := by
  rw [← Finset.card_range (p.natDegree + 1)]
  exact Finset.card_le_card supp_subset_range_natDegree_succ

/--
theorem `le_degree_of_mem_supp` / 定理 `le_degree_of_mem_supp`

English:
theorem le_degree_of_mem_supp
  given: (a : Nat)
  statement: a in p.support -> ↑a <= degree p
  proof: le_degree_of_ne_zero ∘ mem_support_iff.mp

中文:
定理 le_degree_of_mem_supp
  条件: (a : 自然数)
  结论: a in p.support -> ↑a <= degree p
  证明: le_degree_of_ne_zero ∘ mem_support_iff.mp

Depends on / 依赖: le_degree_of_ne_zero, mem_support_iff, mem_support_iff.mp
-/
theorem le_degree_of_mem_supp (a : Nat) : a in p.support -> ↑a <= degree p :=
  le_degree_of_ne_zero ∘ mem_support_iff.mp

/--
theorem `nonempty_support_iff` / 定理 `nonempty_support_iff`

English:
theorem nonempty_support_iff
  statement: p.support.Nonempty ↔ p != 0
  proof: by
  rw [Ne]; rw [nonempty_iff_ne_empty]; rw [Ne]; rw [← support_eq_empty]

中文:
定理 nonempty_support_iff
  结论: p.support.非空 ↔ p != 0
  证明: by
  rw [Ne]; rw [nonempty_iff_ne_empty]; rw [Ne]; rw [← support_eq_empty]

Depends on / 依赖: nonempty_iff_ne_empty, support_eq_empty
-/
theorem nonempty_support_iff : p.support.Nonempty ↔ p != 0 := by
  rw [Ne]; rw [nonempty_iff_ne_empty]; rw [Ne]; rw [← support_eq_empty]

end Semiring

section Semiring

variable [Semiring R] {p q : R[X]} {ι : Type*}

/--
theorem `natDegree_mem_support_of_nonzero` / 定理 `natDegree_mem_support_of_nonzero`

English:
theorem natDegree_mem_support_of_nonzero
  given: (H : p != 0)
  statement: p.natDegree in p.support
  proof: by
  rw [mem_support_iff]
  exact (not_congr leadingCoeff_eq_zero).mpr H

中文:
定理 natDegree_mem_support_of_nonzero
  条件: (H : p != 0)
  结论: p.natDegree in p.support
  证明: by
  rw [mem_support_iff]
  exact (not_congr leadingCoeff_eq_zero).mpr H

Depends on / 依赖: leadingCoeff_eq_zero, mem_support_iff, not_congr
-/
theorem natDegree_mem_support_of_nonzero (H : p != 0) : p.natDegree in p.support := by
  rw [mem_support_iff]
  exact (not_congr leadingCoeff_eq_zero).mpr H

/--
theorem `natDegree_eq_support_max'` / 定理 `natDegree_eq_support_max'`

English:
theorem natDegree_eq_support_max'
  given: (h : p != 0)
  proof: (le_max' _ _ <| natDegree_mem_support_of_nonzero h).antisymm
    max'_le _ _ _ le_natDegree_of_mem_supp

中文:
定理 natDegree_eq_support_max'
  条件: (h : p != 0)
  证明: (le_max' _ _ <| natDegree_mem_support_of_nonzero h).antisymm
    max'_le _ _ _ le_natDegree_of_mem_supp

Depends on / 依赖: antisymm, le_max, le_natDegree_of_mem_supp, natDegree_mem_support_of_nonzero
-/
theorem natDegree_eq_support_max' (h : p != 0) :
    p.natDegree = p.support.max' (nonempty_support_iff.mpr h) :=
(le_max' _ _ <| natDegree_mem_support_of_nonzero h).antisymm
    max'_le _ _ _ le_natDegree_of_mem_supp

end Semiring

end Polynomial
