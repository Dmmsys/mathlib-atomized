/-
Copyright (c) 2021 Benjamin Davidson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Davidson, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.LocalExtr.Rolle
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Topology.Algebra.Polynomial

/-!
# Rolle's Theorem for polynomials

In this file we use Rolle's Theorem
to relate the number of real roots of a real polynomial and its derivative.
Namely, we prove the following facts.

* `Polynomial.card_roots_toFinset_le_card_roots_derivative_sdiff_roots_succ`:
  the number of roots of a real polynomial `p` is at most the number of roots of its derivative
  that are not roots of `p` plus one.
* `Polynomial.card_roots_toFinset_le_derivative`, `Polynomial.card_rootSet_le_derivative`:
  the number of roots of a real polynomial
  is at most the number of roots of its derivative plus one.
* `Polynomial.card_roots_le_derivative`: same, but the roots are counted with multiplicities.

## Keywords

polynomial, Rolle's Theorem, root
-/

public section

namespace Polynomial

/--
theorem `card_roots_toFinset_le_card_roots_derivative_sdiff_roots_succ` / 定理 `card_roots_toFinset_le_card_roots_derivative_sdiff_roots_succ`

English:
theorem card_roots_toFinset_le_card_roots_derivative_sdiff_roots_succ
  given: (p : Real[X])
  proof: by
  rcases eq_or_ne (derivative p) 0 with hp' | hp'
  · rw [eq_C_of_derivative_eq_zero hp']
    simp
  have hp : p != 0 := ne_of_apply_ne derivative (by rwa [derivative_zero])
  refine Finset.card_le_sdiff_of_interleaved fun x hx y hy hxy hxy' => ?_
  rw [Multiset.mem_toFinset]; rw [mem_roots hp] at hx hy
  obtain ⟨z, hz1, hz2⟩ := exists_deriv_eq_zero hxy p.continuousOn (hx.trans hy.symm)
  refine ⟨z, ?_, hz1⟩
  rwa [Multiset.mem_toFinset, mem_roots hp', IsRoot, ← p.deriv]

@[deprecated (since := "2026-06-03")]
alias card_roots_toFinset_le_card_roots_derivative_diff_roots_succ :=
  card_roots_toFinset_le_card_roots_derivative_sdiff_roots_succ

中文:
定理 card_roots_toFinset_le_card_roots_derivative_sdiff_roots_succ
  条件: (p : 实数[X])
  证明: by
  rcases eq_or_ne (derivative p) 0 with hp' | hp'
  · rw [eq_C_of_derivative_eq_zero hp']
    simp
  have hp : p != 0 := ne_of_apply_ne derivative (by rwa [derivative_zero])
  refine Finset.card_le_sdiff_of_interleaved fun x hx y hy hxy hxy' => ?_
  rw [Multiset.mem_toFinset]; rw [mem_roots hp] at hx hy
  obtain ⟨z, hz1, hz2⟩ := exists_deriv_eq_zero hxy p.continuousOn (hx.trans hy.symm)
  refine ⟨z, ?_, hz1⟩
  rwa [Multiset.mem_toFinset, mem_roots hp', IsRoot, ← p.deriv]

@[deprecated (since := "2026-06-03")]
alias card_roots_toFinset_le_card_roots_derivative_diff_roots_succ :=
  card_roots_toFinset_le_card_roots_derivative_sdiff_roots_succ

Depends on / 依赖: Finset, Finset.card_le_sdiff_of_interleaved, IsRoot, Multiset, Multiset.mem_toFinset, card_le_sdiff_of_interleaved, continuousOn, derivative, derivative_zero, eq_C_of_derivative_eq_zero, eq_or_ne, exists_deriv_eq_zero, hx.trans, hy.symm, mem_roots, mem_toFinset, ne_of_apply_ne, p.continuousOn, p.deriv
-/
theorem card_roots_toFinset_le_card_roots_derivative_sdiff_roots_succ (p : Real[X]) :
    p.roots.toFinset.card <= (p.derivative.roots.toFinset \ p.roots.toFinset).card + 1 := by
  rcases eq_or_ne (derivative p) 0 with hp' | hp'
  · rw [eq_C_of_derivative_eq_zero hp']
    simp
  have hp : p != 0 := ne_of_apply_ne derivative (by rwa [derivative_zero])
  refine Finset.card_le_sdiff_of_interleaved fun x hx y hy hxy hxy' => ?_
  rw [Multiset.mem_toFinset]; rw [mem_roots hp] at hx hy
  obtain ⟨z, hz1, hz2⟩ := exists_deriv_eq_zero hxy p.continuousOn (hx.trans hy.symm)
  refine ⟨z, ?_, hz1⟩
  rwa [Multiset.mem_toFinset, mem_roots hp', IsRoot, ← p.deriv]

@[deprecated (since := "2026-06-03")]
alias card_roots_toFinset_le_card_roots_derivative_diff_roots_succ :=
  card_roots_toFinset_le_card_roots_derivative_sdiff_roots_succ

/--
theorem `card_roots_toFinset_le_derivative` / 定理 `card_roots_toFinset_le_derivative`

English:
theorem card_roots_toFinset_le_derivative
  given: (p : Real[X])
  proof: p.card_roots_toFinset_le_card_roots_derivative_sdiff_roots_succ.trans by
    grw [Finset.sdiff_subset]

中文:
定理 card_roots_toFinset_le_derivative
  条件: (p : 实数[X])
  证明: p.card_roots_toFinset_le_card_roots_derivative_sdiff_roots_succ.trans by
    grw [Finset.sdiff_subset]

Depends on / 依赖: Finset, Finset.sdiff_subset, card_roots_toFinset_le_card_roots_derivative_sdiff_roots_succ, p.card_roots_toFinset_le_card_roots_derivative_sdiff_roots_succ.trans, sdiff_subset
-/
theorem card_roots_toFinset_le_derivative (p : Real[X]) :
    p.roots.toFinset.card <= p.derivative.roots.toFinset.card + 1 :=
p.card_roots_toFinset_le_card_roots_derivative_sdiff_roots_succ.trans by
    grw [Finset.sdiff_subset]

/--
theorem `card_roots_le_derivative` / 定理 `card_roots_le_derivative`

English:
theorem card_roots_le_derivative
  given: (p : Real[X])
  proof: calc
    Multiset.card p.roots = ∑ x in p.roots.toFinset, p.roots.count x :=
      (Multiset.toFinset_sum_count_eq _).symm
    _ = ∑ x in p.roots.toFinset, (p.roots.count x - 1 + 1) :=
      (Eq.symm <| Finset.sum_congr rfl fun _ hx => tsub_add_cancel_of_le <|
Nat.succ_le_iff.2 Multiset.count_pos.2 Multiset.mem_toFinset.1 hx)
    _ = (∑ x in p.roots.toFinset, (p.rootMultiplicity x - 1)) + p.roots.toFinset.card := by
      simp only [Finset.sum_add_distrib, Finset.card_eq_sum_ones, count_roots]
    _ <= (∑ x in p.roots.toFinset, p.derivative.rootMultiplicity x) +
          ((p.derivative.roots.toFinset \ p.roots.toFinset).card + 1) :=
      (add_le_add
        (Finset.sum_le_sum fun _ _ => rootMultiplicity_sub_one_le_derivative_rootMultiplicity _ _)
        p.card_roots_toFinset_le_card_roots_derivative_sdiff_roots_succ)
    _ <= (∑ x in p.roots.toFinset, p.derivative.roots.count x) +
          ((∑ x in p.derivative.roots.toFinset \ p.roots.toFinset,
            p.derivative.roots.count x) + 1) := by
      simp only [← count_roots, Finset.card_eq_sum_ones]
      gcongr with x hx
      rw [Nat.succ_le_iff]; rw [Multiset.count_pos]; rw [← Multiset.mem_toFinset]
      exact (Finset.mem_sdiff.1 hx).1
    _ = Multiset.card (derivative p).roots + 1 := by
      rw [← add_assoc]; rw [← Finset.sum_union Finset.disjoint_sdiff]; rw [Finset.union_sdiff_self_eq_union]; rw [←
        Multiset.toFinset_sum_count_eq]; rw [← Finset.sum_subset Finset.subset_union_right]
      intro x _ hx₂
      simpa only [Multiset.mem_toFinset, Multiset.count_eq_zero] using hx₂

中文:
定理 card_roots_le_derivative
  条件: (p : 实数[X])
  证明: calc
    Multiset.card p.roots = ∑ x in p.roots.toFinset, p.roots.count x :=
      (Multiset.toFinset_sum_count_eq _).symm
    _ = ∑ x in p.roots.toFinset, (p.roots.count x - 1 + 1) :=
      (Eq.symm <| Finset.sum_congr rfl fun _ hx => tsub_add_cancel_of_le <|
Nat.succ_le_iff.2 Multiset.count_pos.2 Multiset.mem_toFinset.1 hx)
    _ = (∑ x in p.roots.toFinset, (p.rootMultiplicity x - 1)) + p.roots.toFinset.card := by
      simp only [Finset.sum_add_distrib, Finset.card_eq_sum_ones, count_roots]
    _ <= (∑ x in p.roots.toFinset, p.derivative.rootMultiplicity x) +
          ((p.derivative.roots.toFinset \ p.roots.toFinset).card + 1) :=
      (add_le_add
        (Finset.sum_le_sum fun _ _ => rootMultiplicity_sub_one_le_derivative_rootMultiplicity _ _)
        p.card_roots_toFinset_le_card_roots_derivative_sdiff_roots_succ)
    _ <= (∑ x in p.roots.toFinset, p.derivative.roots.count x) +
          ((∑ x in p.derivative.roots.toFinset \ p.roots.toFinset,
            p.derivative.roots.count x) + 1) := by
      simp only [← count_roots, Finset.card_eq_sum_ones]
      gcongr with x hx
      rw [Nat.succ_le_iff]; rw [Multiset.count_pos]; rw [← Multiset.mem_toFinset]
      exact (Finset.mem_sdiff.1 hx).1
    _ = Multiset.card (derivative p).roots + 1 := by
      rw [← add_assoc]; rw [← Finset.sum_union Finset.disjoint_sdiff]; rw [Finset.union_sdiff_self_eq_union]; rw [←
        Multiset.toFinset_sum_count_eq]; rw [← Finset.sum_subset Finset.subset_union_right]
      intro x _ hx₂
      simpa only [Multiset.mem_toFinset, Multiset.count_eq_zero] using hx₂

Depends on / 依赖: Eq.symm, Finset, Finset.card_eq_sum_ones, Finset.sum_add_distrib, Finset.sum_congr, Multiset, Multiset.card, Multiset.count_pos, Multiset.mem_toFinset, Multiset.toFinset_sum_count_eq, Nat.succ_le_iff, card_eq_sum_ones, count_pos, count_roots, mem_toFinset, p.rootMultiplicity, p.roots, p.roots.count, p.roots.toFinset, p.roots.toFinset.card
-/
theorem card_roots_le_derivative (p : Real[X]) :
    Multiset.card p.roots <= Multiset.card (derivative p).roots + 1 :=
  calc
    Multiset.card p.roots = ∑ x in p.roots.toFinset, p.roots.count x :=
      (Multiset.toFinset_sum_count_eq _).symm
    _ = ∑ x in p.roots.toFinset, (p.roots.count x - 1 + 1) :=
      (Eq.symm <| Finset.sum_congr rfl fun _ hx => tsub_add_cancel_of_le <|
Nat.succ_le_iff.2 Multiset.count_pos.2 Multiset.mem_toFinset.1 hx)
    _ = (∑ x in p.roots.toFinset, (p.rootMultiplicity x - 1)) + p.roots.toFinset.card := by
      simp only [Finset.sum_add_distrib, Finset.card_eq_sum_ones, count_roots]
    _ <= (∑ x in p.roots.toFinset, p.derivative.rootMultiplicity x) +
          ((p.derivative.roots.toFinset \ p.roots.toFinset).card + 1) :=
      (add_le_add
        (Finset.sum_le_sum fun _ _ => rootMultiplicity_sub_one_le_derivative_rootMultiplicity _ _)
        p.card_roots_toFinset_le_card_roots_derivative_sdiff_roots_succ)
    _ <= (∑ x in p.roots.toFinset, p.derivative.roots.count x) +
          ((∑ x in p.derivative.roots.toFinset \ p.roots.toFinset,
            p.derivative.roots.count x) + 1) := by
      simp only [← count_roots, Finset.card_eq_sum_ones]
      gcongr with x hx
      rw [Nat.succ_le_iff]; rw [Multiset.count_pos]; rw [← Multiset.mem_toFinset]
      exact (Finset.mem_sdiff.1 hx).1
    _ = Multiset.card (derivative p).roots + 1 := by
      rw [← add_assoc]; rw [← Finset.sum_union Finset.disjoint_sdiff]; rw [Finset.union_sdiff_self_eq_union]; rw [←
        Multiset.toFinset_sum_count_eq]; rw [← Finset.sum_subset Finset.subset_union_right]
      intro x _ hx₂
      simpa only [Multiset.mem_toFinset, Multiset.count_eq_zero] using hx₂

/--
theorem `card_rootSet_le_derivative` / 定理 `card_rootSet_le_derivative`

English:
theorem card_rootSet_le_derivative
  given: {F : Type*} [CommRing F] [Algebra F Real] (p : F[X])
  proof: by
  simpa only [rootSet_def, Finset.coe_sort_coe, Fintype.card_coe, derivative_map] using
    card_roots_toFinset_le_derivative (p.map (algebraMap F Real))

中文:
定理 card_rootSet_le_derivative
  条件: {F : 类型} [交换环 F] [代数 F 实数] (p : F[X])
  证明: by
  simpa only [rootSet_def, Finset.coe_sort_coe, Fintype.card_coe, derivative_map] using
    card_roots_toFinset_le_derivative (p.map (algebraMap F Real))

Depends on / 依赖: Finset, Finset.coe_sort_coe, Fintype, Fintype.card_coe, algebraMap, card_coe, card_roots_toFinset_le_derivative, coe_sort_coe, derivative_map, p.map, rootSet_def
-/
theorem card_rootSet_le_derivative {F : Type*} [CommRing F] [Algebra F Real] (p : F[X]) :
    Fintype.card (p.rootSet Real) <= Fintype.card (p.derivative.rootSet Real) + 1 := by
  simpa only [rootSet_def, Finset.coe_sort_coe, Fintype.card_coe, derivative_map] using
    card_roots_toFinset_le_derivative (p.map (algebraMap F Real))

end Polynomial
