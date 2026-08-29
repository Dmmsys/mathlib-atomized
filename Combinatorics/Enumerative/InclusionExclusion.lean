/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Module.BigOperators

/-!
# Inclusion-exclusion principle

This file proves several variants of the inclusion-exclusion principle.

The inclusion-exclusion principle says that the sum/integral of a function over a finite union of
sets can be calculated as the alternating sum over `n > 0` of the sum/integral of the function over
the intersection of `n` of the sets.

By taking complements, it also says that the sum/integral of a function over a finite intersection
of complements of sets can be calculated as the alternating sum over `n ≥ 0` of the sum/integral of
the function over the intersection of `n` of the sets.

By taking the function to be constant `1`, we instead get a result about the cardinality/measure of
the sets.

## Main declarations

Per the above explanation, this file contains the following variants of inclusion-exclusion:
* `Finset.inclusion_exclusion_sum_biUnion`: Sum of a function over a finite union of sets
* `Finset.inclusion_exclusion_card_biUnion`: Cardinality of a finite union of sets
* `Finset.inclusion_exclusion_sum_inf_compl`: Sum of a function over a finite intersection of
  complements of sets
* `Finset.inclusion_exclusion_card_inf_compl`: Cardinality of a finite intersection of
  complements of sets

See also `MeasureTheory.integral_biUnion_eq_sum_powerset` for the version with integrals, and
`MeasureTheory.measureReal_biUnion_eq_sum_powerset` for the version with measures.

## TODO

* Prove that truncating the series alternatively gives an upper/lower bound to the true value.
-/

public section

assert_not_exists Field

namespace Finset
variable {ι α G : Type*} [AddCommGroup G] {s : Finset ι}

/--
lemma `prod_indicator_biUnion_sub_indicator` / 引理 `prod_indicator_biUnion_sub_indicator`

English:
lemma prod_indicator_biUnion_sub_indicator
  given: (hs : s.Nonempty) (S : ι -> Set α) (a : α)
  proof: by
  by_cases ha : a in ⋃ i in s, S i
  · have ha' := ha
    simp only [Set.mem_iUnion, exists_prop] at ha
    obtain ⟨i, hi, ha⟩ := ha
    apply prod_eq_zero hi (by simp [ha, ha'])
  · obtain ⟨i, hi⟩ := hs
    have ha : a ∉ S i := by aesop
exact prod_eq_zero hi by simp [*, -coe_biUnion]

中文:
引理 prod_indicator_biUnion_sub_indicator
  条件: (hs : s.Nonempty) (S : ι -> Set α) (a : α)
  证明: by
  by_cases ha : a in ⋃ i in s, S i
  · have ha' := ha
    simp only [Set.mem_iUnion, exists_prop] at ha
    obtain ⟨i, hi, ha⟩ := ha
    apply prod_eq_zero hi (by simp [ha, ha'])
  · obtain ⟨i, hi⟩ := hs
    have ha : a ∉ S i := by aesop
exact prod_eq_zero hi by simp [*, -coe_biUnion]

Depends on / 依赖: Set.mem_iUnion, coe_biUnion, exists_prop, mem_iUnion, prod_eq_zero
-/
lemma prod_indicator_biUnion_sub_indicator (hs : s.Nonempty) (S : ι -> Set α) (a : α) :
    ∏ i in s, (Set.indicator (⋃ i in s, S i) 1 a - Set.indicator (S i) 1 a) = (0 : Int) := by
  by_cases ha : a in ⋃ i in s, S i
  · have ha' := ha
    simp only [Set.mem_iUnion, exists_prop] at ha
    obtain ⟨i, hi, ha⟩ := ha
    apply prod_eq_zero hi (by simp [ha, ha'])
  · obtain ⟨i, hi⟩ := hs
    have ha : a ∉ S i := by aesop
exact prod_eq_zero hi by simp [*, -coe_biUnion]

/--
lemma `indicator_biUnion_eq_sum_powerset` / 引理 `indicator_biUnion_eq_sum_powerset`

English:
lemma indicator_biUnion_eq_sum_powerset
  given: (s : Finset ι) (S : ι -> Set α) (f : α -> G) (a : α)
  proof: by
  classical
  by_cases ha : a in ⋃ i in s, S i; swap
  · simp only [ha, not_false_eq_true, Set.indicator_of_notMem, Int.reduceNeg, pow_succ, mul_neg,
      mul_one, neg_smul]
    symm
    apply sum_eq_zero
    simp only [Int.reduceNeg, neg_eq_zero, mem_filter, mem_powerset, and_imp]
    intro t h

中文:
引理 indicator_biUnion_eq_sum_powerset
  条件: (s : Finset ι) (S : ι -> Set α) (f : α -> G) (a : α)
  证明: by
  classical
  by_cases ha : a in ⋃ i in s, S i; swap
  · simp only [ha, not_false_eq_true, Set.indicator_of_notMem, Int.reduceNeg, pow_succ, mul_neg,
      mul_one, neg_smul]
    symm
    apply sum_eq_zero
    simp only [Int.reduceNeg, neg_eq_zero, mem_filter, mem_powerset, and_imp]
    intro t h

Depends on / 依赖: Int.reduceNeg, Set.indicator, Set.indicator_of_notMem, Set.mem_iInter, Set.mem_iUnion, and_imp, classical, contrapose, exists_prop, indicator, indicator_of_notMem, mem_filter, mem_iInter, mem_iUnion, mem_powerset, mul_neg, mul_one, neg_eq_zero, neg_smul, not_false_eq_true
-/
lemma indicator_biUnion_eq_sum_powerset (s : Finset ι) (S : ι -> Set α) (f : α -> G) (a : α) :
    Set.indicator (⋃ i in s, S i) f a = ∑ t in s.powerset with t.Nonempty,
      (-1) ^ (#t + 1) • Set.indicator (⋂ i in t, S i) f a := by
  classical
  by_cases ha : a in ⋃ i in s, S i; swap
  · simp only [ha, not_false_eq_true, Set.indicator_of_notMem, Int.reduceNeg, pow_succ, mul_neg,
      mul_one, neg_smul]
    symm
    apply sum_eq_zero
    simp only [Int.reduceNeg, neg_eq_zero, mem_filter, mem_powerset, and_imp]
    intro t hts ht
    rw [Set.indicator_of_notMem]
    · simp
    · contrapose ha
      simp only [Set.mem_iInter] at ha
      rcases ht with ⟨i, hi⟩
      simp only [Set.mem_iUnion, exists_prop]
      exact ⟨i, hts hi, ha _ hi⟩
  rw [← sub_eq_zero]
  calc
    Set.indicator (⋃ i in s, S i) f a - ∑ t in s.powerset with t.Nonempty,
      (-1) ^ (#t + 1) • Set.indicator (⋂ i in t.1, S i) f a
    _ = ∑ t in s.powerset with t.Nonempty, (-1) ^ #t • Set.indicator (⋂ i in t, S i) f a +
        ∑ t in s.powerset with ¬ t.Nonempty, (-1) ^ #t • Set.indicator (⋂ i in t, S i) f a := by
      simp [sub_eq_neg_add, ← sum_neg_distrib, filter_eq', pow_succ, ha]
    _ = ∑ t in s.powerset, (-1) ^ #t • Set.indicator (⋂ i in t, S i) f a := by
      rw [sum_filter_add_sum_filter_not]
    _ = (∏ i in s, (1 - Set.indicator (S i) 1 a : Int)) • f a := by
      simp only [Int.reduceNeg, prod_sub, prod_const_one, mul_one, sum_smul]
      congr! 1 with t
      simp only [prod_const_one, prod_indicator_apply]
      simp [Set.indicator]
    _ = 0 := by
      have : Set.indicator (⋃ i in s, S i) 1 a = (1 : Int) := Set.indicator_of_mem ha 1
      rw [← this]; rw [prod_indicator_biUnion_sub_indicator]; rw [zero_smul]
      simp only [Set.mem_iUnion, exists_prop] at ha
      rcases ha with ⟨i, hi, -⟩
      exact ⟨i, hi⟩

variable [DecidableEq α]

/--
lemma `prod_indicator_biUnion_finset_sub_indicator` / 引理 `prod_indicator_biUnion_finset_sub_indicator`

English:
lemma prod_indicator_biUnion_finset_sub_indicator
  given: (hs : s.Nonempty) (S : ι -> Finset α) (a : α)
  proof: by
  convert! prod_indicator_biUnion_sub_indicator hs (fun i => S i) a
  simp

中文:
引理 prod_indicator_biUnion_finset_sub_indicator
  条件: (hs : s.Nonempty) (S : ι -> Finset α) (a : α)
  证明: by
  convert! prod_indicator_biUnion_sub_indicator hs (fun i => S i) a
  simp

Depends on / 依赖: convert, prod_indicator_biUnion_sub_indicator
-/
lemma prod_indicator_biUnion_finset_sub_indicator (hs : s.Nonempty) (S : ι -> Finset α) (a : α) :
    ∏ i in s, (Set.indicator (s.biUnion S) 1 a - Set.indicator (S i) 1 a) = (0 : Int) := by
  convert! prod_indicator_biUnion_sub_indicator hs (fun i => S i) a
  simp

set_option backward.isDefEq.respectTransparency false in
/--
theorem `inclusion_exclusion_sum_biUnion` / 定理 `inclusion_exclusion_sum_biUnion`

English:
theorem inclusion_exclusion_sum_biUnion
  given: (s : Finset ι) (S : ι -> Finset α) (f : α -> G)
  proof: by
  classical
  rw [← sub_eq_zero]
  calc
    ∑ a in s.biUnion S, f a - ∑ t : s.powerset.filter (·.Nonempty),
      (-1) ^ (#t.1 + 1) • ∑ a in t.1.inf' (mem_filter.1 t.2).2 S, f a
      = ∑ t : s.powerset.filter (·.Nonempty),
          (-1) ^ #t.1 • ∑ a in t.1.inf' (mem_filter.1 t.2).2 S, f a +
   

中文:
定理 inclusion_exclusion_sum_biUnion
  条件: (s : Finset ι) (S : ι -> Finset α) (f : α -> G)
  证明: by
  classical
  rw [← sub_eq_zero]
  calc
    ∑ a in s.biUnion S, f a - ∑ t : s.powerset.filter (·.Nonempty),
      (-1) ^ (#t.1 + 1) • ∑ a in t.1.inf' (mem_filter.1 t.2).2 S, f a
      = ∑ t : s.powerset.filter (·.Nonempty),
          (-1) ^ #t.1 • ∑ a in t.1.inf' (mem_filter.1 t.2).2 S, f a +
   

Depends on / 依赖: Nonempty, biUnion, classical, filter, filter_eq, mem_filter, pow_succ, powerset, s.biUnion, s.powerset, s.powerset.filter, sub_eq_neg_add, sub_eq_zero, sum_neg_distrib, t.Nonempty, t.inf
-/
theorem inclusion_exclusion_sum_biUnion (s : Finset ι) (S : ι -> Finset α) (f : α -> G) :
    ∑ a in s.biUnion S, f a = ∑ t : s.powerset.filter (·.Nonempty),
      (-1) ^ (#t.1 + 1) • ∑ a in t.1.inf' (mem_filter.1 t.2).2 S, f a := by
  classical
  rw [← sub_eq_zero]
  calc
    ∑ a in s.biUnion S, f a - ∑ t : s.powerset.filter (·.Nonempty),
      (-1) ^ (#t.1 + 1) • ∑ a in t.1.inf' (mem_filter.1 t.2).2 S, f a
      = ∑ t : s.powerset.filter (·.Nonempty),
          (-1) ^ #t.1 • ∑ a in t.1.inf' (mem_filter.1 t.2).2 S, f a +
          ∑ t in s.powerset.filter (¬ ·.Nonempty), (-1) ^ #t • ∑ a in s.biUnion S, f a := by
      simp [sub_eq_neg_add, ← sum_neg_distrib, filter_eq', pow_succ]
    _ = ∑ t in s.powerset, (-1) ^ #t •
          if ht : t.Nonempty then ∑ a in t.inf' ht S, f a else ∑ a in s.biUnion S, f a := by
      rw [← sum_attach (filter ..)]; simp [sum_dite]
    _ = ∑ a in s.biUnion S, (∏ i in s, (1 - Set.indicator (S i) 1 a : Int)) • f a := by
      simp only [Int.reduceNeg, prod_sub, sum_comm (s := s.biUnion S), sum_smul, mul_assoc]
      congr! with t
      split_ifs with ht
      · obtain ⟨i, hi⟩ := ht
        simp only [prod_const_one, prod_indicator_apply]
        simp only [smul_sum, Set.indicator, Set.mem_iInter, mem_coe, Pi.one_apply, mul_ite, mul_one,
          mul_zero, ite_smul, zero_smul, sum_ite, not_forall, sum_const_zero, add_zero]
        congr
        aesop
      · obtain rfl := not_nonempty_iff_eq_empty.1 ht
        simp
    _ = ∑ a in s.biUnion S, (∏ i in s,
          (Set.indicator (s.biUnion S) 1 a - Set.indicator (S i) 1 a) : Int) • f a := by
      congr! with t; rw [Set.indicator_of_mem ‹_›, Pi.one_apply]
    _ = 0 := by
      obtain rfl | hs := s.eq_empty_or_nonempty <;>
        simp [-coe_biUnion, prod_indicator_biUnion_finset_sub_indicator, *]

/--
theorem `inclusion_exclusion_card_biUnion` / 定理 `inclusion_exclusion_card_biUnion`

English:
theorem inclusion_exclusion_card_biUnion
  given: (s : Finset ι) (S : ι -> Finset α)
  proof: by
  simpa using inclusion_exclusion_sum_biUnion (G := Int) s S (f := 1)

中文:
定理 inclusion_exclusion_card_biUnion
  条件: (s : Finset ι) (S : ι -> Finset α)
  证明: by
  simpa using inclusion_exclusion_sum_biUnion (G := Int) s S (f := 1)

Depends on / 依赖: inclusion_exclusion_sum_biUnion
-/
theorem inclusion_exclusion_card_biUnion (s : Finset ι) (S : ι -> Finset α) :
    #(s.biUnion S) = ∑ t : s.powerset.filter (·.Nonempty),
      (-1 : Int) ^ (#t.1 + 1) * #(t.1.inf' (mem_filter.1 t.2).2 S) := by
  simpa using inclusion_exclusion_sum_biUnion (G := Int) s S (f := 1)

variable [Fintype α]

/--
theorem `inclusion_exclusion_sum_inf_compl` / 定理 `inclusion_exclusion_sum_inf_compl`

English:
theorem inclusion_exclusion_sum_inf_compl
  given: (s : Finset ι) (S : ι -> Finset α) (f : α -> G)
  proof: by
  classical
  calc
    ∑ a in s.inf fun i => (S i)ᶜ, f a
      = ∑ a, f a - ∑ a in s.biUnion S, f a := by
      rw [← Finset.compl_sup]; rw [sup_eq_biUnion]; rw [eq_sub_iff_add_eq]; rw [sum_compl_add_sum]
    _ = ∑ t in s.powerset.filter (¬ ·.Nonempty), (-1) ^ #t • ∑ a in t.inf S, f a
          +

中文:
定理 inclusion_exclusion_sum_inf_compl
  条件: (s : Finset ι) (S : ι -> Finset α) (f : α -> G)
  证明: by
  classical
  calc
    ∑ a in s.inf fun i => (S i)ᶜ, f a
      = ∑ a, f a - ∑ a in s.biUnion S, f a := by
      rw [← Finset.compl_sup]; rw [sup_eq_biUnion]; rw [eq_sub_iff_add_eq]; rw [sum_compl_add_sum]
    _ = ∑ t in s.powerset.filter (¬ ·.Nonempty), (-1) ^ #t • ∑ a in t.inf S, f a
          +

Depends on / 依赖: Finset, Finset.compl_sup, Nonempty, _eq_inf, biUnion, classical, compl_sup, eq_sub_iff_add_eq, filter, filter_eq, inclusion_exclusion_sum_biUnion, pow_succ, powerset, s.biUnion, s.inf, s.powerset, s.powerset.filter, sub_eq_add_neg, sum_attach, sum_compl_add_sum
-/
theorem inclusion_exclusion_sum_inf_compl (s : Finset ι) (S : ι -> Finset α) (f : α -> G) :
    ∑ a in s.inf fun i => (S i)ᶜ, f a = ∑ t in s.powerset, (-1) ^ #t • ∑ a in t.inf S, f a := by
  classical
  calc
    ∑ a in s.inf fun i => (S i)ᶜ, f a
      = ∑ a, f a - ∑ a in s.biUnion S, f a := by
      rw [← Finset.compl_sup]; rw [sup_eq_biUnion]; rw [eq_sub_iff_add_eq]; rw [sum_compl_add_sum]
    _ = ∑ t in s.powerset.filter (¬ ·.Nonempty), (-1) ^ #t • ∑ a in t.inf S, f a
          + ∑ t in s.powerset.filter (·.Nonempty), (-1) ^ #t • ∑ a in t.inf S, f a := by
      simp [← sum_attach (filter ..), inclusion_exclusion_sum_biUnion, inf'_eq_inf, filter_eq',
        sub_eq_add_neg, pow_succ]
    _ = ∑ t in s.powerset, (-1) ^ #t • ∑ a in t.inf S, f a := sum_filter_not_add_sum_filter ..

/--
theorem `inclusion_exclusion_card_inf_compl` / 定理 `inclusion_exclusion_card_inf_compl`

English:
theorem inclusion_exclusion_card_inf_compl
  given: (s : Finset ι) (S : ι -> Finset α)
  proof: by
  simpa using inclusion_exclusion_sum_inf_compl (G := Int) s S (f := 1)

中文:
定理 inclusion_exclusion_card_inf_compl
  条件: (s : Finset ι) (S : ι -> Finset α)
  证明: by
  simpa using inclusion_exclusion_sum_inf_compl (G := Int) s S (f := 1)

Depends on / 依赖: inclusion_exclusion_sum_inf_compl
-/
theorem inclusion_exclusion_card_inf_compl (s : Finset ι) (S : ι -> Finset α) :
    #(s.inf fun i => (S i)ᶜ) = ∑ t in s.powerset, (-1 : Int) ^ #t * #(t.inf S) := by
  simpa using inclusion_exclusion_sum_inf_compl (G := Int) s S (f := 1)

end Finset
