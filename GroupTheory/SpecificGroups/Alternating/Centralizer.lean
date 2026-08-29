/-
Copyright (c) 2023 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-! # Centralizer of an element in the alternating group

Given a finite type `α`, our goal is to compute the cardinality of conjugacy classes
in `alternatingGroup α`.

* `AlternatingGroup.card_of_cycleType_mul_eq m` and `AlternatingGroup.card_of_cycleType m`
  compute the number of even permutations of given cycle type.

* `Equiv.Perm.OnCycleFactors.odd_of_centralizer_le_alternatingGroup` :
  if `Subgroup.centralizer {g} ≤ alternatingGroup α`, then all members of the `g.cycleType` are odd.

* `Equiv.Perm.card_le_of_centralizer_le_alternating` :
  if `Subgroup.centralizer {g} ≤ alternatingGroup α`, then the cardinality of α
  is at most `g.cycleType.sum` plus one.

* `Equiv.Perm.count_le_one_of_centralizer_le_alternating` :
  if `Subgroup.centralizer {g} ≤ alternatingGroup α`, then `g.cycleType` has no repetitions.

* `Equiv.Perm.centralizer_le_alternating_iff` :
  the previous three conditions are necessary and sufficient
  for having `Subgroup.centralizer {g} ≤ alternatingGroup α`.

TODO :
Deduce the formula for the cardinality of the centralizers
and conjugacy classes in `alternatingGroup α`.
-/

public section

open Equiv Finset Function MulAction

variable {α : Type*} [Fintype α] [DecidableEq α] {g : Perm α}

namespace Equiv.Perm.OnCycleFactors

/--
theorem `odd_of_centralizer_le_alternatingGroup` / 定理 `odd_of_centralizer_le_alternatingGroup`

English:
theorem odd_of_centralizer_le_alternatingGroup
  statement: (h : Subgroup.centralizer {g} <= alternatingGroup α)
  proof: by
  rw [cycleType_def g]; rw [Multiset.mem_map] at hi
  obtain ⟨c, hc, rfl⟩ := hi
  rw [← Finset.mem_def] at hc
  suffices sign c = 1 by
    rw [IsCycle.sign _]; rw [neg_eq_iff_eq_neg]; rw [← Int.units_ne_iff_eq_neg] at this
    · rw [← Nat.not_even_iff_odd, comp_apply]
      exact fun h => this h.neg_one_pow
    · rw [mem_cycleFactorsFinset_iff] at hc
      exact hc.left
  apply h
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Equiv.Perm.self_mem_cycle_factors_commute hc

中文:
定理 odd_of_centralizer_le_alternatingGroup
  结论: (h : 子群.centralizer {g} <= alternatingGroup α)
  证明: by
  rw [cycleType_def g]; rw [Multiset.mem_map] at hi
  obtain ⟨c, hc, rfl⟩ := hi
  rw [← Finset.mem_def] at hc
  suffices sign c = 1 by
    rw [IsCycle.sign _]; rw [neg_eq_iff_eq_neg]; rw [← Int.units_ne_iff_eq_neg] at this
    · rw [← Nat.not_even_iff_odd, comp_apply]
      exact fun h => this h.neg_one_pow
    · rw [mem_cycleFactorsFinset_iff] at hc
      exact hc.left
  apply h
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Equiv.Perm.self_mem_cycle_factors_commute hc

Depends on / 依赖: Equiv.Perm.self_mem_cycle_factors_commute, Finset, Finset.mem_def, Int.units_ne_iff_eq_neg, IsCycle, IsCycle.sign, Multiset, Multiset.mem_map, Nat.not_even_iff_odd, Subgroup, Subgroup.mem_centralizer_singleton_iff, comp_apply, cycleType_def, h.neg_one_pow, hc.left, mem_centralizer_singleton_iff, mem_cycleFactorsFinset_iff, mem_def, mem_map, neg_eq_iff_eq_neg
-/
theorem odd_of_centralizer_le_alternatingGroup (h : Subgroup.centralizer {g} <= alternatingGroup α)
    (i : Nat) (hi : i in g.cycleType) :
    Odd i := by
  rw [cycleType_def g]; rw [Multiset.mem_map] at hi
  obtain ⟨c, hc, rfl⟩ := hi
  rw [← Finset.mem_def] at hc
  suffices sign c = 1 by
    rw [IsCycle.sign _]; rw [neg_eq_iff_eq_neg]; rw [← Int.units_ne_iff_eq_neg] at this
    · rw [← Nat.not_even_iff_odd, comp_apply]
      exact fun h => this h.neg_one_pow
    · rw [mem_cycleFactorsFinset_iff] at hc
      exact hc.left
  apply h
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Equiv.Perm.self_mem_cycle_factors_commute hc

end Equiv.Perm.OnCycleFactors

namespace AlternatingGroup

open Nat Equiv.Perm.OnCycleFactors Equiv.Perm

/--
theorem `map_subtype_of_cycleType` / 定理 `map_subtype_of_cycleType`

English:
theorem map_subtype_of_cycleType
  given: (m : Multiset Nat)
  proof: by
  split_ifs with hm
  · ext g
    simp_rw [Finset.mem_map, Finset.mem_filter_univ, Embedding.coe_subtype, Subtype.exists,
      mem_alternatingGroup, exists_and_left, exists_prop, exists_eq_right_right,
      and_iff_left_iff_imp]
    intro hg
    rw [sign_of_cycleType]; rw [hg]; rw [Even.neg_one_pow hm]
  · rw [Finset.eq_empty_iff_forall_notMem]
    intro g hg
    simp_rw [Finset.mem_map, Finset.mem_filter_univ, Embedding.coe_subtype, Subtype.exists,
      mem_alternatingGroup, exists_and_left, exists_prop, exists_eq_right_right] at hg
    rcases hg with ⟨hg, hs⟩
    rw [g.sign_of_cycleType]; rw [hg]; rw [neg_one_pow_eq_one_iff_even (by simp)] at hs
    contradiction

中文:
定理 map_subtype_of_cycleType
  条件: (m : Multiset 自然数)
  证明: by
  split_ifs with hm
  · ext g
    simp_rw [Finset.mem_map, Finset.mem_filter_univ, Embedding.coe_subtype, Subtype.exists,
      mem_alternatingGroup, exists_and_left, exists_prop, exists_eq_right_right,
      and_iff_left_iff_imp]
    intro hg
    rw [sign_of_cycleType]; rw [hg]; rw [Even.neg_one_pow hm]
  · rw [Finset.eq_empty_iff_forall_notMem]
    intro g hg
    simp_rw [Finset.mem_map, Finset.mem_filter_univ, Embedding.coe_subtype, Subtype.exists,
      mem_alternatingGroup, exists_and_left, exists_prop, exists_eq_right_right] at hg
    rcases hg with ⟨hg, hs⟩
    rw [g.sign_of_cycleType]; rw [hg]; rw [neg_one_pow_eq_one_iff_even (by simp)] at hs
    contradiction

Depends on / 依赖: Embedding, Embedding.coe_subtype, Even.neg_one_pow, Finset, Finset.eq_empty_iff_forall_notMem, Finset.mem_filter_univ, Finset.mem_map, Subtype, Subtype.exists, and_iff_left_iff_imp, coe_subtype, eq_empty_iff_forall_notMem, exists_and_left, exists_eq_right_right, exists_prop, mem_alternatingGroup, mem_filter_univ, mem_map, neg_one_pow, sign_of_cycleType
-/
theorem map_subtype_of_cycleType (m : Multiset Nat) :
    ({g | (g : Perm α).cycleType = m} : Finset (alternatingGroup α)).map (Embedding.subtype _) =
      if Even (m.sum + m.card) then ({g | g.cycleType = m} : Finset (Perm α)) else ∅ := by
  split_ifs with hm
  · ext g
    simp_rw [Finset.mem_map, Finset.mem_filter_univ, Embedding.coe_subtype, Subtype.exists,
      mem_alternatingGroup, exists_and_left, exists_prop, exists_eq_right_right,
      and_iff_left_iff_imp]
    intro hg
    rw [sign_of_cycleType]; rw [hg]; rw [Even.neg_one_pow hm]
  · rw [Finset.eq_empty_iff_forall_notMem]
    intro g hg
    simp_rw [Finset.mem_map, Finset.mem_filter_univ, Embedding.coe_subtype, Subtype.exists,
      mem_alternatingGroup, exists_and_left, exists_prop, exists_eq_right_right] at hg
    rcases hg with ⟨hg, hs⟩
    rw [g.sign_of_cycleType]; rw [hg]; rw [neg_one_pow_eq_one_iff_even (by simp)] at hs
    contradiction

variable (α) in
/--
theorem `card_of_cycleType_mul_eq` / 定理 `card_of_cycleType_mul_eq`

English:
theorem card_of_cycleType_mul_eq
  given: (m : Multiset Nat)
  proof: by
  rw [← Finset.card_map]; rw [map_subtype_of_cycleType]; rw [apply_ite Finset.card]; rw [Finset.card_empty]; rw [ite_mul]; rw [zero_mul]
  simp only [and_comm (b := Even _)]
  rw [ite_and]; rw [Equiv.Perm.card_of_cycleType_mul_eq]

中文:
定理 card_of_cycleType_mul_eq
  条件: (m : Multiset 自然数)
  证明: by
  rw [← Finset.card_map]; rw [map_subtype_of_cycleType]; rw [apply_ite Finset.card]; rw [Finset.card_empty]; rw [ite_mul]; rw [zero_mul]
  simp only [and_comm (b := Even _)]
  rw [ite_and]; rw [Equiv.Perm.card_of_cycleType_mul_eq]

Depends on / 依赖: Equiv.Perm.card_of_cycleType_mul_eq, Finset, Finset.card, Finset.card_empty, Finset.card_map, and_comm, apply_ite, card_empty, card_map, card_of_cycleType_mul_eq, ite_and, ite_mul, map_subtype_of_cycleType, zero_mul
-/
theorem card_of_cycleType_mul_eq (m : Multiset Nat) :
    #{g : alternatingGroup α | g.val.cycleType = m} *
        ((Fintype.card α - m.sum)! * m.prod * (∏ n in m.toFinset, (m.count n)!)) =
          if ((m.sum <= Fintype.card α ∧ forall a in m, 2 <= a) ∧ Even (m.sum + Multiset.card m))
          then (Fintype.card α)!
          else 0 := by
  rw [← Finset.card_map]; rw [map_subtype_of_cycleType]; rw [apply_ite Finset.card]; rw [Finset.card_empty]; rw [ite_mul]; rw [zero_mul]
  simp only [and_comm (b := Even _)]
  rw [ite_and]; rw [Equiv.Perm.card_of_cycleType_mul_eq]

variable (α) in
/--
theorem `card_of_cycleType` / 定理 `card_of_cycleType`

English:
theorem card_of_cycleType
  given: (m : Multiset Nat)
  proof: by
  split_ifs with hm
  · -- m is an even cycle_type
    rw [← Finset.card_map]; rw [map_subtype_of_cycleType]; rw [if_pos hm.2]; rw [Equiv.Perm.card_of_cycleType α m]; rw [if_pos hm.1]; rw [mul_assoc]
  · -- m does not correspond to a permutation, or to an odd one,
    rw [← Finset.card_map]; rw [map_subtype_of_cycleType]
    rw [apply_ite Finset.card]; rw [Finset.card_empty]
    split_ifs with hm'
    · rw [Equiv.Perm.card_of_cycleType, if_neg]
      obtain hm | hm := not_and_or.mp hm
      · exact hm
      · contradiction
    · rfl

中文:
定理 card_of_cycleType
  条件: (m : Multiset 自然数)
  证明: by
  split_ifs with hm
  · -- m is an even cycle_type
    rw [← Finset.card_map]; rw [map_subtype_of_cycleType]; rw [if_pos hm.2]; rw [Equiv.Perm.card_of_cycleType α m]; rw [if_pos hm.1]; rw [mul_assoc]
  · -- m does not correspond to a permutation, or to an odd one,
    rw [← Finset.card_map]; rw [map_subtype_of_cycleType]
    rw [apply_ite Finset.card]; rw [Finset.card_empty]
    split_ifs with hm'
    · rw [Equiv.Perm.card_of_cycleType, if_neg]
      obtain hm | hm := not_and_or.mp hm
      · exact hm
      · contradiction
    · rfl

Depends on / 依赖: Equiv.Perm.card_of_cycleType, Finset, Finset.card, Finset.card_empty, Finset.card_map, apply_ite, card_empty, card_map, card_of_cycleType, correspond, cycle_type, if_neg, if_pos, map_subtype_of_cycleType, mul_assoc, not_and_or, not_and_or.mp, permutation, split_ifs
-/
theorem card_of_cycleType (m : Multiset Nat) :
    #{g : alternatingGroup α | (g : Equiv.Perm α).cycleType = m} =
      if (m.sum <= Fintype.card α ∧ forall a in m, 2 <= a) ∧ Even (m.sum + Multiset.card m) then
        (Fintype.card α)! /
          ((Fintype.card α - m.sum)! *
            (m.prod * (∏ n in m.toFinset, (m.count n)!)))
      else 0 := by
  split_ifs with hm
  · -- m is an even cycle_type
    rw [← Finset.card_map]; rw [map_subtype_of_cycleType]; rw [if_pos hm.2]; rw [Equiv.Perm.card_of_cycleType α m]; rw [if_pos hm.1]; rw [mul_assoc]
  · -- m does not correspond to a permutation, or to an odd one,
    rw [← Finset.card_map]; rw [map_subtype_of_cycleType]
    rw [apply_ite Finset.card]; rw [Finset.card_empty]
    split_ifs with hm'
    · rw [Equiv.Perm.card_of_cycleType, if_neg]
      obtain hm | hm := not_and_or.mp hm
      · exact hm
      · contradiction
    · rfl

open Fintype in
/--
lemma `card_of_cycleType_singleton` / 引理 `card_of_cycleType_singleton`

English:
lemma card_of_cycleType_singleton
  given: {n : Nat} (hn : 2 <= n) (hα : n <= card α)
  proof: by
  rw [← card_map]; rw [map_subtype_of_cycleType]; rw [apply_ite Finset.card]
  simp only [Multiset.sum_singleton, Multiset.card_singleton, Finset.card_empty]
  simp_rw [← Nat.not_odd_iff_even, Nat.odd_add_one, not_not,
    Perm.card_of_cycleType_singleton hn hα]

中文:
引理 card_of_cycleType_singleton
  条件: {n : 自然数} (hn : 2 <= n) (hα : n <= card α)
  证明: by
  rw [← card_map]; rw [map_subtype_of_cycleType]; rw [apply_ite Finset.card]
  simp only [Multiset.sum_singleton, Multiset.card_singleton, Finset.card_empty]
  simp_rw [← Nat.not_odd_iff_even, Nat.odd_add_one, not_not,
    Perm.card_of_cycleType_singleton hn hα]

Depends on / 依赖: Finset, Finset.card, Finset.card_empty, Multiset, Multiset.card_singleton, Multiset.sum_singleton, Nat.not_odd_iff_even, Nat.odd_add_one, Perm.card_of_cycleType_singleton, apply_ite, card_empty, card_map, card_of_cycleType_singleton, card_singleton, map_subtype_of_cycleType, not_not, not_odd_iff_even, odd_add_one, simp_rw, sum_singleton
-/
lemma card_of_cycleType_singleton {n : Nat} (hn : 2 <= n) (hα : n <= card α) :
    #{g : alternatingGroup α | g.val.cycleType = {n}} =
      if Odd n then (n - 1)! * (choose (card α) n) else 0 := by
  rw [← card_map]; rw [map_subtype_of_cycleType]; rw [apply_ite Finset.card]
  simp only [Multiset.sum_singleton, Multiset.card_singleton, Finset.card_empty]
  simp_rw [← Nat.not_odd_iff_even, Nat.odd_add_one, not_not,
    Perm.card_of_cycleType_singleton hn hα]

end AlternatingGroup

namespace Equiv.Perm

open Basis OnCycleFactors

/--
theorem `card_le_of_centralizer_le_alternating` / 定理 `card_le_of_centralizer_le_alternating`

English:
theorem card_le_of_centralizer_le_alternating
  given: (h : Subgroup.centralizer {g} <= alternatingGroup α)
  proof: by
  by_contra! hm
  replace hm : 2 + g.cycleType.sum <= Fintype.card α := by lia
  suffices 1 < Fintype.card (Function.fixedPoints g) by
    obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card this
    suffices sign (kerParam g ⟨swap a b, 1⟩) != 1 from
      this (h (kerParam_range_le_centralizer (Set.mem_range_self _)))
    simp [sign_kerParam_apply_apply, hab]
  rwa [card_fixedPoints g, Nat.lt_iff_add_one_le, Nat.le_sub_iff_add_le]
  rw [sum_cycleType]
  exact Finset.card_le_univ _

中文:
定理 card_le_of_centralizer_le_alternating
  条件: (h : 子群.centralizer {g} <= alternatingGroup α)
  证明: by
  by_contra! hm
  replace hm : 2 + g.cycleType.sum <= Fintype.card α := by lia
  suffices 1 < Fintype.card (Function.fixedPoints g) by
    obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card this
    suffices sign (kerParam g ⟨swap a b, 1⟩) != 1 from
      this (h (kerParam_range_le_centralizer (Set.mem_range_self _)))
    simp [sign_kerParam_apply_apply, hab]
  rwa [card_fixedPoints g, Nat.lt_iff_add_one_le, Nat.le_sub_iff_add_le]
  rw [sum_cycleType]
  exact Finset.card_le_univ _

Depends on / 依赖: Finset, Finset.card_le_univ, Fintype, Fintype.card, Fintype.exists_pair_of_one_lt_card, Function, Function.fixedPoints, Nat.le_sub_iff_add_le, Nat.lt_iff_add_one_le, Set.mem_range_self, card_fixedPoints, card_le_univ, cycleType, exists_pair_of_one_lt_card, fixedPoints, g.cycleType.sum, kerParam, kerParam_range_le_centralizer, le_sub_iff_add_le, lt_iff_add_one_le
-/
theorem card_le_of_centralizer_le_alternating (h : Subgroup.centralizer {g} <= alternatingGroup α) :
    Fintype.card α <= g.cycleType.sum + 1 := by
  by_contra! hm
  replace hm : 2 + g.cycleType.sum <= Fintype.card α := by lia
  suffices 1 < Fintype.card (Function.fixedPoints g) by
    obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card this
    suffices sign (kerParam g ⟨swap a b, 1⟩) != 1 from
      this (h (kerParam_range_le_centralizer (Set.mem_range_self _)))
    simp [sign_kerParam_apply_apply, hab]
  rwa [card_fixedPoints g, Nat.lt_iff_add_one_le, Nat.le_sub_iff_add_le]
  rw [sum_cycleType]
  exact Finset.card_le_univ _

/--
theorem `count_le_one_of_centralizer_le_alternating` / 定理 `count_le_one_of_centralizer_le_alternating`

English:
theorem count_le_one_of_centralizer_le_alternating
  proof: by
  rw [← Multiset.nodup_iff_count_le_one]; rw [Equiv.Perm.cycleType_def]
  rw [Multiset.nodup_map_iff_inj_on g.cycleFactorsFinset.nodup]
  simp only [Function.comp_apply, ← Finset.mem_def]
  by_contra! ⟨c, hc, d, hd, hm, hm'⟩
  let τ : Equiv.Perm g.cycleFactorsFinset := Equiv.swap ⟨c, hc⟩ ⟨d, hd⟩
  obtain ⟨a⟩ := Equiv.Perm.Basis.nonempty g
  have hτ : τ in range_toPermHom' g := fun x => by
    by_cases hx : x = ⟨c, hc⟩
    · rw [hx, Equiv.swap_apply_left]; exact hm.symm
    by_cases hx' : x = ⟨d, hd⟩
    · rw [hx', Equiv.swap_apply_right]; exact hm
    · rw [Equiv.swap_apply_of_ne_of_ne hx hx']
  set k := toCentralizer a ⟨τ, hτ⟩ with hk
  suffices hsign_k : k.val.sign = -1 by
    apply units_ne_neg_self (1 : Intˣ)
    rw [← hsign_k]; rw [h (toCentralizer a ⟨τ]; rw [hτ⟩).prop]
  /- to prove that `hsign_k : sign k = -1` below,
  we could prove that it is the product of the transpositions with disjoint supports
  [(g ^ n) (a c), (g ^ n) (a d)], for 0 ≤ n < c.support.card,
  which are in odd number by `odd_of_centralizer_le_alternatingGroup`,
  but it will be sufficient to observe that `k ^ 2 = 1`
  (which implies that `k.cycleType` is of the form (2,2,…))
  and to control its support. -/
  have hk_cT : k.val.cycleType = Multiset.replicate k.val.cycleType.card 2 := by
    rw [Multiset.eq_replicate_card]; rw [← pow_prime_eq_one_iff]; rw [← Subgroup.coe_pow]; rw [← Subgroup.coe_one]; rw [Subtype.coe_inj]; rw [hk]; rw [← map_pow]
    convert! MonoidHom.map_one _
    rw [← Subtype.coe_inj]
    apply Equiv.swap_mul_self
  rw [sign_of_cycleType]; rw [hk_cT]
  simp only [Multiset.sum_replicate, smul_eq_mul, Multiset.card_replicate, pow_add,
    even_two, Even.mul_left, Even.neg_pow, one_pow, one_mul]
  apply Odd.neg_one_pow
  apply odd_of_centralizer_le_alternatingGroup h
  have : (k : Perm α).cycleType.card * 2 = (k : Perm α).support.card := by
    rw [← sum_cycleType]; rw [hk_cT]
    simp
  have that : Multiset.card (k : Perm α).cycleType = (c : Perm α).support.card := by
    rw [← Nat.mul_left_inj (a := 2) (by simp)]; rw [this]
    simp only [hk, toCentralizer, MonoidHom.coe_mk, OneHom.coe_mk, card_ofPermHom_support]
    have H : (⟨c, hc⟩ : g.cycleFactorsFinset) != ⟨d, hd⟩ := Subtype.coe_ne_coe.mp hm'
    simp only [τ, support_swap H]
    rw [Finset.sum_insert (by simp only [mem_singleton]; rw [H]; rw [not_false_eq_true]),
      Finset.sum_singleton, hm, mul_two]
  rw [that]
  simp only [cycleType_def, Multiset.mem_map]
  exact ⟨c, hc, by simp only [Function.comp_apply]⟩

中文:
定理 count_le_one_of_centralizer_le_alternating
  证明: by
  rw [← Multiset.nodup_iff_count_le_one]; rw [Equiv.Perm.cycleType_def]
  rw [Multiset.nodup_map_iff_inj_on g.cycleFactorsFinset.nodup]
  simp only [Function.comp_apply, ← Finset.mem_def]
  by_contra! ⟨c, hc, d, hd, hm, hm'⟩
  let τ : Equiv.Perm g.cycleFactorsFinset := Equiv.swap ⟨c, hc⟩ ⟨d, hd⟩
  obtain ⟨a⟩ := Equiv.Perm.Basis.nonempty g
  have hτ : τ in range_toPermHom' g := fun x => by
    by_cases hx : x = ⟨c, hc⟩
    · rw [hx, Equiv.swap_apply_left]; exact hm.symm
    by_cases hx' : x = ⟨d, hd⟩
    · rw [hx', Equiv.swap_apply_right]; exact hm
    · rw [Equiv.swap_apply_of_ne_of_ne hx hx']
  set k := toCentralizer a ⟨τ, hτ⟩ with hk
  suffices hsign_k : k.val.sign = -1 by
    apply units_ne_neg_self (1 : Intˣ)
    rw [← hsign_k]; rw [h (toCentralizer a ⟨τ]; rw [hτ⟩).prop]
  /- to prove that `hsign_k : sign k = -1` below,
  we could prove that it is the product of the transpositions with disjoint supports
  [(g ^ n) (a c), (g ^ n) (a d)], for 0 ≤ n < c.support.card,
  which are in odd number by `odd_of_centralizer_le_alternatingGroup`,
  but it will be sufficient to observe that `k ^ 2 = 1`
  (which implies that `k.cycleType` is of the form (2,2,…))
  and to control its support. -/
  have hk_cT : k.val.cycleType = Multiset.replicate k.val.cycleType.card 2 := by
    rw [Multiset.eq_replicate_card]; rw [← pow_prime_eq_one_iff]; rw [← Subgroup.coe_pow]; rw [← Subgroup.coe_one]; rw [Subtype.coe_inj]; rw [hk]; rw [← map_pow]
    convert! MonoidHom.map_one _
    rw [← Subtype.coe_inj]
    apply Equiv.swap_mul_self
  rw [sign_of_cycleType]; rw [hk_cT]
  simp only [Multiset.sum_replicate, smul_eq_mul, Multiset.card_replicate, pow_add,
    even_two, Even.mul_left, Even.neg_pow, one_pow, one_mul]
  apply Odd.neg_one_pow
  apply odd_of_centralizer_le_alternatingGroup h
  have : (k : Perm α).cycleType.card * 2 = (k : Perm α).support.card := by
    rw [← sum_cycleType]; rw [hk_cT]
    simp
  have that : Multiset.card (k : Perm α).cycleType = (c : Perm α).support.card := by
    rw [← Nat.mul_left_inj (a := 2) (by simp)]; rw [this]
    simp only [hk, toCentralizer, MonoidHom.coe_mk, OneHom.coe_mk, card_ofPermHom_support]
    have H : (⟨c, hc⟩ : g.cycleFactorsFinset) != ⟨d, hd⟩ := Subtype.coe_ne_coe.mp hm'
    simp only [τ, support_swap H]
    rw [Finset.sum_insert (by simp only [mem_singleton]; rw [H]; rw [not_false_eq_true]),
      Finset.sum_singleton, hm, mul_two]
  rw [that]
  simp only [cycleType_def, Multiset.mem_map]
  exact ⟨c, hc, by simp only [Function.comp_apply]⟩

Depends on / 依赖: Equiv.Perm, Equiv.Perm.Basis.nonempty, Equiv.Perm.cycleType_def, Equiv.s, Equiv.swap, Equiv.swap_apply_left, Finset, Finset.mem_def, Function, Function.comp_apply, Multiset, Multiset.nodup_iff_count_le_one, Multiset.nodup_map_iff_inj_on, comp_apply, cycleFactorsFinset, cycleType_def, g.cycleFactorsFinset, g.cycleFactorsFinset.nodup, hm.symm, mem_def
-/
theorem count_le_one_of_centralizer_le_alternating
    (h : Subgroup.centralizer {g} <= alternatingGroup α) :
    forall i, g.cycleType.count i <= 1 := by
  rw [← Multiset.nodup_iff_count_le_one]; rw [Equiv.Perm.cycleType_def]
  rw [Multiset.nodup_map_iff_inj_on g.cycleFactorsFinset.nodup]
  simp only [Function.comp_apply, ← Finset.mem_def]
  by_contra! ⟨c, hc, d, hd, hm, hm'⟩
  let τ : Equiv.Perm g.cycleFactorsFinset := Equiv.swap ⟨c, hc⟩ ⟨d, hd⟩
  obtain ⟨a⟩ := Equiv.Perm.Basis.nonempty g
  have hτ : τ in range_toPermHom' g := fun x => by
    by_cases hx : x = ⟨c, hc⟩
    · rw [hx, Equiv.swap_apply_left]; exact hm.symm
    by_cases hx' : x = ⟨d, hd⟩
    · rw [hx', Equiv.swap_apply_right]; exact hm
    · rw [Equiv.swap_apply_of_ne_of_ne hx hx']
  set k := toCentralizer a ⟨τ, hτ⟩ with hk
  suffices hsign_k : k.val.sign = -1 by
    apply units_ne_neg_self (1 : Intˣ)
    rw [← hsign_k]; rw [h (toCentralizer a ⟨τ]; rw [hτ⟩).prop]
  /- to prove that `hsign_k : sign k = -1` below,
  we could prove that it is the product of the transpositions with disjoint supports
  [(g ^ n) (a c), (g ^ n) (a d)], for 0 ≤ n < c.support.card,
  which are in odd number by `odd_of_centralizer_le_alternatingGroup`,
  but it will be sufficient to observe that `k ^ 2 = 1`
  (which implies that `k.cycleType` is of the form (2,2,…))
  and to control its support. -/
  have hk_cT : k.val.cycleType = Multiset.replicate k.val.cycleType.card 2 := by
    rw [Multiset.eq_replicate_card]; rw [← pow_prime_eq_one_iff]; rw [← Subgroup.coe_pow]; rw [← Subgroup.coe_one]; rw [Subtype.coe_inj]; rw [hk]; rw [← map_pow]
    convert! MonoidHom.map_one _
    rw [← Subtype.coe_inj]
    apply Equiv.swap_mul_self
  rw [sign_of_cycleType]; rw [hk_cT]
  simp only [Multiset.sum_replicate, smul_eq_mul, Multiset.card_replicate, pow_add,
    even_two, Even.mul_left, Even.neg_pow, one_pow, one_mul]
  apply Odd.neg_one_pow
  apply odd_of_centralizer_le_alternatingGroup h
  have : (k : Perm α).cycleType.card * 2 = (k : Perm α).support.card := by
    rw [← sum_cycleType]; rw [hk_cT]
    simp
  have that : Multiset.card (k : Perm α).cycleType = (c : Perm α).support.card := by
    rw [← Nat.mul_left_inj (a := 2) (by simp)]; rw [this]
    simp only [hk, toCentralizer, MonoidHom.coe_mk, OneHom.coe_mk, card_ofPermHom_support]
    have H : (⟨c, hc⟩ : g.cycleFactorsFinset) != ⟨d, hd⟩ := Subtype.coe_ne_coe.mp hm'
    simp only [τ, support_swap H]
    rw [Finset.sum_insert (by simp only [mem_singleton]; rw [H]; rw [not_false_eq_true]),
      Finset.sum_singleton, hm, mul_two]
  rw [that]
  simp only [cycleType_def, Multiset.mem_map]
  exact ⟨c, hc, by simp only [Function.comp_apply]⟩

/--
theorem `OnCycleFactors.kerParam_range_eq_centralizer_of_count_le_one` / 定理 `OnCycleFactors.kerParam_range_eq_centralizer_of_count_le_one`

English:
theorem OnCycleFactors.kerParam_range_eq_centralizer_of_count_le_one
  proof: by
  ext x
  refine ⟨fun hx => kerParam_range_le_centralizer hx, fun hx => ?_⟩
  simp_rw [kerParam_range_eq, Subgroup.mem_map, MonoidHom.mem_ker, Subgroup.coe_subtype,
    Subtype.exists, exists_and_right, exists_eq_right]
  use hx
  ext c : 2
  rw [← Multiset.nodup_iff_count_le_one]; rw [cycleType_def]; rw [Multiset.nodup_map_iff_inj_on (cycleFactorsFinset g).nodup] at h_count
  exact h_count _ (by simp) _ c.prop (mem_range_toPermHom_iff.mp (by simp) c)

中文:
定理 OnCycleFactors.kerParam_range_eq_centralizer_of_count_le_one
  证明: by
  ext x
  refine ⟨fun hx => kerParam_range_le_centralizer hx, fun hx => ?_⟩
  simp_rw [kerParam_range_eq, Subgroup.mem_map, MonoidHom.mem_ker, Subgroup.coe_subtype,
    Subtype.exists, exists_and_right, exists_eq_right]
  use hx
  ext c : 2
  rw [← Multiset.nodup_iff_count_le_one]; rw [cycleType_def]; rw [Multiset.nodup_map_iff_inj_on (cycleFactorsFinset g).nodup] at h_count
  exact h_count _ (by simp) _ c.prop (mem_range_toPermHom_iff.mp (by simp) c)

Depends on / 依赖: MonoidHom, MonoidHom.mem_ker, Multiset, Multiset.nodup_iff_count_le_one, Multiset.nodup_map_iff_inj_on, Subgroup, Subgroup.coe_subtype, Subgroup.mem_map, Subtype, Subtype.exists, c.prop, coe_subtype, cycleFactorsFinset, cycleType_def, exists_and_right, exists_eq_right, h_count, kerParam_range_eq, kerParam_range_le_centralizer, mem_ker
-/
theorem OnCycleFactors.kerParam_range_eq_centralizer_of_count_le_one
    (h_count : forall i, g.cycleType.count i <= 1) :
    (kerParam g).range = Subgroup.centralizer {g} := by
  ext x
  refine ⟨fun hx => kerParam_range_le_centralizer hx, fun hx => ?_⟩
  simp_rw [kerParam_range_eq, Subgroup.mem_map, MonoidHom.mem_ker, Subgroup.coe_subtype,
    Subtype.exists, exists_and_right, exists_eq_right]
  use hx
  ext c : 2
  rw [← Multiset.nodup_iff_count_le_one]; rw [cycleType_def]; rw [Multiset.nodup_map_iff_inj_on (cycleFactorsFinset g).nodup] at h_count
  exact h_count _ (by simp) _ c.prop (mem_range_toPermHom_iff.mp (by simp) c)

/--
theorem `centralizer_le_alternating_iff` / 定理 `centralizer_le_alternating_iff`

English:
theorem centralizer_le_alternating_iff
  proof: by
  rw [SetLike.le_def]
  constructor
  · intro h
    exact ⟨odd_of_centralizer_le_alternatingGroup h,
      card_le_of_centralizer_le_alternating h,
      count_le_one_of_centralizer_le_alternating h⟩
  · rintro ⟨h_odd, h_fixed, h_count⟩ x hx
    rw [← kerParam_range_eq_centralizer_of_count_le_one h_count] at hx
    obtain ⟨⟨y, uv⟩, rfl⟩ := MonoidHom.mem_range.mp hx
    rw [mem_alternatingGroup]; rw [sign_kerParam_apply_apply (g := g) y uv]
    convert! mul_one _
    · apply Finset.prod_eq_one
      rintro ⟨c, hc⟩ _
      obtain ⟨k, hk⟩ := (uv _).prop
      rw [← hk]; rw [map_zpow]
      convert! one_zpow k
      rw [IsCycle.sign]; rw [Odd.neg_one_pow]; rw [neg_neg]
      · apply h_odd
        rw [cycleType_def]; rw [Multiset.mem_map]
        exact ⟨c, hc, rfl⟩
      · rw [mem_cycleFactorsFinset_iff] at hc
        exact hc.left
    · suffices y = 1 by simp [this]
      have := card_fixedPoints g
exact card_support_le_one.mp le_trans (Finset.card_le_univ _) (by lia)

中文:
定理 centralizer_le_alternating_iff
  证明: by
  rw [SetLike.le_def]
  constructor
  · intro h
    exact ⟨odd_of_centralizer_le_alternatingGroup h,
      card_le_of_centralizer_le_alternating h,
      count_le_one_of_centralizer_le_alternating h⟩
  · rintro ⟨h_odd, h_fixed, h_count⟩ x hx
    rw [← kerParam_range_eq_centralizer_of_count_le_one h_count] at hx
    obtain ⟨⟨y, uv⟩, rfl⟩ := MonoidHom.mem_range.mp hx
    rw [mem_alternatingGroup]; rw [sign_kerParam_apply_apply (g := g) y uv]
    convert! mul_one _
    · apply Finset.prod_eq_one
      rintro ⟨c, hc⟩ _
      obtain ⟨k, hk⟩ := (uv _).prop
      rw [← hk]; rw [map_zpow]
      convert! one_zpow k
      rw [IsCycle.sign]; rw [Odd.neg_one_pow]; rw [neg_neg]
      · apply h_odd
        rw [cycleType_def]; rw [Multiset.mem_map]
        exact ⟨c, hc, rfl⟩
      · rw [mem_cycleFactorsFinset_iff] at hc
        exact hc.left
    · suffices y = 1 by simp [this]
      have := card_fixedPoints g
exact card_support_le_one.mp le_trans (Finset.card_le_univ _) (by lia)

Depends on / 依赖: Finset, Finset.prod_eq_one, MonoidHom, MonoidHom.mem_range.mp, SetLike, SetLike.le_def, card_le_of_centralizer_le_alternating, convert, count_le_one_of_centralizer_le_alternating, h_count, h_fixed, h_odd, kerParam_range_eq_centralizer_of_count_le_one, le_def, mem_alternatingGroup, mem_range, mul_one, odd_of_centralizer_le_alternatingGroup, prod_eq_one, sign_kerParam_apply_apply
-/
theorem centralizer_le_alternating_iff :
    Subgroup.centralizer {g} <= alternatingGroup α ↔
      (forall c in g.cycleType, Odd c) ∧ Fintype.card α <= g.cycleType.sum + 1 ∧
        forall i, g.cycleType.count i <= 1 := by
  rw [SetLike.le_def]
  constructor
  · intro h
    exact ⟨odd_of_centralizer_le_alternatingGroup h,
      card_le_of_centralizer_le_alternating h,
      count_le_one_of_centralizer_le_alternating h⟩
  · rintro ⟨h_odd, h_fixed, h_count⟩ x hx
    rw [← kerParam_range_eq_centralizer_of_count_le_one h_count] at hx
    obtain ⟨⟨y, uv⟩, rfl⟩ := MonoidHom.mem_range.mp hx
    rw [mem_alternatingGroup]; rw [sign_kerParam_apply_apply (g := g) y uv]
    convert! mul_one _
    · apply Finset.prod_eq_one
      rintro ⟨c, hc⟩ _
      obtain ⟨k, hk⟩ := (uv _).prop
      rw [← hk]; rw [map_zpow]
      convert! one_zpow k
      rw [IsCycle.sign]; rw [Odd.neg_one_pow]; rw [neg_neg]
      · apply h_odd
        rw [cycleType_def]; rw [Multiset.mem_map]
        exact ⟨c, hc, rfl⟩
      · rw [mem_cycleFactorsFinset_iff] at hc
        exact hc.left
    · suffices y = 1 by simp [this]
      have := card_fixedPoints g
exact card_support_le_one.mp le_trans (Finset.card_le_univ _) (by lia)

namespace IsThreeCycle

variable (h5 : 5 <= Nat.card α) {g : alternatingGroup α} (hg : IsThreeCycle (g : Perm α))

include h5 hg

/--
theorem `mem_commutatorSet_alternatingGroup` / 定理 `mem_commutatorSet_alternatingGroup`

English:
theorem mem_commutatorSet_alternatingGroup
  statement: g in commutatorSet (alternatingGroup α)
  proof: by
  apply mem_commutatorSet_of_isConj_sq
  apply alternatingGroup.isThreeCycle_isConj h5 hg
  simpa [sq] using hg.isThreeCycle_sq

中文:
定理 mem_commutatorSet_alternatingGroup
  结论: g in commutatorSet (alternatingGroup α)
  证明: by
  apply mem_commutatorSet_of_isConj_sq
  apply alternatingGroup.isThreeCycle_isConj h5 hg
  simpa [sq] using hg.isThreeCycle_sq

Depends on / 依赖: alternatingGroup, alternatingGroup.isThreeCycle_isConj, hg.isThreeCycle_sq, isThreeCycle_isConj, isThreeCycle_sq, mem_commutatorSet_of_isConj_sq
-/
theorem mem_commutatorSet_alternatingGroup : g in commutatorSet (alternatingGroup α) := by
  apply mem_commutatorSet_of_isConj_sq
  apply alternatingGroup.isThreeCycle_isConj h5 hg
  simpa [sq] using hg.isThreeCycle_sq

/--
theorem `mem_commutator_alternatingGroup` / 定理 `mem_commutator_alternatingGroup`

English:
theorem mem_commutator_alternatingGroup
  statement: g in commutator (alternatingGroup α)
  proof: by
  rw [commutator_eq_closure]
  apply Subgroup.subset_closure
  exact hg.mem_commutatorSet_alternatingGroup h5

中文:
定理 mem_commutator_alternatingGroup
  结论: g in commutator (alternatingGroup α)
  证明: by
  rw [commutator_eq_closure]
  apply Subgroup.subset_closure
  exact hg.mem_commutatorSet_alternatingGroup h5

Depends on / 依赖: Subgroup, Subgroup.subset_closure, commutator_eq_closure, hg.mem_commutatorSet_alternatingGroup, mem_commutatorSet_alternatingGroup, subset_closure
-/
theorem mem_commutator_alternatingGroup : g in commutator (alternatingGroup α) := by
  rw [commutator_eq_closure]
  apply Subgroup.subset_closure
  exact hg.mem_commutatorSet_alternatingGroup h5

end IsThreeCycle

end Equiv.Perm

section Perfect

open Subgroup Equiv.Perm

/--
theorem `alternatingGroup.commutator_perm_le` / 定理 `alternatingGroup.commutator_perm_le`

English:
theorem alternatingGroup.commutator_perm_le
  proof: by
  simp only [commutator_eq_closure, closure_le, Set.subset_def, mem_commutatorSet_iff,
    SetLike.mem_coe, mem_alternatingGroup, forall_exists_index]
  rintro _ p q rfl
  simp [map_commutatorElement, commutatorElement_eq_one_iff_commute, Commute.all]

中文:
定理 alternatingGroup.commutator_perm_le
  证明: by
  simp only [commutator_eq_closure, closure_le, Set.subset_def, mem_commutatorSet_iff,
    SetLike.mem_coe, mem_alternatingGroup, forall_exists_index]
  rintro _ p q rfl
  simp [map_commutatorElement, commutatorElement_eq_one_iff_commute, Commute.all]

Depends on / 依赖: Commute, Commute.all, Set.subset_def, SetLike, SetLike.mem_coe, closure_le, commutatorElement_eq_one_iff_commute, commutator_eq_closure, forall_exists_index, map_commutatorElement, mem_alternatingGroup, mem_coe, mem_commutatorSet_iff, subset_def
-/
theorem alternatingGroup.commutator_perm_le :
    commutator (Perm α) <= alternatingGroup α := by
  simp only [commutator_eq_closure, closure_le, Set.subset_def, mem_commutatorSet_iff,
    SetLike.mem_coe, mem_alternatingGroup, forall_exists_index]
  rintro _ p q rfl
  simp [map_commutatorElement, commutatorElement_eq_one_iff_commute, Commute.all]

/--
theorem `commutator_alternatingGroup_eq_top` / 定理 `commutator_alternatingGroup_eq_top`

English:
theorem commutator_alternatingGroup_eq_top
  given: (h5 : 5 <= Nat.card α)
  proof: by
  suffices closure {b : alternatingGroup α | (b : Perm α).IsThreeCycle} = ⊤ by
    rw [eq_top_iff]; rw [← this]; rw [Subgroup.closure_le]
    intro b hb
    exact hb.mem_commutator_alternatingGroup h5
  rw [← closure_three_cycles_eq_alternating]
  exact Subgroup.closure_closure_coe_preimage

中文:
定理 commutator_alternatingGroup_eq_top
  条件: (h5 : 5 <= 自然数.card α)
  证明: by
  suffices closure {b : alternatingGroup α | (b : Perm α).IsThreeCycle} = ⊤ by
    rw [eq_top_iff]; rw [← this]; rw [Subgroup.closure_le]
    intro b hb
    exact hb.mem_commutator_alternatingGroup h5
  rw [← closure_three_cycles_eq_alternating]
  exact Subgroup.closure_closure_coe_preimage

Depends on / 依赖: IsThreeCycle, Subgroup, Subgroup.closure_closure_coe_preimage, Subgroup.closure_le, alternatingGroup, closure, closure_closure_coe_preimage, closure_le, closure_three_cycles_eq_alternating, eq_top_iff, hb.mem_commutator_alternatingGroup, mem_commutator_alternatingGroup
-/
theorem commutator_alternatingGroup_eq_top (h5 : 5 <= Nat.card α) :
    commutator (alternatingGroup α) = ⊤ := by
  suffices closure {b : alternatingGroup α | (b : Perm α).IsThreeCycle} = ⊤ by
    rw [eq_top_iff]; rw [← this]; rw [Subgroup.closure_le]
    intro b hb
    exact hb.mem_commutator_alternatingGroup h5
  rw [← closure_three_cycles_eq_alternating]
  exact Subgroup.closure_closure_coe_preimage

/--
theorem `commutator_alternatingGroup_eq_self` / 定理 `commutator_alternatingGroup_eq_self`

English:
theorem commutator_alternatingGroup_eq_self
  given: (h5 : 5 <= Nat.card α)
  proof: by
  rw [← Subgroup.map_subtype_commutator]; rw [commutator_alternatingGroup_eq_top h5]; rw [← MonoidHom.range_eq_map]; rw [Subgroup.range_subtype]

中文:
定理 commutator_alternatingGroup_eq_self
  条件: (h5 : 5 <= 自然数.card α)
  证明: by
  rw [← Subgroup.map_subtype_commutator]; rw [commutator_alternatingGroup_eq_top h5]; rw [← MonoidHom.range_eq_map]; rw [Subgroup.range_subtype]

Depends on / 依赖: MonoidHom, MonoidHom.range_eq_map, Subgroup, Subgroup.map_subtype_commutator, Subgroup.range_subtype, commutator_alternatingGroup_eq_top, map_subtype_commutator, range_eq_map, range_subtype
-/
theorem commutator_alternatingGroup_eq_self (h5 : 5 <= Nat.card α) :
    ⁅alternatingGroup α, alternatingGroup α⁆ = alternatingGroup α := by
  rw [← Subgroup.map_subtype_commutator]; rw [commutator_alternatingGroup_eq_top h5]; rw [← MonoidHom.range_eq_map]; rw [Subgroup.range_subtype]

/--
theorem `alternatingGroup.commutator_perm_eq` / 定理 `alternatingGroup.commutator_perm_eq`

English:
theorem alternatingGroup.commutator_perm_eq
  given: (h5 : 5 <= Nat.card α)
  proof: by
  apply le_antisymm alternatingGroup.commutator_perm_le
  rw [← commutator_alternatingGroup_eq_self h5]
  exact commutator_mono le_top le_top

中文:
定理 alternatingGroup.commutator_perm_eq
  条件: (h5 : 5 <= 自然数.card α)
  证明: by
  apply le_antisymm alternatingGroup.commutator_perm_le
  rw [← commutator_alternatingGroup_eq_self h5]
  exact commutator_mono le_top le_top

Depends on / 依赖: alternatingGroup, alternatingGroup.commutator_perm_le, commutator_alternatingGroup_eq_self, commutator_mono, commutator_perm_le, le_antisymm, le_top
-/
theorem alternatingGroup.commutator_perm_eq (h5 : 5 <= Nat.card α) :
    commutator (Perm α) = alternatingGroup α := by
  apply le_antisymm alternatingGroup.commutator_perm_le
  rw [← commutator_alternatingGroup_eq_self h5]
  exact commutator_mono le_top le_top

end Perfect
