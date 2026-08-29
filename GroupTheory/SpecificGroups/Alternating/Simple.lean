/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module


public import Mathlib.GroupTheory.GroupAction.Iwasawa
public import Mathlib.GroupTheory.GroupAction.SubMulAction.Combination
public import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour

/-! # The alternating group is simple

## Main results

* `Equiv.Perm.alternatingGroup_le_of_normal`:
  If `α` has at least 5 elements, then a nontrivial normal subgroup
  of `Equiv.Perm α` contains the alternating group.

* `alternatingGroup.normal_subgroup_eq_bot_or_eq_top`:
  If `α` has at least 5 elements, then a nontrivial normal subgroup of `alternatingGroup` is `⊤`.

* `alternatingGroup.isSimpleGroup`:
  If `α` has at least 5 elements, then `alternatingGroup α` is a simple group.

## Main definitions

The proofs of the above results follow from the Iwasawa criterion
applied to the following Iwasawa structures. Their definitions are similar:
the groups `Equiv.Perm α` and `alternatingGroup α` act on `α` hence
they act on `Set.powersetCard α n`, for any natural number `n`.
For `n = 2`, this gives an Iwaswa structure of `Equiv.Perm α`,
for `n = 3` or `n = 4`, this gives an Iwasawa structure of `alternatingGroup α`.

* `Equiv.Perm.iwasawaStructure_two`:
  the natural `IwasawaStructure` of `Equiv.Perm α` acting on `Set.powersetCard α 2`.
  Its commutative subgroups consist of the permutations with support in a given element
  of `Set.powersetCard α 2`. They are cyclic of order 2.

* `alternatingGroup.iwasawaStructure_three`:
  the natural `IwasawaStructure` of `alternatingGroup α` acting on `Set.powersetCard α 3`.

  Its commutative subgroups consist of the permutations with support
  in a given element of `Set.powersetCard α 2`. They are cyclic of order 3.

* `alternatingGroup.iwasawaStructure_four`:
  the natural `IwasawaStructure` of `alternatingGroup α` acting on `Set.powersetCard α 4`

  Its commutative subgroups consist of the permutations of cycleType (2, 2) with support
  in a given element of `Set.powersetCard α 2`. They have order 4 and exponent 2 (`IsKleinFour`).

## TODO

This file contains one uncomfortable use of `convert`: on line 78, to identify `MulAut.conj`
and `ConjAct.toConjAct`.

-/

@[expose] public section

open scoped Pointwise

open MulAction Equiv.Perm Equiv Set.powersetCard Subgroup

namespace Equiv.Perm

variable {α : Type*} [Finite α] [DecidableEq α]

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `iwasawaStructure_two` / `iwasawaStructure_two` 的定义

English:
definition iwasawaStructure_two
  signature: [forall s : Set α, DecidablePred fun x => x in s]
  body: (ofSubtype : Perm (s : Set α) ->* Perm α).range
  is_comm s := by
    have : IsMulCommutative (Perm s) := isMulCommutative_iff_card_le_two.mpr (by simp)
    infer_instance
  is_conj g s := by
    convert! (conj_smul_range_ofSubtype g s).symm
  is_generator := by
    rw [eq_top_iff]; rw [← Equiv.Perm.closure_isSwap]; rw [Subgroup.closure_le]
    rintro g ⟨a, b, hab, rfl⟩
    apply Subgroup.mem_iSup_of_mem ⟨{a, b}, Finset.card_pair hab⟩
    exact ⟨swap ⟨a, by simp⟩ ⟨b, by simp⟩, Equiv.Perm.ofSubtype_swap_eq _ _⟩

中文:
定义 iwasawaStructure_two
  签名: [对任意 s : 集合 α, DecidablePred fun x => x in s]
  定义体: (ofSubtype : Perm (s : Set α) ->* Perm α).range
  is_comm s := by
    have : IsMulCommutative (Perm s) := isMulCommutative_iff_card_le_two.mpr (by simp)
    infer_instance
  is_conj g s := by
    convert! (conj_smul_range_ofSubtype g s).symm
  is_generator := by
    rw [eq_top_iff]; rw [← Equiv.Perm.closure_isSwap]; rw [Subgroup.closure_le]
    rintro g ⟨a, b, hab, rfl⟩
    apply Subgroup.mem_iSup_of_mem ⟨{a, b}, Finset.card_pair hab⟩
    exact ⟨swap ⟨a, by simp⟩ ⟨b, by simp⟩, Equiv.Perm.ofSubtype_swap_eq _ _⟩

Depends on / 依赖: ofSubtype
-/
def iwasawaStructure_two [forall s : Set α, DecidablePred fun x => x in s] :
    IwasawaStructure (Perm α) (Set.powersetCard α 2) where
  T s := (ofSubtype : Perm (s : Set α) ->* Perm α).range
  is_comm s := by
    have : IsMulCommutative (Perm s) := isMulCommutative_iff_card_le_two.mpr (by simp)
    infer_instance
  is_conj g s := by
    convert! (conj_smul_range_ofSubtype g s).symm
  is_generator := by
    rw [eq_top_iff]; rw [← Equiv.Perm.closure_isSwap]; rw [Subgroup.closure_le]
    rintro g ⟨a, b, hab, rfl⟩
    apply Subgroup.mem_iSup_of_mem ⟨{a, b}, Finset.card_pair hab⟩
    exact ⟨swap ⟨a, by simp⟩ ⟨b, by simp⟩, Equiv.Perm.ofSubtype_swap_eq _ _⟩

/--
theorem `alternatingGroup_le_of_normal` / 定理 `alternatingGroup_le_of_normal`

English:
theorem alternatingGroup_le_of_normal
  proof: by
  rw [← alternatingGroup.commutator_perm_eq hα]
  have : IsPreprimitive (Perm α) (Set.powersetCard α 2) := by
    apply Set.powersetCard.isPreprimitive_perm <;> grind
  classical
  apply iwasawaStructure_two.commutator_le
  exact fixedPoints_ne_univ_of_faithfulSMul (by norm_num) (by grind)

中文:
定理 alternatingGroup_le_of_normal
  证明: by
  rw [← alternatingGroup.commutator_perm_eq hα]
  have : IsPreprimitive (Perm α) (Set.powersetCard α 2) := by
    apply Set.powersetCard.isPreprimitive_perm <;> grind
  classical
  apply iwasawaStructure_two.commutator_le
  exact fixedPoints_ne_univ_of_faithfulSMul (by norm_num) (by grind)

Depends on / 依赖: IsPreprimitive, Set.powersetCard, Set.powersetCard.isPreprimitive_perm, alternatingGroup, alternatingGroup.commutator_perm_eq, classical, commutator_le, commutator_perm_eq, fixedPoints_ne_univ_of_faithfulSMul, isPreprimitive_perm, iwasawaStructure_two, iwasawaStructure_two.commutator_le, powersetCard
-/
theorem alternatingGroup_le_of_normal
    {α : Type*} [DecidableEq α] [Fintype α] (hα : 5 <= Nat.card α)
    {N : Subgroup (Perm α)} [N.Normal] (ntN : Nontrivial N) :
    alternatingGroup α <= N := by
  rw [← alternatingGroup.commutator_perm_eq hα]
  have : IsPreprimitive (Perm α) (Set.powersetCard α 2) := by
    apply Set.powersetCard.isPreprimitive_perm <;> grind
  classical
  apply iwasawaStructure_two.commutator_le
  exact fixedPoints_ne_univ_of_faithfulSMul (by norm_num) (by grind)

end Equiv.Perm

namespace alternatingGroup

variable {α : Type*} [DecidableEq α] [Fintype α]

/--
Definition of `iwasawaStructure_three` / `iwasawaStructure_three` 的定义

English:
definition iwasawaStructure_three
  signature: : IwasawaStructure (alternatingGroup α) (Set.powersetCard α 3) where
  body: (alternatingGroup.ofSubtype s).range
  is_comm s := by
    have : IsMulCommutative (alternatingGroup s) := isMulCommutative_of_card_le_three (by simp)
    infer_instance
  is_conj g s := (conj_smul_range_ofSubtype s g).symm
  is_generator := by
    rw [eq_top_iff]; rw [← closure_isThreeCycles_eq_top]; rw [Subgroup.closure_le]
    intro g hg
    apply Subgroup.mem_iSup_of_mem ⟨(g : Perm α).support, hg.card_support⟩
    rw [mem_range_ofSubtype_iff]

中文:
定义 iwasawaStructure_three
  签名: : IwasawaStructure (alternatingGroup α) (集合.powersetCard α 3) where
  定义体: (alternatingGroup.ofSubtype s).range
  is_comm s := by
    have : IsMulCommutative (alternatingGroup s) := isMulCommutative_of_card_le_three (by simp)
    infer_instance
  is_conj g s := (conj_smul_range_ofSubtype s g).symm
  is_generator := by
    rw [eq_top_iff]; rw [← closure_isThreeCycles_eq_top]; rw [Subgroup.closure_le]
    intro g hg
    apply Subgroup.mem_iSup_of_mem ⟨(g : Perm α).support, hg.card_support⟩
    rw [mem_range_ofSubtype_iff]

Depends on / 依赖: alternatingGroup, alternatingGroup.ofSubtype, ofSubtype
-/
def iwasawaStructure_three : IwasawaStructure (alternatingGroup α) (Set.powersetCard α 3) where
  T s := (alternatingGroup.ofSubtype s).range
  is_comm s := by
    have : IsMulCommutative (alternatingGroup s) := isMulCommutative_of_card_le_three (by simp)
    infer_instance
  is_conj g s := (conj_smul_range_ofSubtype s g).symm
  is_generator := by
    rw [eq_top_iff]; rw [← closure_isThreeCycles_eq_top]; rw [Subgroup.closure_le]
    intro g hg
    apply Subgroup.mem_iSup_of_mem ⟨(g : Perm α).support, hg.card_support⟩
    rw [mem_range_ofSubtype_iff]

/--
theorem `normal_subgroup_eq_bot_or_eq_top_of_card_ne_six` / 定理 `normal_subgroup_eq_bot_or_eq_top_of_card_ne_six`

English:
theorem normal_subgroup_eq_bot_or_eq_top_of_card_ne_six
  proof: by
  rw [or_iff_not_imp_left]; rw [← ne_eq]; rw [← Subgroup.nontrivial_iff_ne_bot]
  intro hN
  have : IsPreprimitive (alternatingGroup α) (Set.powersetCard α 3) := by
    refine Set.powersetCard.isPreprimitive_alternatingGroup (by norm_num) ?_ ?_
    · exact lt_of_lt_of_le (by norm_num) hα
    · simpa using hα'
  rw [eq_top_iff]; rw [← commutator_alternatingGroup_eq_top (by simpa using hα)]
  apply iwasawaStructure_three.commutator_le
  exact fixedPoints_ne_univ_of_faithfulSMul (by norm_num) (by grind)

中文:
定理 normal_subgroup_eq_bot_or_eq_top_of_card_ne_six
  证明: by
  rw [or_iff_not_imp_left]; rw [← ne_eq]; rw [← Subgroup.nontrivial_iff_ne_bot]
  intro hN
  have : IsPreprimitive (alternatingGroup α) (Set.powersetCard α 3) := by
    refine Set.powersetCard.isPreprimitive_alternatingGroup (by norm_num) ?_ ?_
    · exact lt_of_lt_of_le (by norm_num) hα
    · simpa using hα'
  rw [eq_top_iff]; rw [← commutator_alternatingGroup_eq_top (by simpa using hα)]
  apply iwasawaStructure_three.commutator_le
  exact fixedPoints_ne_univ_of_faithfulSMul (by norm_num) (by grind)

Depends on / 依赖: IsPreprimitive, Set.powersetCard, Set.powersetCard.isPreprimitive_alternatingGroup, Subgroup, Subgroup.nontrivial_iff_ne_bot, alternatingGroup, commutator_alternatingGroup_eq_top, commutator_le, eq_top_iff, fixedPoints_ne_univ_of_faithfulSMul, hab.to_reflTransGen, isPreprimitive_alternatingGroup, iwasawaStructure_three, iwasawaStructure_three.commutator_le, lt_of_lt_of_le, ne_eq, nontrivial_iff_ne_bot, or_iff_not_imp_left, powersetCard, single
-/
theorem normal_subgroup_eq_bot_or_eq_top_of_card_ne_six
    (hα : 5 <= Nat.card α) (hα' : Nat.card α != 6)
    {N : Subgroup (alternatingGroup α)} [N.Normal] :
    N = ⊥ ∨ N = ⊤ := by
  rw [or_iff_not_imp_left]; rw [← ne_eq]; rw [← Subgroup.nontrivial_iff_ne_bot]
  intro hN
  have : IsPreprimitive (alternatingGroup α) (Set.powersetCard α 3) := by
    refine Set.powersetCard.isPreprimitive_alternatingGroup (by norm_num) ?_ ?_
    · exact lt_of_lt_of_le (by norm_num) hα
    · simpa using hα'
  rw [eq_top_iff]; rw [← commutator_alternatingGroup_eq_top (by simpa using hα)]
  apply iwasawaStructure_three.commutator_le
  exact fixedPoints_ne_univ_of_faithfulSMul (by norm_num) (by grind)

/--
theorem `mem_map_kleinFour_ofSubtype` / 定理 `mem_map_kleinFour_ofSubtype`

English:
theorem mem_map_kleinFour_ofSubtype
  given: {s : Finset α} (hs : s.card = 4) (k : alternatingGroup α)
  proof: by
  have hs : Nat.card s = 4 := by simpa
  by_cases hk : (k : Perm α).support subseteq s
  · obtain ⟨σ, rfl⟩ := (mem_range_ofSubtype_iff s k).mpr hk
    simp_rw [and_iff_right hk, Subgroup.mem_map, ofSubtype_inj, existsAndEq, and_true,
      ← SetLike.mem_coe, coe_kleinFour_of_card_eq_four hs]
    simp [cycleType_ofSubtype, coe_ofSubtype, map_eq_one_iff _ Perm.ofSubtype_injective]
  · simp_rw [hk, false_and, iff_false]
    contrapose! hk
    exact (mem_range_ofSubtype_iff s k).mp (Subgroup.map_le_range _ _ hk)

中文:
定理 mem_map_kleinFour_ofSubtype
  条件: {s : 有限集 α} (hs : s.card = 4) (k : alternatingGroup α)
  证明: by
  have hs : Nat.card s = 4 := by simpa
  by_cases hk : (k : Perm α).support subseteq s
  · obtain ⟨σ, rfl⟩ := (mem_range_ofSubtype_iff s k).mpr hk
    simp_rw [and_iff_right hk, Subgroup.mem_map, ofSubtype_inj, existsAndEq, and_true,
      ← SetLike.mem_coe, coe_kleinFour_of_card_eq_four hs]
    simp [cycleType_ofSubtype, coe_ofSubtype, map_eq_one_iff _ Perm.ofSubtype_injective]
  · simp_rw [hk, false_and, iff_false]
    contrapose! hk
    exact (mem_range_ofSubtype_iff s k).mp (Subgroup.map_le_range _ _ hk)

Depends on / 依赖: Nat.card, Perm.ofSubtype_injective, SetLike, SetLike.mem_coe, Subgroup, Subgroup.map_le_range, Subgroup.mem_map, and_iff_right, and_true, coe_kleinFour_of_card_eq_four, coe_ofSubtype, contrapose, cycleType_ofSubtype, existsAndEq, false_and, hdb.tail, iff_false, map_eq_one_iff, map_le_range, mem_coe
-/
theorem mem_map_kleinFour_ofSubtype {s : Finset α} (hs : s.card = 4) (k : alternatingGroup α) :
    k in (kleinFour s).map (ofSubtype s) ↔
      (k : Perm α).support subseteq s ∧ ((k : Perm α) = 1 ∨ (k : Perm α).cycleType = {2, 2}) := by
  have hs : Nat.card s = 4 := by simpa
  by_cases hk : (k : Perm α).support subseteq s
  · obtain ⟨σ, rfl⟩ := (mem_range_ofSubtype_iff s k).mpr hk
    simp_rw [and_iff_right hk, Subgroup.mem_map, ofSubtype_inj, existsAndEq, and_true,
      ← SetLike.mem_coe, coe_kleinFour_of_card_eq_four hs]
    simp [cycleType_ofSubtype, coe_ofSubtype, map_eq_one_iff _ Perm.ofSubtype_injective]
  · simp_rw [hk, false_and, iff_false]
    contrapose! hk
    exact (mem_range_ofSubtype_iff s k).mp (Subgroup.map_le_range _ _ hk)

/--
theorem `map_kleinFour_conj` / 定理 `map_kleinFour_conj`

English:
theorem map_kleinFour_conj
  given: (s : Finset α) (hs : s.card = 4) (g : alternatingGroup α)
  proof: by
  rcases g with ⟨g, hg⟩
  ext ⟨k, hk⟩
  simp_rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, mem_map_kleinFour_ofSubtype hs,
    Subgroup.mk_smul, MulAut.smul_def, MulAut.inv_apply, MulAut.conj_symm_apply, Subgroup.coe_mul,
    Subgroup.coe_inv, ← ConjAct.toConjAct_inv_smul, Equiv.Perm.support_toConjAct_eq_smul_support,
    mem_map_kleinFour_ofSubtype (s := g • s) (by simpa), Finset.subset_smul_finset_iff,
    ConjAct.toConjAct_smul, cycleType_conj, mul_inv_eq_one, mul_eq_left]

中文:
定理 map_kleinFour_conj
  条件: (s : 有限集 α) (hs : s.card = 4) (g : alternatingGroup α)
  证明: by
  rcases g with ⟨g, hg⟩
  ext ⟨k, hk⟩
  simp_rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, mem_map_kleinFour_ofSubtype hs,
    Subgroup.mk_smul, MulAut.smul_def, MulAut.inv_apply, MulAut.conj_symm_apply, Subgroup.coe_mul,
    Subgroup.coe_inv, ← ConjAct.toConjAct_inv_smul, Equiv.Perm.support_toConjAct_eq_smul_support,
    mem_map_kleinFour_ofSubtype (s := g • s) (by simpa), Finset.subset_smul_finset_iff,
    ConjAct.toConjAct_smul, cycleType_conj, mul_inv_eq_one, mul_eq_left]

Depends on / 依赖: ConjAct, ConjAct.toConjAct_inv_smul, ConjAct.toConjAct_smul, Equiv.Perm.support_toConjAct_eq_smul_support, Finset, Finset.subset_smul_finset_iff, MulAut, MulAut.conj_symm_apply, MulAut.inv_apply, MulAut.smul_def, Subgroup, Subgroup.coe_inv, Subgroup.coe_mul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mk_smul, coe_inv, coe_mul, conj_symm_apply, cycleType_conj, inv_apply
-/
theorem map_kleinFour_conj (s : Finset α) (hs : s.card = 4) (g : alternatingGroup α) :
    (kleinFour _).map (ofSubtype (g • s)) = MulAut.conj g • ((kleinFour s).map (ofSubtype s)) := by
  rcases g with ⟨g, hg⟩
  ext ⟨k, hk⟩
  simp_rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, mem_map_kleinFour_ofSubtype hs,
    Subgroup.mk_smul, MulAut.smul_def, MulAut.inv_apply, MulAut.conj_symm_apply, Subgroup.coe_mul,
    Subgroup.coe_inv, ← ConjAct.toConjAct_inv_smul, Equiv.Perm.support_toConjAct_eq_smul_support,
    mem_map_kleinFour_ofSubtype (s := g • s) (by simpa), Finset.subset_smul_finset_iff,
    ConjAct.toConjAct_smul, cycleType_conj, mul_inv_eq_one, mul_eq_left]

/--
Definition of `iwasawaStructure_four` / `iwasawaStructure_four` 的定义

English:
definition iwasawaStructure_four
  signature: (h5 : 5 <= Nat.card α)
  body: (kleinFour s).map (ofSubtype s)
  is_comm s := by
    have : IsMulCommutative (kleinFour s) :=
      (kleinFour_isKleinFour (by simp)).isMulCommutative
    infer_instance
  is_conj g s := map_kleinFour_conj s.val s.prop g
  is_generator := by
    rw [eq_top_iff]; rw [← closure_cycleType_eq_two_two_eq_top h5]; rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_ofPred_eq] at hg
    apply Subgroup.mem_iSup_of_mem ⟨(g : Perm α).support, by simp [← sum_cycleType, hg]⟩
    rw [mem_map_kleinFour_ofSubtype] <;> simp [hg, ← sum_cycleType]

中文:
定义 iwasawaStructure_four
  签名: (h5 : 5 <= 自然数.card α)
  定义体: (kleinFour s).map (ofSubtype s)
  is_comm s := by
    have : IsMulCommutative (kleinFour s) :=
      (kleinFour_isKleinFour (by simp)).isMulCommutative
    infer_instance
  is_conj g s := map_kleinFour_conj s.val s.prop g
  is_generator := by
    rw [eq_top_iff]; rw [← closure_cycleType_eq_two_two_eq_top h5]; rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_ofPred_eq] at hg
    apply Subgroup.mem_iSup_of_mem ⟨(g : Perm α).support, by simp [← sum_cycleType, hg]⟩
    rw [mem_map_kleinFour_ofSubtype] <;> simp [hg, ← sum_cycleType]

Depends on / 依赖: kleinFour, ofSubtype
-/
def iwasawaStructure_four (h5 : 5 <= Nat.card α) :
    IwasawaStructure (alternatingGroup α) (Set.powersetCard α 4) where
  T s := (kleinFour s).map (ofSubtype s)
  is_comm s := by
    have : IsMulCommutative (kleinFour s) :=
      (kleinFour_isKleinFour (by simp)).isMulCommutative
    infer_instance
  is_conj g s := map_kleinFour_conj s.val s.prop g
  is_generator := by
    rw [eq_top_iff]; rw [← closure_cycleType_eq_two_two_eq_top h5]; rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_ofPred_eq] at hg
    apply Subgroup.mem_iSup_of_mem ⟨(g : Perm α).support, by simp [← sum_cycleType, hg]⟩
    rw [mem_map_kleinFour_ofSubtype] <;> simp [hg, ← sum_cycleType]

/--
theorem `normal_subgroup_eq_bot_or_eq_top_of_card_ne_eight` / 定理 `normal_subgroup_eq_bot_or_eq_top_of_card_ne_eight`

English:
theorem normal_subgroup_eq_bot_or_eq_top_of_card_ne_eight
  proof: by
  rw [or_iff_not_imp_left]; rw [← ne_eq]; rw [← Subgroup.nontrivial_iff_ne_bot]
  intro hN
  have : IsPreprimitive (alternatingGroup α) (Set.powersetCard α 4) := by
    apply Set.powersetCard.isPreprimitive_alternatingGroup (by norm_num) <;> grind
  rw [eq_top_iff]; rw [← commutator_alternatingGroup_eq_top hα]
  apply (iwasawaStructure_four hα).commutator_le
  exact fixedPoints_ne_univ_of_faithfulSMul (by norm_num) (by grind)

中文:
定理 normal_subgroup_eq_bot_or_eq_top_of_card_ne_eight
  证明: by
  rw [or_iff_not_imp_left]; rw [← ne_eq]; rw [← Subgroup.nontrivial_iff_ne_bot]
  intro hN
  have : IsPreprimitive (alternatingGroup α) (Set.powersetCard α 4) := by
    apply Set.powersetCard.isPreprimitive_alternatingGroup (by norm_num) <;> grind
  rw [eq_top_iff]; rw [← commutator_alternatingGroup_eq_top hα]
  apply (iwasawaStructure_four hα).commutator_le
  exact fixedPoints_ne_univ_of_faithfulSMul (by norm_num) (by grind)

Depends on / 依赖: IsPreprimitive, Set.powersetCard, Set.powersetCard.isPreprimitive_alternatingGroup, Subgroup, Subgroup.nontrivial_iff_ne_bot, alternatingGroup, commutator_alternatingGroup_eq_top, commutator_le, eq_top_iff, fixedPoints_ne_univ_of_faithfulSMul, isPreprimitive_alternatingGroup, iwasawaStructure_four, ne_eq, nontrivial_iff_ne_bot, or_iff_not_imp_left, powersetCard
-/
theorem normal_subgroup_eq_bot_or_eq_top_of_card_ne_eight
    (hα : 5 <= Nat.card α) (hα' : Nat.card α != 8)
    {N : Subgroup (alternatingGroup α)} [N.Normal] :
    N = ⊥ ∨ N = ⊤ := by
  rw [or_iff_not_imp_left]; rw [← ne_eq]; rw [← Subgroup.nontrivial_iff_ne_bot]
  intro hN
  have : IsPreprimitive (alternatingGroup α) (Set.powersetCard α 4) := by
    apply Set.powersetCard.isPreprimitive_alternatingGroup (by norm_num) <;> grind
  rw [eq_top_iff]; rw [← commutator_alternatingGroup_eq_top hα]
  apply (iwasawaStructure_four hα).commutator_le
  exact fixedPoints_ne_univ_of_faithfulSMul (by norm_num) (by grind)

/--
theorem `normal_subgroup_eq_bot_or_eq_top` / 定理 `normal_subgroup_eq_bot_or_eq_top`

English:
theorem normal_subgroup_eq_bot_or_eq_top
  proof: by
  by_cases hα' : Nat.card α = 6
  · apply normal_subgroup_eq_bot_or_eq_top_of_card_ne_eight hα (by grind)
  · apply normal_subgroup_eq_bot_or_eq_top_of_card_ne_six hα hα'

中文:
定理 normal_subgroup_eq_bot_or_eq_top
  证明: by
  by_cases hα' : Nat.card α = 6
  · apply normal_subgroup_eq_bot_or_eq_top_of_card_ne_eight hα (by grind)
  · apply normal_subgroup_eq_bot_or_eq_top_of_card_ne_six hα hα'

Depends on / 依赖: Nat.card, normal_subgroup_eq_bot_or_eq_top_of_card_ne_eight, normal_subgroup_eq_bot_or_eq_top_of_card_ne_six
-/
theorem normal_subgroup_eq_bot_or_eq_top
    (hα : 5 <= Nat.card α)
    {N : Subgroup (alternatingGroup α)} [N.Normal] :
    N = ⊥ ∨ N = ⊤ := by
  by_cases hα' : Nat.card α = 6
  · apply normal_subgroup_eq_bot_or_eq_top_of_card_ne_eight hα (by grind)
  · apply normal_subgroup_eq_bot_or_eq_top_of_card_ne_six hα hα'

/--
theorem `isSimpleGroup` / 定理 `isSimpleGroup`

English:
theorem isSimpleGroup
  given: (hα : 5 <= Nat.card α)
  proof: by
    rw [← _root_.nontrivial_iff]
    refine nontrivial_of_three_le_card ?_
    simpa using le_trans (by norm_num) hα
  eq_bot_or_eq_top_of_normal H _ := normal_subgroup_eq_bot_or_eq_top hα

@[deprecated "Use `alternatingGroup.isSimpleGroup` instead." (since := "2026-04-28")]

中文:
定理 isSimpleGroup
  条件: (hα : 5 <= 自然数.card α)
  证明: by
    rw [← _root_.nontrivial_iff]
    refine nontrivial_of_three_le_card ?_
    simpa using le_trans (by norm_num) hα
  eq_bot_or_eq_top_of_normal H _ := normal_subgroup_eq_bot_or_eq_top hα

@[deprecated "Use `alternatingGroup.isSimpleGroup` instead." (since := "2026-04-28")]

Depends on / 依赖: _root_, _root_.nontrivial_iff, eq_bot_or_eq_top_of_normal, le_trans, nontrivial_iff, nontrivial_of_three_le_card, normal_subgroup_eq_bot_or_eq_top
-/
theorem isSimpleGroup (hα : 5 <= Nat.card α) :
    IsSimpleGroup (alternatingGroup α) where
  exists_pair_ne := by
    rw [← _root_.nontrivial_iff]
    refine nontrivial_of_three_le_card ?_
    simpa using le_trans (by norm_num) hα
  eq_bot_or_eq_top_of_normal H _ := normal_subgroup_eq_bot_or_eq_top hα

@[deprecated "Use `alternatingGroup.isSimpleGroup` instead." (since := "2026-04-28")]
/--
theorem `_root_.Equiv.Perm.IsThreeCycle.alternating_normalClosure` / 定理 `_root_.Equiv.Perm.IsThreeCycle.alternating_normalClosure`

English:
theorem _root_.Equiv.Perm.IsThreeCycle.alternating_normalClosure
  proof: by
  have : IsSimpleGroup (alternatingGroup α) := isSimpleGroup h5
  apply normalClosure_normal.eq_bot_or_eq_top.resolve_left
  simp [hf.ne_one]

@[deprecated "Use `alternatingGroup.isSimpleGroup` instead." (since := "2026-04-28")]

中文:
定理 _root_.等价.置换.IsThreeCycle.alternating_normalClosure
  证明: by
  have : IsSimpleGroup (alternatingGroup α) := isSimpleGroup h5
  apply normalClosure_normal.eq_bot_or_eq_top.resolve_left
  simp [hf.ne_one]

@[deprecated "Use `alternatingGroup.isSimpleGroup` instead." (since := "2026-04-28")]

Depends on / 依赖: IsSimpleGroup, alternatingGroup, eq_bot_or_eq_top, hf.ne_one, isSimpleGroup, ne_one, normalClosure_normal, normalClosure_normal.eq_bot_or_eq_top.resolve_left, resolve_left
-/
theorem _root_.Equiv.Perm.IsThreeCycle.alternating_normalClosure
    (h5 : 5 <= Nat.card α) {f : Perm α} (hf : IsThreeCycle f) :
    normalClosure ({⟨f, hf.mem_alternatingGroup⟩} : Set (alternatingGroup α)) = ⊤ := by
  have : IsSimpleGroup (alternatingGroup α) := isSimpleGroup h5
  apply normalClosure_normal.eq_bot_or_eq_top.resolve_left
  simp [hf.ne_one]

@[deprecated "Use `alternatingGroup.isSimpleGroup` instead." (since := "2026-04-28")]
/--
theorem `normalClosure_finRotate_five` / 定理 `normalClosure_finRotate_five`

English:
theorem normalClosure_finRotate_five
  statement: normalClosure ({⟨finRotate 5,
  proof: by
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := isSimpleGroup (by simp)
  apply normalClosure_normal.eq_bot_or_eq_top.resolve_left
  simp +decide

@[deprecated "Use `alternatingGroup.isSimpleGroup` instead." (since := "2026-04-28")]

中文:
定理 normalClosure_finRotate_five
  结论: normalClosure ({⟨finRotate 5,
  证明: by
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := isSimpleGroup (by simp)
  apply normalClosure_normal.eq_bot_or_eq_top.resolve_left
  simp +decide

@[deprecated "Use `alternatingGroup.isSimpleGroup` instead." (since := "2026-04-28")]

Depends on / 依赖: IsSimpleGroup, alternatingGroup, eq_bot_or_eq_top, isSimpleGroup, normalClosure_normal, normalClosure_normal.eq_bot_or_eq_top.resolve_left, resolve_left
-/
theorem normalClosure_finRotate_five : normalClosure ({⟨finRotate 5,
    finRotate_bit1_mem_alternatingGroup (n := 2)⟩} : Set (alternatingGroup (Fin 5))) = ⊤ := by
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := isSimpleGroup (by simp)
  apply normalClosure_normal.eq_bot_or_eq_top.resolve_left
  simp +decide

@[deprecated "Use `alternatingGroup.isSimpleGroup` instead." (since := "2026-04-28")]
/--
theorem `normalClosure_swap_mul_swap_five` / 定理 `normalClosure_swap_mul_swap_five`

English:
theorem normalClosure_swap_mul_swap_five
  statement: normalClosure ({⟨swap 0 4 * swap 1 3,
  proof: by
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := isSimpleGroup (by simp)
  apply normalClosure_normal.eq_bot_or_eq_top.resolve_left
  simp +decide

@[deprecated "Use `alternatingGroup.isSimpleGroup` instead." (since := "2026-04-28")]

中文:
定理 normalClosure_swap_mul_swap_five
  结论: normalClosure ({⟨swap 0 4 * swap 1 3,
  证明: by
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := isSimpleGroup (by simp)
  apply normalClosure_normal.eq_bot_or_eq_top.resolve_left
  simp +decide

@[deprecated "Use `alternatingGroup.isSimpleGroup` instead." (since := "2026-04-28")]

Depends on / 依赖: IsSimpleGroup, alternatingGroup, eq_bot_or_eq_top, isSimpleGroup, normalClosure_normal, normalClosure_normal.eq_bot_or_eq_top.resolve_left, resolve_left
-/
theorem normalClosure_swap_mul_swap_five : normalClosure ({⟨swap 0 4 * swap 1 3,
    mem_alternatingGroup.2 (by decide)⟩} : Set (alternatingGroup (Fin 5))) = ⊤ := by
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := isSimpleGroup (by simp)
  apply normalClosure_normal.eq_bot_or_eq_top.resolve_left
  simp +decide

@[deprecated "Use `alternatingGroup.isSimpleGroup` instead." (since := "2026-04-28")]
/--
Instance `isSimpleGroup_five` / 实例 `isSimpleGroup_five`

English:
instance isSimpleGroup_five
  signature: : IsSimpleGroup (alternatingGroup (Fin 5))
  body: isSimpleGroup (by simp)

中文:
实例 isSimpleGroup_five
  签名: : 是单群 (alternatingGroup (有限集 5))
  定义体: isSimpleGroup (by simp)

Depends on / 依赖: isSimpleGroup
-/
instance isSimpleGroup_five : IsSimpleGroup (alternatingGroup (Fin 5)) :=
  isSimpleGroup (by simp)

end alternatingGroup
