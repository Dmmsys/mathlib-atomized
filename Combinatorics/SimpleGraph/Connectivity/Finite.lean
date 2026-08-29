/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Nat
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
public import Mathlib.Data.Set.Card

/-!
# Counting walks of a given length

## Main definitions
- `walkLengthTwoEquivCommonNeighbors`: bijective correspondence between walks of length two
from `u` to `v` and common neighbours of `u` and `v`. Note that `u` and `v` may be the same.
- `finsetWalkLength`: the `Finset` of length-`n` walks from `u` to `v`.
This is used to give `{p : G.walk u v | p.length = n}` a `Fintype` instance, and it
can also be useful as a recursive description of this set when `V` is finite.

TODO: should this be extended further?
-/

public section

assert_not_exists Field

open Finset Function

universe u v w

namespace SimpleGraph

variable {V : Type u} (G : SimpleGraph V)

/--
theorem `ConnectedComponent.card_le_card_of_le` / 定理 `ConnectedComponent.card_le_card_of_le`

English:
theorem ConnectedComponent.card_le_card_of_le
  given: [Finite V] {G G' : SimpleGraph V} (h : G <= G')
  proof: Nat.card_le_card_of_surjective _ ConnectedComponent.surjective_map_ofLE h

中文:
定理 ConnectedComponent.card_le_card_of_le
  条件: [有限 V] {G G' : 简单图 V} (h : G <= G')
  证明: Nat.card_le_card_of_surjective _ ConnectedComponent.surjective_map_ofLE h

Depends on / 依赖: ConnectedComponent, ConnectedComponent.surjective_map_ofLE, Nat.card_le_card_of_surjective, card_le_card_of_surjective, surjective_map_ofLE
-/
theorem ConnectedComponent.card_le_card_of_le [Finite V] {G G' : SimpleGraph V} (h : G <= G') :
    Nat.card G'.ConnectedComponent <= Nat.card G.ConnectedComponent :=
Nat.card_le_card_of_surjective _ ConnectedComponent.surjective_map_ofLE h

section Fintype

variable [DecidableEq V] [Fintype V] [DecidableRel G.Adj]

/--
theorem `reachable_iff_exists_finsetWalkLength_nonempty` / 定理 `reachable_iff_exists_finsetWalkLength_nonempty`

English:
theorem reachable_iff_exists_finsetWalkLength_nonempty
  given: (u v : V)
  proof: by
  constructor
  · intro r
    refine r.elim_path fun p => ?_
    refine ⟨⟨_, p.isPath.length_lt⟩, p, ?_⟩
    simp [mem_finsetWalkLength_iff]
  · rintro ⟨_, p, _⟩
    exact ⟨p⟩

中文:
定理 reachable_iff_存在_finsetWalkLength_nonempty
  条件: (u v : V)
  证明: by
  constructor
  · intro r
    refine r.elim_path fun p => ?_
    refine ⟨⟨_, p.isPath.length_lt⟩, p, ?_⟩
    simp [mem_finsetWalkLength_iff]
  · rintro ⟨_, p, _⟩
    exact ⟨p⟩

Depends on / 依赖: elim_path, isPath, length_lt, mem_finsetWalkLength_iff, p.isPath.length_lt, r.elim_path
-/
theorem reachable_iff_exists_finsetWalkLength_nonempty (u v : V) :
    G.Reachable u v ↔ exists n : Fin (Fintype.card V), (G.finsetWalkLength n u v).Nonempty := by
  constructor
  · intro r
    refine r.elim_path fun p => ?_
    refine ⟨⟨_, p.isPath.length_lt⟩, p, ?_⟩
    simp [mem_finsetWalkLength_iff]
  · rintro ⟨_, p, _⟩
    exact ⟨p⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DecidableRel G.Reachable
  body: fun u v =>
  decidable_of_iff' _ (reachable_iff_exists_finsetWalkLength_nonempty G u v)

中文:
实例 :
  签名: DecidableRel G.Reachable
  定义体: fun u v =>
  decidable_of_iff' _ (reachable_iff_exists_finsetWalkLength_nonempty G u v)
-/
instance : DecidableRel G.Reachable := fun u v =>
  decidable_of_iff' _ (reachable_iff_exists_finsetWalkLength_nonempty G u v)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Fintype G.ConnectedComponent
  body: fast_instance% @Quotient.fintype _ _ G.reachableSetoid (inferInstance : DecidableRel G.Reachable)

中文:
实例 :
  签名: 有限类型 G.ConnectedComponent
  定义体: fast_instance% @Quotient.fintype _ _ G.reachableSetoid (inferInstance : DecidableRel G.Reachable)

Depends on / 依赖: DecidableRel, G.Reachable, G.reachableSetoid, Quotient, Quotient.fintype, Reachable, fast_instance, fintype, reachableSetoid
-/
instance : Fintype G.ConnectedComponent :=
  fast_instance% @Quotient.fintype _ _ G.reachableSetoid (inferInstance : DecidableRel G.Reachable)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Decidable G.Preconnected
  body: inferInstanceAs Decidable (forall u v, G.Reachable u v)

中文:
实例 :
  签名: 可判定 G.预连通
  定义体: inferInstanceAs Decidable (forall u v, G.Reachable u v)

Depends on / 依赖: Decidable, G.Reachable, Reachable
-/
instance : Decidable G.Preconnected :=
inferInstanceAs Decidable (forall u v, G.Reachable u v)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Decidable G.Connected
  body: decidable_of_iff (G.Preconnected ∧ (Finset.univ : Finset V).Nonempty) by
    rw [connected_iff]; rw [← Finset.univ_nonempty_iff]

中文:
实例 :
  签名: 可判定 G.连通
  定义体: decidable_of_iff (G.Preconnected ∧ (Finset.univ : Finset V).Nonempty) by
    rw [connected_iff]; rw [← Finset.univ_nonempty_iff]

Depends on / 依赖: Finset, Finset.univ, Finset.univ_nonempty_iff, G.Preconnected, Nonempty, Preconnected, connected_iff, decidable_of_iff, univ_nonempty_iff
-/
instance : Decidable G.Connected :=
decidable_of_iff (G.Preconnected ∧ (Finset.univ : Finset V).Nonempty) by
    rw [connected_iff]; rw [← Finset.univ_nonempty_iff]

/--
Instance `instDecidableMemSupp` / 实例 `instDecidableMemSupp`

English:
instance instDecidableMemSupp
  signature: (c : G.ConnectedComponent) (v : V)
  body: c.recOn (fun w => decidable_of_iff (G.Reachable v w) <| by simp)
    (fun _ _ _ _ => Subsingleton.elim _ _)

中文:
实例 instDecidableMemSupp
  签名: (c : G.ConnectedComponent) (v : V)
  定义体: c.recOn (fun w => decidable_of_iff (G.Reachable v w) <| by simp)
    (fun _ _ _ _ => Subsingleton.elim _ _)

Depends on / 依赖: G.Reachable, Reachable, Subsingleton, Subsingleton.elim, c.recOn, decidable_of_iff
-/
instance instDecidableMemSupp (c : G.ConnectedComponent) (v : V) : Decidable (v in c.supp) :=
  c.recOn (fun w => decidable_of_iff (G.Reachable v w) <| by simp)
    (fun _ _ _ _ => Subsingleton.elim _ _)

set_option backward.isDefEq.respectTransparency.types false in
variable {G} in
/--
lemma `disjiUnion_supp_toFinset_eq_supp_toFinset` / 引理 `disjiUnion_supp_toFinset_eq_supp_toFinset`

English:
lemma disjiUnion_supp_toFinset_eq_supp_toFinset
  statement: {G' : SimpleGraph V} (h : G <= G')
  proof: Finset.coe_injective by simpa using ConnectedComponent.biUnion_supp_eq_supp h _

中文:
引理 disjiUnion_supp_toFinset_eq_supp_toFinset
  结论: {G' : 简单图 V} (h : G <= G')
  证明: Finset.coe_injective by simpa using ConnectedComponent.biUnion_supp_eq_supp h _

Depends on / 依赖: ConnectedComponent, ConnectedComponent.biUnion_supp_eq_supp, Finset, Finset.coe_injective, biUnion_supp_eq_supp, coe_injective
-/
lemma disjiUnion_supp_toFinset_eq_supp_toFinset {G' : SimpleGraph V} (h : G <= G')
    (c' : ConnectedComponent G') [Fintype c'.supp]
    [DecidablePred fun c : G.ConnectedComponent => c.supp subseteq c'.supp] :
    .disjiUnion {c : ConnectedComponent G | c.supp subseteq c'.supp} (fun c => c.supp.toFinset)
      (fun x _ y _ hxy => by simpa using pairwise_disjoint_supp_connectedComponent _ hxy) =
      c'.supp.toFinset :=
Finset.coe_injective by simpa using ConnectedComponent.biUnion_supp_eq_supp h _

end Fintype

/--
Definition of `oddComponents` / `oddComponents` 的定义

English:
abbreviation oddComponents
  signature: : Set G.ConnectedComponent
  body: {c : G.ConnectedComponent | Odd c.supp.ncard}

中文:
缩写 oddComponents
  签名: : 集合 G.ConnectedComponent
  定义体: {c : G.ConnectedComponent | Odd c.supp.ncard}

Depends on / 依赖: ConnectedComponent, G.ConnectedComponent, c.supp.ncard
-/
abbrev oddComponents : Set G.ConnectedComponent := {c : G.ConnectedComponent | Odd c.supp.ncard}

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `ConnectedComponent.odd_oddComponents_ncard_subset_supp` / 引理 `ConnectedComponent.odd_oddComponents_ncard_subset_supp`

English:
lemma ConnectedComponent.odd_oddComponents_ncard_subset_supp
  statement: [Finite V] {G'}
  proof: by
  simp_rw [← Nat.card_coe_set_eq]
  classical
  cases nonempty_fintype V
  rw [Nat.card_eq_card_toFinset c'.supp]; rw [← disjiUnion_supp_toFinset_eq_supp_toFinset h]
  simp only [Finset.card_disjiUnion, Set.toFinset_card, Fintype.card_ofFinset]
  rw [Finset.odd_sum_iff_odd_card_odd]; rw [Nat.card_eq_fintype_card]; rw [Fintype.card_ofFinset]
  congr! 2
  ext c
  simp_rw [Set.toFinset_ofPred, mem_filter, ← Set.ncard_coe_finset, coe_filter,
    mem_supp_iff, mem_univ, true_and, supp, and_comm]

中文:
引理 ConnectedComponent.odd_oddComponents_ncard_subset_supp
  结论: [有限 V] {G'}
  证明: by
  simp_rw [← Nat.card_coe_set_eq]
  classical
  cases nonempty_fintype V
  rw [Nat.card_eq_card_toFinset c'.supp]; rw [← disjiUnion_supp_toFinset_eq_supp_toFinset h]
  simp only [Finset.card_disjiUnion, Set.toFinset_card, Fintype.card_ofFinset]
  rw [Finset.odd_sum_iff_odd_card_odd]; rw [Nat.card_eq_fintype_card]; rw [Fintype.card_ofFinset]
  congr! 2
  ext c
  simp_rw [Set.toFinset_ofPred, mem_filter, ← Set.ncard_coe_finset, coe_filter,
    mem_supp_iff, mem_univ, true_and, supp, and_comm]

Depends on / 依赖: Finset, Finset.card_disjiUnion, Finset.odd_sum_iff_odd_card_odd, Fintype, Fintype.card_ofFinset, Nat.card_coe_set_eq, Nat.card_eq_card_toFinset, Nat.card_eq_fintype_card, Set.ncard_coe_finset, Set.toFinset_card, Set.toFinset_ofPred, and_comm, card_coe_set_eq, card_disjiUnion, card_eq_card_toFinset, card_eq_fintype_card, card_ofFinset, classical, coe_filter, disjiUnion_supp_toFinset_eq_supp_toFinset
-/
lemma ConnectedComponent.odd_oddComponents_ncard_subset_supp [Finite V] {G'}
    (h : G <= G') (c' : ConnectedComponent G') :
    Odd {c in G.oddComponents | c.supp subseteq c'.supp}.ncard ↔ Odd c'.supp.ncard := by
  simp_rw [← Nat.card_coe_set_eq]
  classical
  cases nonempty_fintype V
  rw [Nat.card_eq_card_toFinset c'.supp]; rw [← disjiUnion_supp_toFinset_eq_supp_toFinset h]
  simp only [Finset.card_disjiUnion, Set.toFinset_card, Fintype.card_ofFinset]
  rw [Finset.odd_sum_iff_odd_card_odd]; rw [Nat.card_eq_fintype_card]; rw [Fintype.card_ofFinset]
  congr! 2
  ext c
  simp_rw [Set.toFinset_ofPred, mem_filter, ← Set.ncard_coe_finset, coe_filter,
    mem_supp_iff, mem_univ, true_and, supp, and_comm]

/--
lemma `odd_ncard_oddComponents` / 引理 `odd_ncard_oddComponents`

English:
lemma odd_ncard_oddComponents
  given: [Finite V]
  statement: Odd G.oddComponents.ncard ↔ Odd (Nat.card V)
  proof: by
  classical
  cases nonempty_fintype V
  rw [Nat.card_eq_fintype_card]
  simp only [← (set_fintype_card_eq_univ_iff _).mpr G.iUnion_connectedComponentSupp,
    ← Set.toFinset_card, Set.toFinset_iUnion ConnectedComponent.supp]
  rw [Finset.card_biUnion
    (fun x _ y _ hxy => Set.disjoint_toFinset.mpr (pairwise_disjoint_supp_connectedComponent _ hxy))]
  simp_rw [← Set.ncard_eq_toFinset_card', ← Finset.coe_filter_univ, Set.ncard_coe_finset]
  exact (Finset.odd_sum_iff_odd_card_odd (fun x : G.ConnectedComponent => x.supp.ncard)).symm

中文:
引理 odd_ncard_oddComponents
  条件: [有限 V]
  结论: Odd G.oddComponents.ncard ↔ Odd (自然数.card V)
  证明: by
  classical
  cases nonempty_fintype V
  rw [Nat.card_eq_fintype_card]
  simp only [← (set_fintype_card_eq_univ_iff _).mpr G.iUnion_connectedComponentSupp,
    ← Set.toFinset_card, Set.toFinset_iUnion ConnectedComponent.supp]
  rw [Finset.card_biUnion
    (fun x _ y _ hxy => Set.disjoint_toFinset.mpr (pairwise_disjoint_supp_connectedComponent _ hxy))]
  simp_rw [← Set.ncard_eq_toFinset_card', ← Finset.coe_filter_univ, Set.ncard_coe_finset]
  exact (Finset.odd_sum_iff_odd_card_odd (fun x : G.ConnectedComponent => x.supp.ncard)).symm

Depends on / 依赖: ConnectedComponent, ConnectedComponent.supp, Finset, Finset.card_biUnion, Finset.coe_filter_univ, Finset.odd_sum_iff_odd_card_odd, G.ConnectedComponent, G.iUnion_connectedComponentSupp, Nat.card_eq_fintype_card, Set.disjoint_toFinset.mpr, Set.ncard_coe_finset, Set.ncard_eq_toFinset_card, Set.toFinset_card, Set.toFinset_iUnion, card_biUnion, card_eq_fintype_card, classical, coe_filter_univ, disjoint_toFinset, iUnion_connectedComponentSupp
-/
lemma odd_ncard_oddComponents [Finite V] : Odd G.oddComponents.ncard ↔ Odd (Nat.card V) := by
  classical
  cases nonempty_fintype V
  rw [Nat.card_eq_fintype_card]
  simp only [← (set_fintype_card_eq_univ_iff _).mpr G.iUnion_connectedComponentSupp,
    ← Set.toFinset_card, Set.toFinset_iUnion ConnectedComponent.supp]
  rw [Finset.card_biUnion
    (fun x _ y _ hxy => Set.disjoint_toFinset.mpr (pairwise_disjoint_supp_connectedComponent _ hxy))]
  simp_rw [← Set.ncard_eq_toFinset_card', ← Finset.coe_filter_univ, Set.ncard_coe_finset]
  exact (Finset.odd_sum_iff_odd_card_odd (fun x : G.ConnectedComponent => x.supp.ncard)).symm

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `ncard_oddComponents_mono` / 引理 `ncard_oddComponents_mono`

English:
lemma ncard_oddComponents_mono
  given: [Finite V] {G' : SimpleGraph V} (h : G <= G')
  proof: by
  have aux (c : G'.ConnectedComponent) (hc : Odd c.supp.ncard) :
      {c' : G.ConnectedComponent | Odd c'.supp.ncard ∧ c'.supp subseteq c.supp}.Nonempty := by
    refine Set.nonempty_of_ncard_ne_zero fun h' => Nat.not_odd_zero ?_
    rw [← h']
    exact (c.odd_oddComponents_ncard_subset_supp _ h).2 hc
  let f : G'.oddComponents -> G.oddComponents :=
    fun ⟨c, hc⟩ => ⟨(aux c hc).choose, (aux c hc).choose_spec.1⟩
  refine Nat.card_le_card_of_injective f fun c c' fcc' => ?_
  simp only [Subtype.mk.injEq, f] at fcc'
  exact Subtype.val_injective (ConnectedComponent.eq_of_common_vertex
    ((fcc' ▸ (aux c.1 c.2).choose_spec.2) (ConnectedComponent.nonempty_supp _).some_mem)
      ((aux c'.1 c'.2).choose_spec.2 (ConnectedComponent.nonempty_supp _).some_mem))

中文:
引理 ncard_oddComponents_mono
  条件: [有限 V] {G' : 简单图 V} (h : G <= G')
  证明: by
  have aux (c : G'.ConnectedComponent) (hc : Odd c.supp.ncard) :
      {c' : G.ConnectedComponent | Odd c'.supp.ncard ∧ c'.supp subseteq c.supp}.Nonempty := by
    refine Set.nonempty_of_ncard_ne_zero fun h' => Nat.not_odd_zero ?_
    rw [← h']
    exact (c.odd_oddComponents_ncard_subset_supp _ h).2 hc
  let f : G'.oddComponents -> G.oddComponents :=
    fun ⟨c, hc⟩ => ⟨(aux c hc).choose, (aux c hc).choose_spec.1⟩
  refine Nat.card_le_card_of_injective f fun c c' fcc' => ?_
  simp only [Subtype.mk.injEq, f] at fcc'
  exact Subtype.val_injective (ConnectedComponent.eq_of_common_vertex
    ((fcc' ▸ (aux c.1 c.2).choose_spec.2) (ConnectedComponent.nonempty_supp _).some_mem)
      ((aux c'.1 c'.2).choose_spec.2 (ConnectedComponent.nonempty_supp _).some_mem))

Depends on / 依赖: ConnectedComponent, G.ConnectedComponent, G.oddComponents, Nat.card_le_card_of_injective, Nat.not_odd_zero, Nonempty, Set.nonempty_of_ncard_ne_zero, Subtype, Subtype.mk.injEq, c.odd_oddComponents_ncard_subset_supp, c.supp, c.supp.ncard, card_le_card_of_injective, choose_spec, nonempty_of_ncard_ne_zero, not_odd_zero, oddComponents, odd_oddComponents_ncard_subset_supp, subseteq, supp.ncard
-/
lemma ncard_oddComponents_mono [Finite V] {G' : SimpleGraph V} (h : G <= G') :
     G'.oddComponents.ncard <= G.oddComponents.ncard := by
  have aux (c : G'.ConnectedComponent) (hc : Odd c.supp.ncard) :
      {c' : G.ConnectedComponent | Odd c'.supp.ncard ∧ c'.supp subseteq c.supp}.Nonempty := by
    refine Set.nonempty_of_ncard_ne_zero fun h' => Nat.not_odd_zero ?_
    rw [← h']
    exact (c.odd_oddComponents_ncard_subset_supp _ h).2 hc
  let f : G'.oddComponents -> G.oddComponents :=
    fun ⟨c, hc⟩ => ⟨(aux c hc).choose, (aux c hc).choose_spec.1⟩
  refine Nat.card_le_card_of_injective f fun c c' fcc' => ?_
  simp only [Subtype.mk.injEq, f] at fcc'
  exact Subtype.val_injective (ConnectedComponent.eq_of_common_vertex
    ((fcc' ▸ (aux c.1 c.2).choose_spec.2) (ConnectedComponent.nonempty_supp _).some_mem)
      ((aux c'.1 c'.2).choose_spec.2 (ConnectedComponent.nonempty_supp _).some_mem))

end SimpleGraph
