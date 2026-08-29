/-
Copyright (c) 2025 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.GroupTheory.Finiteness
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Rank of a group

This file defines the rank of a group, namely the minimum size of a generating set.

## TODO

Should we define `erank G : ℕ∞` the rank of a not necessarily finitely generated group `G`,
then redefine `rank G` as `(erank G).toNat`? Maybe a `Cardinal`-valued version too?
-/

@[expose] public section

open Function Group

variable {G H : Type*} [Group G] [Group H]

namespace Group

variable (G) in
/-- The minimum number of generators of a group. -/
@[to_additive /-- The minimum number of generators of an additive group. -/]
/--
Definition of `rank` / `rank` 的定义

English:
definition rank
  signature: [h : FG G]
  body: @Nat.find _ (Classical.decPred _) (fg_iff'.mp h)

中文:
定义 rank
  签名: [h : FG G]
  定义体: @Nat.find _ (Classical.decPred _) (fg_iff'.mp h)

Depends on / 依赖: Classical, Classical.decPred, Nat.find, decPred, fg_iff
-/
noncomputable def rank [h : FG G] : Nat := @Nat.find _ (Classical.decPred _) (fg_iff'.mp h)

variable (G) in
@[to_additive]
/--
lemma `rank_spec` / 引理 `rank_spec`

English:
lemma rank_spec
  given: [h : FG G]
  statement: exists S : Finset G, S.card = rank G ∧ .closure S = (⊤ : Subgroup G)
  proof: @Nat.find_spec _ (Classical.decPred _) (fg_iff'.mp h)

@[to_additive]

中文:
引理 rank_spec
  条件: [h : FG G]
  结论: 存在 S : 有限集 G, S.card = rank G ∧ .closure S = (⊤ : 子群 G)
  证明: @Nat.find_spec _ (Classical.decPred _) (fg_iff'.mp h)

@[to_additive]

Depends on / 依赖: Classical, Classical.decPred, Nat.find_spec, decPred, fg_iff, find_spec
-/
lemma rank_spec [h : FG G] : exists S : Finset G, S.card = rank G ∧ .closure S = (⊤ : Subgroup G) :=
  @Nat.find_spec _ (Classical.decPred _) (fg_iff'.mp h)

@[to_additive]
/--
lemma `rank_le` / 引理 `rank_le`

English:
lemma rank_le
  given: [h : FG G] {S : Finset G} (hS : .closure S = (⊤ : Subgroup G))
  statement: rank G <= S.card
  proof: @Nat.find_le _ _ (Classical.decPred _) (fg_iff'.mp h) ⟨S, rfl, hS⟩

中文:
引理 rank_le
  条件: [h : FG G] {S : 有限集 G} (hS : .closure S = (⊤ : 子群 G))
  结论: rank G <= S.card
  证明: @Nat.find_le _ _ (Classical.decPred _) (fg_iff'.mp h) ⟨S, rfl, hS⟩

Depends on / 依赖: Classical, Classical.decPred, Nat.find_le, decPred, fg_iff, find_le
-/
lemma rank_le [h : FG G] {S : Finset G} (hS : .closure S = (⊤ : Subgroup G)) : rank G <= S.card :=
  @Nat.find_le _ _ (Classical.decPred _) (fg_iff'.mp h) ⟨S, rfl, hS⟩

variable (G) in
@[to_additive (attr := nontriviality)]
/--
theorem `rank_eq_zero` / 定理 `rank_eq_zero`

English:
theorem rank_eq_zero
  given: [Subsingleton G]
  statement: rank G = 0
  proof: by
  rw [← le_zero_iff]; rw [← Finset.card_empty]
  exact rank_le (Subsingleton.elim _ _)

@[to_additive]

中文:
定理 rank_eq_zero
  条件: [子单例 G]
  结论: rank G = 0
  证明: by
  rw [← le_zero_iff]; rw [← Finset.card_empty]
  exact rank_le (Subsingleton.elim _ _)

@[to_additive]

Depends on / 依赖: Finset, Finset.card_empty, Subsingleton, Subsingleton.elim, card_empty, le_zero_iff, rank_le
-/
theorem rank_eq_zero [Subsingleton G] : rank G = 0 := by
  rw [← le_zero_iff]; rw [← Finset.card_empty]
  exact rank_le (Subsingleton.elim _ _)

@[to_additive]
/--
theorem `rank_eq_zero_iff` / 定理 `rank_eq_zero_iff`

English:
theorem rank_eq_zero_iff
  given: [FG G]
  statement: rank G = 0 ↔ Subsingleton G
  proof: by
  refine ⟨fun h => ?_, fun _ => rank_eq_zero G⟩
  obtain ⟨s, hs, hs'⟩ := rank_spec G
  rw [h]; rw [Finset.card_eq_zero] at hs
  simpa [hs, subsingleton_iff_bot_eq_top] using hs'

中文:
定理 rank_eq_zero_iff
  条件: [FG G]
  结论: rank G = 0 ↔ 子单例 G
  证明: by
  refine ⟨fun h => ?_, fun _ => rank_eq_zero G⟩
  obtain ⟨s, hs, hs'⟩ := rank_spec G
  rw [h]; rw [Finset.card_eq_zero] at hs
  simpa [hs, subsingleton_iff_bot_eq_top] using hs'

Depends on / 依赖: Finset, Finset.card_eq_zero, card_eq_zero, rank_eq_zero, rank_spec, subsingleton_iff_bot_eq_top
-/
theorem rank_eq_zero_iff [FG G] : rank G = 0 ↔ Subsingleton G := by
  refine ⟨fun h => ?_, fun _ => rank_eq_zero G⟩
  obtain ⟨s, hs, hs'⟩ := rank_spec G
  rw [h]; rw [Finset.card_eq_zero] at hs
  simpa [hs, subsingleton_iff_bot_eq_top] using hs'

variable (G) in
@[to_additive]
/--
theorem `rank_pos` / 定理 `rank_pos`

English:
theorem rank_pos
  given: [Nontrivial G] [FG G]
  statement: 0 < rank G
  proof: by
  rwa [pos_iff_ne_zero, ne_eq, rank_eq_zero_iff, not_subsingleton_iff_nontrivial]

中文:
定理 rank_pos
  条件: [非平凡 G] [FG G]
  结论: 0 < rank G
  证明: by
  rwa [pos_iff_ne_zero, ne_eq, rank_eq_zero_iff, not_subsingleton_iff_nontrivial]

Depends on / 依赖: ne_eq, not_subsingleton_iff_nontrivial, pos_iff_ne_zero, rank_eq_zero_iff
-/
theorem rank_pos [Nontrivial G] [FG G] : 0 < rank G := by
  rwa [pos_iff_ne_zero, ne_eq, rank_eq_zero_iff, not_subsingleton_iff_nontrivial]

-- TODO: Prove monotonicity of `rank` along injective homomorphisms of abelian groups. This could
-- potentially be deduced from a (yet unproved) analogous statement for `Submodule.spanRank`.
@[to_additive]
/--
lemma `rank_le_of_surjective` / 引理 `rank_le_of_surjective`

English:
lemma rank_le_of_surjective
  given: [FG G] [FG H] (f : G ->* H) (hf : Surjective f)
  statement: rank H <= rank G
  proof: by
  classical
  obtain ⟨S, hS1, hS2⟩ := rank_spec G
  trans (S.image f).card
  · apply rank_le
    rw [Finset.coe_image]; rw [← MonoidHom.map_closure]; rw [hS2]; rw [Subgroup.map_top_of_surjective f hf]
  · exact Finset.card_image_le.trans_eq hS1

@[to_additive]

中文:
引理 rank_le_of_surjective
  条件: [FG G] [FG H] (f : G ->* H) (hf : 满射 f)
  结论: rank H <= rank G
  证明: by
  classical
  obtain ⟨S, hS1, hS2⟩ := rank_spec G
  trans (S.image f).card
  · apply rank_le
    rw [Finset.coe_image]; rw [← MonoidHom.map_closure]; rw [hS2]; rw [Subgroup.map_top_of_surjective f hf]
  · exact Finset.card_image_le.trans_eq hS1

@[to_additive]

Depends on / 依赖: Finset, Finset.card_image_le.trans_eq, Finset.coe_image, MonoidHom, MonoidHom.map_closure, S.image, Subgroup, Subgroup.map_top_of_surjective, card_image_le, classical, coe_image, map_closure, map_top_of_surjective, rank_le, rank_spec, trans_eq
-/
lemma rank_le_of_surjective [FG G] [FG H] (f : G ->* H) (hf : Surjective f) : rank H <= rank G := by
  classical
  obtain ⟨S, hS1, hS2⟩ := rank_spec G
  trans (S.image f).card
  · apply rank_le
    rw [Finset.coe_image]; rw [← MonoidHom.map_closure]; rw [hS2]; rw [Subgroup.map_top_of_surjective f hf]
  · exact Finset.card_image_le.trans_eq hS1

@[to_additive]
/--
lemma `rank_range_le` / 引理 `rank_range_le`

English:
lemma rank_range_le
  given: [FG G] {f : G ->* H}
  statement: rank f.range <= rank G
  proof: rank_le_of_surjective f.rangeRestrict f.rangeRestrict_surjective

@[to_additive]

中文:
引理 rank_range_le
  条件: [FG G] {f : G ->* H}
  结论: rank f.range <= rank G
  证明: rank_le_of_surjective f.rangeRestrict f.rangeRestrict_surjective

@[to_additive]

Depends on / 依赖: f.rangeRestrict, f.rangeRestrict_surjective, rangeRestrict, rangeRestrict_surjective, rank_le_of_surjective
-/
lemma rank_range_le [FG G] {f : G ->* H} : rank f.range <= rank G :=
  rank_le_of_surjective f.rangeRestrict f.rangeRestrict_surjective

@[to_additive]
/--
lemma `rank_congr` / 引理 `rank_congr`

English:
lemma rank_congr
  given: [FG G] [FG H] (e : G ≃* H)
  statement: rank G = rank H
  proof: le_antisymm (rank_le_of_surjective e.symm e.symm.surjective)
    (rank_le_of_surjective e e.surjective)

中文:
引理 rank_congr
  条件: [FG G] [FG H] (e : G ≃* H)
  结论: rank G = rank H
  证明: le_antisymm (rank_le_of_surjective e.symm e.symm.surjective)
    (rank_le_of_surjective e e.surjective)

Depends on / 依赖: e.surjective, e.symm, e.symm.surjective, le_antisymm, rank_le_of_surjective, surjective
-/
lemma rank_congr [FG G] [FG H] (e : G ≃* H) : rank G = rank H :=
  le_antisymm (rank_le_of_surjective e.symm e.symm.surjective)
    (rank_le_of_surjective e e.surjective)

end Group

namespace Subgroup

@[to_additive]
/--
lemma `rank_congr` / 引理 `rank_congr`

English:
lemma rank_congr
  given: {H K : Subgroup G} [Group.FG H] [Group.FG K] (h : H = K)
  statement: rank H = rank K
  proof: by
  subst h; rfl

@[to_additive]

中文:
引理 rank_congr
  条件: {H K : 子群 G} [群.FG H] [群.FG K] (h : H = K)
  结论: rank H = rank K
  证明: by
  subst h; rfl

@[to_additive]
-/
lemma rank_congr {H K : Subgroup G} [Group.FG H] [Group.FG K] (h : H = K) : rank H = rank K := by
  subst h; rfl

@[to_additive]
/--
lemma `rank_closure_finset_le_card` / 引理 `rank_closure_finset_le_card`

English:
lemma rank_closure_finset_le_card
  given: (s : Finset G)
  statement: rank (closure (s : Set G)) <= s.card
  proof: by
  classical
  let t : Finset (closure (s : Set G)) := s.preimage Subtype.val Subtype.coe_injective.injOn
  have ht : closure (t : Set (closure (s : Set G))) = ⊤ := by
    rw [Finset.coe_preimage]
    exact closure_preimage_eq_top (s : Set G)
  apply (rank_le ht).trans
  suffices H : Set.InjOn Sub

中文:
引理 rank_closure_finset_le_card
  条件: (s : 有限集 G)
  结论: rank (closure (s : 集合 G)) <= s.card
  证明: by
  classical
  let t : Finset (closure (s : Set G)) := s.preimage Subtype.val Subtype.coe_injective.injOn
  have ht : closure (t : Set (closure (s : Set G))) = ⊤ := by
    rw [Finset.coe_preimage]
    exact closure_preimage_eq_top (s : Set G)
  apply (rank_le ht).trans
  suffices H : Set.InjOn Sub

Depends on / 依赖: Finset, Finset.card_filter_le, Finset.card_image_of_injOn, Finset.coe_preimage, Finset.image_preimage, Set.InjOn, Subtype, Subtype.coe_injective.injOn, Subtype.val, card_filter_le, card_image_of_injOn, classical, closure, closure_preimage_eq_top, coe_injective, coe_preimage, image_preimage, preimage, rank_le, s.preimage
-/
lemma rank_closure_finset_le_card (s : Finset G) : rank (closure (s : Set G)) <= s.card := by
  classical
  let t : Finset (closure (s : Set G)) := s.preimage Subtype.val Subtype.coe_injective.injOn
  have ht : closure (t : Set (closure (s : Set G))) = ⊤ := by
    rw [Finset.coe_preimage]
    exact closure_preimage_eq_top (s : Set G)
  apply (rank_le ht).trans
  suffices H : Set.InjOn Subtype.val (t : Set (closure (s : Set G))) by
    rw [← Finset.card_image_of_injOn H]; rw [Finset.image_preimage]
    apply Finset.card_filter_le
  apply Subtype.coe_injective.injOn

@[to_additive]
/--
lemma `rank_closure_finite_le_nat_card` / 引理 `rank_closure_finite_le_nat_card`

English:
lemma rank_closure_finite_le_nat_card
  given: (s : Set G) [Finite s]
  statement: rank (closure s) <= Nat.card s
  proof: by
  have := Fintype.ofFinite s
  rw [Nat.card_eq_fintype_card]; rw [← s.toFinset_card]; rw [← rank_congr (congr_arg _ s.coe_toFinset)]
  exact rank_closure_finset_le_card s.toFinset

中文:
引理 rank_closure_finite_le_nat_card
  条件: (s : 集合 G) [有限 s]
  结论: rank (closure s) <= 自然数.card s
  证明: by
  have := Fintype.ofFinite s
  rw [Nat.card_eq_fintype_card]; rw [← s.toFinset_card]; rw [← rank_congr (congr_arg _ s.coe_toFinset)]
  exact rank_closure_finset_le_card s.toFinset

Depends on / 依赖: Fintype, Fintype.ofFinite, Nat.card_eq_fintype_card, card_eq_fintype_card, coe_toFinset, congr_arg, ofFinite, rank_closure_finset_le_card, rank_congr, s.coe_toFinset, s.toFinset, s.toFinset_card, toFinset, toFinset_card
-/
lemma rank_closure_finite_le_nat_card (s : Set G) [Finite s] : rank (closure s) <= Nat.card s := by
  have := Fintype.ofFinite s
  rw [Nat.card_eq_fintype_card]; rw [← s.toFinset_card]; rw [← rank_congr (congr_arg _ s.coe_toFinset)]
  exact rank_closure_finset_le_card s.toFinset

/--
lemma `nat_card_centralizer_nat_card_stabilizer` / 引理 `nat_card_centralizer_nat_card_stabilizer`

English:
lemma nat_card_centralizer_nat_card_stabilizer
  given: (g : G)
  proof: by
  rw [centralizer_eq_comap_stabilizer]; rfl

中文:
引理 nat_card_centralizer_nat_card_stabilizer
  条件: (g : G)
  证明: by
  rw [centralizer_eq_comap_stabilizer]; rfl

Depends on / 依赖: centralizer_eq_comap_stabilizer
-/
lemma nat_card_centralizer_nat_card_stabilizer (g : G) :
    Nat.card (centralizer {g}) = Nat.card (MulAction.stabilizer (ConjAct G) g) := by
  rw [centralizer_eq_comap_stabilizer]; rfl

end Subgroup
