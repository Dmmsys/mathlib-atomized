/-
Copyright (c) 2021 Jordan Brown, Thomas Browning, Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jordan Brown, Thomas Browning, Patrick Lutz
-/
module

public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Rank
public import Mathlib.GroupTheory.Index

/-!
The commutator of a finite direct product is contained in the direct product of the commutators.
-/

public section

variable {G : Type*} [Group G]

namespace Subgroup

/-- The commutator of a finite direct product is contained in the direct product of the commutators.
-/
@[to_additive /-- The commutator of a finite direct product is contained in the direct product of
the commutators. -/]
/--
theorem `commutator_pi_pi_of_finite` / 定理 `commutator_pi_pi_of_finite`

English:
theorem commutator_pi_pi_of_finite
  statement: {η : Type*} [Finite η] {Gs : η -> Type*} [forall i, Group (Gs i)]
  proof: by
  classical
    apply le_antisymm (commutator_pi_pi_le H K)
    rw [pi_le_iff]
    intro i hi
    rw [map_commutator]
    apply commutator_mono <;>
      · rw [le_pi_iff]
        intro j _hj
        rintro _ ⟨x, hx, rfl⟩
        by_cases h : j = i
        · subst h
          simpa using hx
      

中文:
定理 commutator_pi_pi_of_finite
  结论: {η : 类型} [有限 η] {Gs : η -> 类型} [对任意 i, 群 (Gs i)]
  证明: by
  classical
    apply le_antisymm (commutator_pi_pi_le H K)
    rw [pi_le_iff]
    intro i hi
    rw [map_commutator]
    apply commutator_mono <;>
      · rw [le_pi_iff]
        intro j _hj
        rintro _ ⟨x, hx, rfl⟩
        by_cases h : j = i
        · subst h
          simpa using hx
      

Depends on / 依赖: classical, commutator_mono, commutator_pi_pi_le, le_antisymm, le_pi_iff, map_commutator, one_mem, pi_le_iff
-/
theorem commutator_pi_pi_of_finite {η : Type*} [Finite η] {Gs : η -> Type*} [forall i, Group (Gs i)]
    (H K : forall i, Subgroup (Gs i)) : ⁅Subgroup.pi Set.univ H, Subgroup.pi Set.univ K⁆ =
    Subgroup.pi Set.univ fun i => ⁅H i, K i⁆ := by
  classical
    apply le_antisymm (commutator_pi_pi_le H K)
    rw [pi_le_iff]
    intro i hi
    rw [map_commutator]
    apply commutator_mono <;>
      · rw [le_pi_iff]
        intro j _hj
        rintro _ ⟨x, hx, rfl⟩
        by_cases h : j = i
        · subst h
          simpa using hx
        · simp [h, one_mem]

variable [Finite (commutatorSet G)]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Group.FG (_root_.commutator G)
  body: by
  rw [commutator_eq_closure]; apply Group.closure_finite_fg

中文:
实例 :
  签名: 群.FG (_root_.commutator G)
  定义体: by
  rw [commutator_eq_closure]; apply Group.closure_finite_fg

Depends on / 依赖: Group.closure_finite_fg, closure_finite_fg, commutator_eq_closure
-/
instance : Group.FG (_root_.commutator G) := by
  rw [commutator_eq_closure]; apply Group.closure_finite_fg

variable (G) in
/--
lemma `rank_commutator_le_card` / 引理 `rank_commutator_le_card`

English:
lemma rank_commutator_le_card
  statement: Group.rank (_root_.commutator G) <= Nat.card (commutatorSet G)
  proof: by
  rw [Subgroup.rank_congr (commutator_eq_closure G)]
  apply Subgroup.rank_closure_finite_le_nat_card

中文:
引理 rank_commutator_le_card
  结论: 群.rank (_root_.commutator G) <= 自然数.card (commutatorSet G)
  证明: by
  rw [Subgroup.rank_congr (commutator_eq_closure G)]
  apply Subgroup.rank_closure_finite_le_nat_card

Depends on / 依赖: Subgroup, Subgroup.rank_closure_finite_le_nat_card, Subgroup.rank_congr, commutator_eq_closure, rank_closure_finite_le_nat_card, rank_congr
-/
lemma rank_commutator_le_card : Group.rank (_root_.commutator G) <= Nat.card (commutatorSet G) := by
  rw [Subgroup.rank_congr (commutator_eq_closure G)]
  apply Subgroup.rank_closure_finite_le_nat_card

variable [Group.FG G]

/--
Instance `finiteIndex_center` / 实例 `finiteIndex_center`

English:
instance finiteIndex_center
  signature: : FiniteIndex (center G)
  body: by
  obtain ⟨S, -, hS⟩ := Group.rank_spec G
  exact ⟨mt (Finite.card_eq_zero_of_embedding (quotientCenterEmbedding hS)) Finite.card_pos.ne'⟩

中文:
实例 finiteIndex_center
  签名: : FiniteIndex (center G)
  定义体: by
  obtain ⟨S, -, hS⟩ := Group.rank_spec G
  exact ⟨mt (Finite.card_eq_zero_of_embedding (quotientCenterEmbedding hS)) Finite.card_pos.ne'⟩

Depends on / 依赖: Finite, Finite.card_eq_zero_of_embedding, Finite.card_pos.ne, Group.rank_spec, card_eq_zero_of_embedding, card_pos, quotientCenterEmbedding, rank_spec
-/
instance finiteIndex_center : FiniteIndex (center G) := by
  obtain ⟨S, -, hS⟩ := Group.rank_spec G
  exact ⟨mt (Finite.card_eq_zero_of_embedding (quotientCenterEmbedding hS)) Finite.card_pos.ne'⟩

variable (G) in
/--
lemma `index_center_le_pow` / 引理 `index_center_le_pow`

English:
lemma index_center_le_pow
  statement: (center G).index <= Nat.card (commutatorSet G) ^ Group.rank G
  proof: by
  obtain ⟨S, hS1, hS2⟩ := Group.rank_spec G
  rw [← hS1]; rw [← Fintype.card_coe]; rw [← Nat.card_eq_fintype_card]; rw [← Finset.coe_sort_coe]; rw [← Nat.card_fun]
  exact Finite.card_le_of_embedding (quotientCenterEmbedding hS2)

中文:
引理 index_center_le_pow
  结论: (center G).index <= 自然数.card (commutatorSet G) ^ 群.rank G
  证明: by
  obtain ⟨S, hS1, hS2⟩ := Group.rank_spec G
  rw [← hS1]; rw [← Fintype.card_coe]; rw [← Nat.card_eq_fintype_card]; rw [← Finset.coe_sort_coe]; rw [← Nat.card_fun]
  exact Finite.card_le_of_embedding (quotientCenterEmbedding hS2)

Depends on / 依赖: Finite, Finite.card_le_of_embedding, Finset, Finset.coe_sort_coe, Fintype, Fintype.card_coe, Group.rank_spec, Nat.card_eq_fintype_card, Nat.card_fun, card_coe, card_eq_fintype_card, card_fun, card_le_of_embedding, coe_sort_coe, quotientCenterEmbedding, rank_spec
-/
lemma index_center_le_pow : (center G).index <= Nat.card (commutatorSet G) ^ Group.rank G := by
  obtain ⟨S, hS1, hS2⟩ := Group.rank_spec G
  rw [← hS1]; rw [← Fintype.card_coe]; rw [← Nat.card_eq_fintype_card]; rw [← Finset.coe_sort_coe]; rw [← Nat.card_fun]
  exact Finite.card_le_of_embedding (quotientCenterEmbedding hS2)

end Subgroup

section commutatorRepresentatives

open Subgroup

/--
lemma `card_commutatorSet_closureCommutatorRepresentatives` / 引理 `card_commutatorSet_closureCommutatorRepresentatives`

English:
lemma card_commutatorSet_closureCommutatorRepresentatives
  proof: by
  rw [← image_commutatorSet_closureCommutatorRepresentatives G]
  exact Nat.card_congr (Equiv.Set.image _ _ (subtype_injective _))

中文:
引理 card_commutatorSet_closureCommutatorRepresentatives
  证明: by
  rw [← image_commutatorSet_closureCommutatorRepresentatives G]
  exact Nat.card_congr (Equiv.Set.image _ _ (subtype_injective _))

Depends on / 依赖: Equiv.Set.image, Nat.card_congr, card_congr, image_commutatorSet_closureCommutatorRepresentatives, subtype_injective
-/
lemma card_commutatorSet_closureCommutatorRepresentatives :
    Nat.card (commutatorSet (closureCommutatorRepresentatives G)) = Nat.card (commutatorSet G) := by
  rw [← image_commutatorSet_closureCommutatorRepresentatives G]
  exact Nat.card_congr (Equiv.Set.image _ _ (subtype_injective _))

/--
lemma `card_commutator_closureCommutatorRepresentatives` / 引理 `card_commutator_closureCommutatorRepresentatives`

English:
lemma card_commutator_closureCommutatorRepresentatives
  proof: by
  rw [commutator_eq_closure G]; rw [← image_commutatorSet_closureCommutatorRepresentatives]; rw [←
    MonoidHom.map_closure]; rw [← commutator_eq_closure]
  exact Nat.card_congr (Equiv.Set.image _ _ (subtype_injective _))

中文:
引理 card_commutator_closureCommutatorRepresentatives
  证明: by
  rw [commutator_eq_closure G]; rw [← image_commutatorSet_closureCommutatorRepresentatives]; rw [←
    MonoidHom.map_closure]; rw [← commutator_eq_closure]
  exact Nat.card_congr (Equiv.Set.image _ _ (subtype_injective _))

Depends on / 依赖: Equiv.Set.image, MonoidHom, MonoidHom.map_closure, Nat.card_congr, card_congr, commutator_eq_closure, image_commutatorSet_closureCommutatorRepresentatives, map_closure, subtype_injective
-/
lemma card_commutator_closureCommutatorRepresentatives :
    Nat.card (commutator (closureCommutatorRepresentatives G)) = Nat.card (commutator G) := by
  rw [commutator_eq_closure G]; rw [← image_commutatorSet_closureCommutatorRepresentatives]; rw [←
    MonoidHom.map_closure]; rw [← commutator_eq_closure]
  exact Nat.card_congr (Equiv.Set.image _ _ (subtype_injective _))

variable [Finite (commutatorSet G)]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Finite (commutatorRepresentatives G)
  body: Set.finite_coe_iff.mpr (Set.finite_range _)

中文:
实例 :
  签名: 有限 (commutatorRepresentatives G)
  定义体: Set.finite_coe_iff.mpr (Set.finite_range _)

Depends on / 依赖: Set.finite_coe_iff.mpr, Set.finite_range, finite_coe_iff, finite_range
-/
instance : Finite (commutatorRepresentatives G) := Set.finite_coe_iff.mpr (Set.finite_range _)

/--
Instance `closureCommutatorRepresentatives_fg` / 实例 `closureCommutatorRepresentatives_fg`

English:
instance closureCommutatorRepresentatives_fg
  signature: : Group.FG (closureCommutatorRepresentatives G)
  body: Group.closure_finite_fg _

中文:
实例 closureCommutatorRepresentatives_fg
  签名: : 群.FG (closureCommutatorRepresentatives G)
  定义体: Group.closure_finite_fg _

Depends on / 依赖: Group.closure_finite_fg, closure_finite_fg
-/
instance closureCommutatorRepresentatives_fg : Group.FG (closureCommutatorRepresentatives G) :=
  Group.closure_finite_fg _

variable (G) in
/--
lemma `rank_closureCommutatorRepresentatives_le` / 引理 `rank_closureCommutatorRepresentatives_le`

English:
lemma rank_closureCommutatorRepresentatives_le
  proof: by
  rw [two_mul]
  exact
    (Subgroup.rank_closure_finite_le_nat_card _).trans
      ((Set.card_union_le _ _).trans
        (add_le_add ((Finite.card_image_le _).trans (Finite.card_range_le _))
          ((Finite.card_image_le _).trans (Finite.card_range_le _))))

中文:
引理 rank_closureCommutatorRepresentatives_le
  证明: by
  rw [two_mul]
  exact
    (Subgroup.rank_closure_finite_le_nat_card _).trans
      ((Set.card_union_le _ _).trans
        (add_le_add ((Finite.card_image_le _).trans (Finite.card_range_le _))
          ((Finite.card_image_le _).trans (Finite.card_range_le _))))

Depends on / 依赖: Finite, Finite.card_image_le, Finite.card_range_le, Set.card_union_le, Subgroup, Subgroup.rank_closure_finite_le_nat_card, add_le_add, card_image_le, card_range_le, card_union_le, rank_closure_finite_le_nat_card, two_mul
-/
lemma rank_closureCommutatorRepresentatives_le :
    Group.rank (closureCommutatorRepresentatives G) <= 2 * Nat.card (commutatorSet G) := by
  rw [two_mul]
  exact
    (Subgroup.rank_closure_finite_le_nat_card _).trans
      ((Set.card_union_le _ _).trans
        (add_le_add ((Finite.card_image_le _).trans (Finite.card_range_le _))
          ((Finite.card_image_le _).trans (Finite.card_range_le _))))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Finite (commutatorSet (closureCommutatorRepresentatives G))
  body: by
  apply Nat.finite_of_card_ne_zero
  rw [card_commutatorSet_closureCommutatorRepresentatives]
  exact Finite.card_pos.ne'

中文:
实例 :
  签名: 有限 (commutatorSet (closureCommutatorRepresentatives G))
  定义体: by
  apply Nat.finite_of_card_ne_zero
  rw [card_commutatorSet_closureCommutatorRepresentatives]
  exact Finite.card_pos.ne'

Depends on / 依赖: Finite, Finite.card_pos.ne, Nat.finite_of_card_ne_zero, card_commutatorSet_closureCommutatorRepresentatives, card_pos, finite_of_card_ne_zero
-/
instance : Finite (commutatorSet (closureCommutatorRepresentatives G)) := by
  apply Nat.finite_of_card_ne_zero
  rw [card_commutatorSet_closureCommutatorRepresentatives]
  exact Finite.card_pos.ne'

end commutatorRepresentatives
