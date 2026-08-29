/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Regularity.Chunk
public import Mathlib.Combinatorics.SimpleGraph.Regularity.Energy

/-!
# Increment partition for Szemerédi Regularity Lemma

In the proof of Szemerédi Regularity Lemma, we need to partition each part of a starting partition
to increase the energy. This file defines the partition obtained by gluing the parts partitions
together (the *increment partition*) and shows that the energy globally increases.

This entire file is internal to the proof of Szemerédi Regularity Lemma.

## Main declarations

* `SzemerediRegularity.increment`: The increment partition.
* `SzemerediRegularity.card_increment`: The increment partition is much bigger than the original,
  but by a controlled amount.
* `SzemerediRegularity.energy_increment`: The increment partition has energy greater than the
  original by a known (small) fixed amount.

## TODO

Once ported to mathlib4, this file will be a great golfing ground for Heather's new tactic
`gcongr`.

## References

[Yaël Dillies, Bhavik Mehta, *Formalising Szemerédi’s Regularity Lemma in Lean*][srl_itp]
-/

@[expose] public section


open Finset Fintype SimpleGraph SzemerediRegularity

open scoped SzemerediRegularity.Positivity

variable {α : Type*} [Fintype α] [DecidableEq α] {P : Finpartition (univ : Finset α)}
  (hP : P.IsEquipartition) (G : SimpleGraph α) [DecidableRel G.Adj] (ε : Real)

local notation3 "m" => (card α / stepBound #P.parts : Nat)

namespace SzemerediRegularity

/--
Definition of `increment` / `increment` 的定义

English:
definition increment
  signature: : Finpartition (univ : Finset α)
  body: P.bind fun _ => chunk hP G ε

中文:
定义 increment
  签名: : Finpartition (univ : Finset α)
  定义体: P.bind fun _ => chunk hP G ε

Depends on / 依赖: P.bind
-/
noncomputable def increment : Finpartition (univ : Finset α) :=
  P.bind fun _ => chunk hP G ε

open Finpartition Finpartition.IsEquipartition

variable {hP G ε}

/--
theorem `card_increment` / 定理 `card_increment`

English:
theorem card_increment
  given: (hPα : #P.parts * 16 ^ #P.parts <= card α) (hPG : ¬P.IsUniform G ε)
  proof: by
  have hPα' : stepBound #P.parts <= card α := by grw [← hPα, stepBound]; gcongr; simp
  have hPpos : 0 < stepBound #P.parts := stepBound_pos (nonempty_of_not_uniform hPG).card_pos
  rw [increment]; rw [card_bind]
  simp_rw [chunk, apply_dite Finpartition.parts, apply_dite card, sum_dite]
  rw [su

中文:
定理 card_increment
  条件: (hPα : #P.parts * 16 ^ #P.parts <= card α) (hPG : ¬P.IsUniform G ε)
  证明: by
  have hPα' : stepBound #P.parts <= card α := by grw [← hPα, stepBound]; gcongr; simp
  have hPpos : 0 < stepBound #P.parts := stepBound_pos (nonempty_of_not_uniform hPG).card_pos
  rw [increment]; rw [card_bind]
  simp_rw [chunk, apply_dite Finpartition.parts, apply_dite card, sum_dite]
  rw [su

Depends on / 依赖: Finpartition, Finpartition.parts, Nat.div_pos, Nat.sub_ad, P.parts, any_goals, apply_dite, card_attach, card_bind, card_parts_equitabilise, card_pos, div_pos, increment, nonempty_of_not_uniform, simp_rw, stepBound, stepBound_pos, sub_ad, sum_const_nat, sum_dite
-/
theorem card_increment (hPα : #P.parts * 16 ^ #P.parts <= card α) (hPG : ¬P.IsUniform G ε) :
    #(increment hP G ε).parts = stepBound #P.parts := by
  have hPα' : stepBound #P.parts <= card α := by grw [← hPα, stepBound]; gcongr; simp
  have hPpos : 0 < stepBound #P.parts := stepBound_pos (nonempty_of_not_uniform hPG).card_pos
  rw [increment]; rw [card_bind]
  simp_rw [chunk, apply_dite Finpartition.parts, apply_dite card, sum_dite]
  rw [sum_const_nat]; rw [sum_const_nat]; rw [univ_eq_attach]; rw [univ_eq_attach]; rw [card_attach]; rw [card_attach]
  any_goals exact fun x hx => card_parts_equitabilise _ _ (Nat.div_pos hPα' hPpos).ne'
  rw [Nat.sub_add_cancel a_add_one_le_four_pow_parts_card]; rw [Nat.sub_add_cancel ((Nat.le_succ _).trans a_add_one_le_four_pow_parts_card)]; rw [← add_mul]
  congr
  rw [card_filter_add_card_filter_not]; rw [card_attach]

variable (hP G ε)

/--
theorem `increment_isEquipartition` / 定理 `increment_isEquipartition`

English:
theorem increment_isEquipartition
  statement: (increment hP G ε).IsEquipartition
  proof: by
  simp_rw [IsEquipartition, Set.equitableOn_iff_exists_eq_eq_add_one]
  refine ⟨m, fun A hA => ?_⟩
  rw [mem_coe]; rw [increment]; rw [mem_bind] at hA
  obtain ⟨U, hU, hA⟩ := hA
  exact card_eq_of_mem_parts_chunk hA

中文:
定理 increment_isEquipartition
  结论: (increment hP G ε).IsEquipartition
  证明: by
  simp_rw [IsEquipartition, Set.equitableOn_iff_exists_eq_eq_add_one]
  refine ⟨m, fun A hA => ?_⟩
  rw [mem_coe]; rw [increment]; rw [mem_bind] at hA
  obtain ⟨U, hU, hA⟩ := hA
  exact card_eq_of_mem_parts_chunk hA

Depends on / 依赖: IsEquipartition, Set.equitableOn_iff_exists_eq_eq_add_one, card_eq_of_mem_parts_chunk, equitableOn_iff_exists_eq_eq_add_one, increment, mem_bind, mem_coe, simp_rw
-/
theorem increment_isEquipartition : (increment hP G ε).IsEquipartition := by
  simp_rw [IsEquipartition, Set.equitableOn_iff_exists_eq_eq_add_one]
  refine ⟨m, fun A hA => ?_⟩
  rw [mem_coe]; rw [increment]; rw [mem_bind] at hA
  obtain ⟨U, hU, hA⟩ := hA
  exact card_eq_of_mem_parts_chunk hA

set_option backward.privateInPublic true in
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def distinctPairs (x : {x // x in P.parts.offDiag})
  body: (chunk hP G ε (mem_offDiag.1 x.2).1).parts ×ˢ (chunk hP G ε (mem_offDiag.1 x.2).2.1).parts

中文:
定义 noncomputable
  签名: def distinctPairs (x : {x // x in P.parts.offDiag})
  定义体: (chunk hP G ε (mem_offDiag.1 x.2).1).parts ×ˢ (chunk hP G ε (mem_offDiag.1 x.2).2.1).parts
-/
private noncomputable def distinctPairs (x : {x // x in P.parts.offDiag}) :
    Finset (Finset α × Finset α) :=
  (chunk hP G ε (mem_offDiag.1 x.2).1).parts ×ˢ (chunk hP G ε (mem_offDiag.1 x.2).2.1).parts

variable {hP G ε}

/--
theorem `distinctPairs_increment` / 定理 `distinctPairs_increment`

English:
theorem distinctPairs_increment
  proof: by
  rintro ⟨Ui, Vj⟩
  simp only [distinctPairs, increment, mem_offDiag, bind_parts, mem_biUnion, Prod.exists,
    mem_product, mem_attach, true_and, Subtype.exists, and_imp,
    mem_offDiag, forall_exists_index, Ne]
  refine fun U V hUV hUi hVj => ⟨⟨_, hUV.1, hUi⟩, ⟨_, hUV.2.1, hVj⟩, ?_⟩
  rintro r

中文:
定理 distinctPairs_increment
  证明: by
  rintro ⟨Ui, Vj⟩
  simp only [distinctPairs, increment, mem_offDiag, bind_parts, mem_biUnion, Prod.exists,
    mem_product, mem_attach, true_and, Subtype.exists, and_imp,
    mem_offDiag, forall_exists_index, Ne]
  refine fun U V hUV hUi hVj => ⟨⟨_, hUV.1, hUi⟩, ⟨_, hUV.2.1, hVj⟩, ?_⟩
  rintro r
-/
private theorem distinctPairs_increment :
    P.parts.offDiag.attach.biUnion (distinctPairs hP G ε) subseteq (increment hP G ε).parts.offDiag := by
  rintro ⟨Ui, Vj⟩
  simp only [distinctPairs, increment, mem_offDiag, bind_parts, mem_biUnion, Prod.exists,
    mem_product, mem_attach, true_and, Subtype.exists, and_imp,
    mem_offDiag, forall_exists_index, Ne]
  refine fun U V hUV hUi hVj => ⟨⟨_, hUV.1, hUi⟩, ⟨_, hUV.2.1, hVj⟩, ?_⟩
  rintro rfl
  obtain ⟨i, hi⟩ := nonempty_of_mem_parts _ hUi
  exact hUV.2.2 (P.disjoint.elim_finset hUV.1 hUV.2.1 i (Finpartition.le _ hUi hi) <|
    Finpartition.le _ hVj hi)

/--
lemma `pairwiseDisjoint_distinctPairs` / 引理 `pairwiseDisjoint_distinctPairs`

English:
lemma pairwiseDisjoint_distinctPairs
  proof: by
  simp +unfoldPartialApp only [distinctPairs, Set.PairwiseDisjoint,
    Function.onFun, Finset.disjoint_left, mem_product]
  rintro ⟨⟨s₁, s₂⟩, hs⟩ _ ⟨⟨t₁, t₂⟩, ht⟩ _ hst ⟨u, v⟩ huv₁ huv₂
  rw [mem_offDiag] at hs ht
  obtain ⟨a, ha⟩ := Finpartition.nonempty_of_mem_parts _ huv₁.1
  obtain ⟨b, hb⟩ :

中文:
引理 pairwiseDisjoint_distinctPairs
  证明: by
  simp +unfoldPartialApp only [distinctPairs, Set.PairwiseDisjoint,
    Function.onFun, Finset.disjoint_left, mem_product]
  rintro ⟨⟨s₁, s₂⟩, hs⟩ _ ⟨⟨t₁, t₂⟩, ht⟩ _ hst ⟨u, v⟩ huv₁ huv₂
  rw [mem_offDiag] at hs ht
  obtain ⟨a, ha⟩ := Finpartition.nonempty_of_mem_parts _ huv₁.1
  obtain ⟨b, hb⟩ :
-/
private lemma pairwiseDisjoint_distinctPairs :
    (P.parts.offDiag.attach : Set {x // x in P.parts.offDiag}).PairwiseDisjoint
      (distinctPairs hP G ε) := by
  simp +unfoldPartialApp only [distinctPairs, Set.PairwiseDisjoint,
    Function.onFun, Finset.disjoint_left, mem_product]
  rintro ⟨⟨s₁, s₂⟩, hs⟩ _ ⟨⟨t₁, t₂⟩, ht⟩ _ hst ⟨u, v⟩ huv₁ huv₂
  rw [mem_offDiag] at hs ht
  obtain ⟨a, ha⟩ := Finpartition.nonempty_of_mem_parts _ huv₁.1
  obtain ⟨b, hb⟩ := Finpartition.nonempty_of_mem_parts _ huv₁.2
exact hst Subtype.ext Prod.ext
    (P.disjoint.elim_finset hs.1 ht.1 a (Finpartition.le _ huv₁.1 ha) <|
      Finpartition.le _ huv₂.1 ha) <|
P.disjoint.elim_finset hs.2.1 ht.2.1 b (Finpartition.le _ huv₁.2 hb)
          Finpartition.le _ huv₂.2 hb

variable [Nonempty α]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
lemma `le_sum_distinctPairs_edgeDensity_sq` / 引理 `le_sum_distinctPairs_edgeDensity_sq`

English:
lemma le_sum_distinctPairs_edgeDensity_sq
  statement: (x : {i // i in P.parts.offDiag}) (hε₁ : ε <= 1)
  proof: by
  rw [distinctPairs]; rw [← add_sub_assoc]; rw [add_sub_right_comm]
  split_ifs with h
  · rw [add_zero]
    exact edgeDensity_chunk_uniform hPα hPε _ _
  · exact edgeDensity_chunk_not_uniform hPα hPε hε₁ (mem_offDiag.1 x.2).2.2 h

中文:
引理 le_sum_distinctPairs_edgeDensity_sq
  结论: (x : {i // i in P.parts.offDiag}) (hε₁ : ε <= 1)
  证明: by
  rw [distinctPairs]; rw [← add_sub_assoc]; rw [add_sub_right_comm]
  split_ifs with h
  · rw [add_zero]
    exact edgeDensity_chunk_uniform hPα hPε _ _
  · exact edgeDensity_chunk_not_uniform hPα hPε hε₁ (mem_offDiag.1 x.2).2.2 h

Depends on / 依赖: add_sub_assoc, add_sub_right_comm, add_zero, distinctPairs, edgeDensity_chunk_not_uniform, edgeDensity_chunk_uniform, mem_offDiag, split_ifs
-/
lemma le_sum_distinctPairs_edgeDensity_sq (x : {i // i in P.parts.offDiag}) (hε₁ : ε <= 1)
    (hPα : #P.parts * 16 ^ #P.parts <= card α) (hPε : ↑100 <= ↑4 ^ #P.parts * ε ^ 5) :
    (G.edgeDensity x.1.1 x.1.2 : Real) ^ 2 +
      ((if G.IsUniform ε x.1.1 x.1.2 then 0 else ε ^ 4 / 3) - ε ^ 5 / 25) <=
    (∑ i in distinctPairs hP G ε x, G.edgeDensity i.1 i.2 ^ 2 : Real) / 16 ^ #P.parts := by
  rw [distinctPairs]; rw [← add_sub_assoc]; rw [add_sub_right_comm]
  split_ifs with h
  · rw [add_zero]
    exact edgeDensity_chunk_uniform hPα hPε _ _
  · exact edgeDensity_chunk_not_uniform hPα hPε hε₁ (mem_offDiag.1 x.2).2.2 h

/--
theorem `energy_increment` / 定理 `energy_increment`

English:
theorem energy_increment
  statement: (hP : P.IsEquipartition) (hP₇ : 7 <= #P.parts)
  proof: by
  calc
    _ = (∑ x in P.parts.offDiag, (G.edgeDensity x.1 x.2 : Real) ^ 2 +
          #P.parts ^ 2 * (ε ^ 5 / 4) : Real) / #P.parts ^ 2 := by
        rw [coe_energy]; rw [add_div]; rw [mul_div_cancel_left₀]; positivity
    _ <= (∑ x in P.parts.offDiag.attach, (∑ i in distinctPairs hP G ε x,
    

中文:
定理 energy_increment
  结论: (hP : P.IsEquipartition) (hP₇ : 7 <= #P.parts)
  证明: by
  calc
    _ = (∑ x in P.parts.offDiag, (G.edgeDensity x.1 x.2 : Real) ^ 2 +
          #P.parts ^ 2 * (ε ^ 5 / 4) : Real) / #P.parts ^ 2 := by
        rw [coe_energy]; rw [add_div]; rw [mul_div_cancel_left₀]; positivity
    _ <= (∑ x in P.parts.offDiag.attach, (∑ i in distinctPairs hP G ε x,
    

Depends on / 依赖: G.edgeDensity, P.parts, P.parts.offDiag, P.parts.offDiag.attach, add_div, attach, card_increment, coe_energy, distinctPairs, edgeDensity, increment, offDiag
-/
theorem energy_increment (hP : P.IsEquipartition) (hP₇ : 7 <= #P.parts)
    (hPε : 100 <= 4 ^ #P.parts * ε ^ 5) (hPα : #P.parts * 16 ^ #P.parts <= card α)
    (hPG : ¬P.IsUniform G ε) (hε₀ : 0 <= ε) (hε₁ : ε <= 1) :
    ↑(P.energy G) + ε ^ 5 / 4 <= (increment hP G ε).energy G := by
  calc
    _ = (∑ x in P.parts.offDiag, (G.edgeDensity x.1 x.2 : Real) ^ 2 +
          #P.parts ^ 2 * (ε ^ 5 / 4) : Real) / #P.parts ^ 2 := by
        rw [coe_energy]; rw [add_div]; rw [mul_div_cancel_left₀]; positivity
    _ <= (∑ x in P.parts.offDiag.attach, (∑ i in distinctPairs hP G ε x,
          G.edgeDensity i.1 i.2 ^ 2 : Real) / 16 ^ #P.parts) / #P.parts ^ 2 := ?_
    _ = (∑ x in P.parts.offDiag.attach, ∑ i in distinctPairs hP G ε x,
          G.edgeDensity i.1 i.2 ^ 2 : Real) / #(increment hP G ε).parts ^ 2 := by
        rw [card_increment hPα hPG]; rw [coe_stepBound]; rw [mul_pow]; rw [pow_right_comm]; rw [div_mul_eq_div_div_swap]; rw [← sum_div]; norm_num
    _ <= _ := by
        rw [coe_energy]
        gcongr
        rw [← sum_biUnion pairwiseDisjoint_distinctPairs]
        exact sum_le_sum_of_subset_of_nonneg distinctPairs_increment fun i _ _ => sq_nonneg _
  gcongr
  rw [Finpartition.IsUniform]; rw [not_le]; rw [mul_tsub]; rw [mul_one]; rw [← offDiag_card] at hPG
  calc
    _ <= ∑ x in P.parts.offDiag, (edgeDensity G x.1 x.2 : Real) ^ 2 +
        (#(nonUniforms P G ε) * (ε ^ 4 / 3) - #P.parts.offDiag * (ε ^ 5 / 25)) := ?_
    _ = ∑ x in P.parts.offDiag, ((G.edgeDensity x.1 x.2 : Real) ^ 2 +
        ((if G.IsUniform ε x.1 x.2 then (0 : Real) else ε ^ 4 / 3) - ε ^ 5 / 25) : Real) := by
        rw [sum_add_distrib]; rw [sum_sub_distrib]; rw [sum_const]; rw [nsmul_eq_mul]; rw [sum_ite]; rw [sum_const_zero]; rw [zero_add]; rw [sum_const]; rw [nsmul_eq_mul]; rw [← Finpartition.nonUniforms]; rw [← add_sub_assoc]; rw [add_sub_right_comm]
    _ = _ := (sum_attach ..).symm
    _ <= _ := sum_le_sum fun i _ => le_sum_distinctPairs_edgeDensity_sq i hε₁ hPα hPε
  gcongr
  calc
    _ = (6 / 7 * #P.parts ^ 2) * ε ^ 5 * (7 / 24) := by ring
    _ <= #P.parts.offDiag * ε ^ 5 * (22 / 75) := by
        gcongr ?_ * _ * ?_
        · rw [← mul_div_right_comm, div_le_iff₀ (by simp), offDiag_card]
          norm_cast
          rw [tsub_mul]
          refine le_tsub_of_add_le_left ?_
          nlinarith
        · norm_num
    _ = (#P.parts.offDiag * ε * (ε ^ 4 / 3) - #P.parts.offDiag * (ε ^ 5 / 25)) := by ring
    _ <= (#(nonUniforms P G ε) * (ε ^ 4 / 3) - #P.parts.offDiag * (ε ^ 5 / 25)) := by gcongr

end SzemerediRegularity
