/-
Copyright (c) 2025 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
module

public import Mathlib.Algebra.Order.Group.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Cyclic linearly ordered groups

This file contains basic results about cyclic linearly ordered groups and cyclic subgroups of
linearly ordered groups.

The definitions `LinearOrderedCommGroup.Subgroup.genLTOne` (*resp.*
`LinearOrderedCommGroup.genLTOne`) yields a generator of a non-trivial subgroup of a linearly
ordered commutative group with (*resp.* of a non-trivial linearly ordered commutative group) that
is strictly less than `1`. The corresponding additive definitions are also provided.
-/

@[expose] public section

noncomputable section

namespace LinearOrderedCommGroup

open LinearOrderedCommGroup

variable {G : Type*} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G]

namespace Subgroup

variable (H : Subgroup G) [Nontrivial H] [hH : IsCyclic H]

@[to_additive exists_neg_generator]
/--
lemma `exists_generator_lt_one` / 引理 `exists_generator_lt_one`

English:
lemma exists_generator_lt_one
  statement: exists (a : G), a < 1 ∧ Subgroup.zpowers a = H
  proof: by
  obtain ⟨a, ha⟩ := H.isCyclic_iff_exists_zpowers_eq_top.mp hH
  obtain ha1 | rfl | ha1 := lt_trichotomy a 1
  · exact ⟨a, ha1, ha⟩
  · rw [Subgroup.zpowers_one_eq_bot] at ha
exact absurd ha.symm (H.nontrivial_iff_ne_bot).mp inferInstance
  · use a⁻¹, Left.inv_lt_one_iff.mpr ha1
    rw [Subgroup.

中文:
引理 exists_generator_lt_one
  结论: 存在 (a : G), a < 1 ∧ Subgroup.zpowers a = H
  证明: by
  obtain ⟨a, ha⟩ := H.isCyclic_iff_exists_zpowers_eq_top.mp hH
  obtain ha1 | rfl | ha1 := lt_trichotomy a 1
  · exact ⟨a, ha1, ha⟩
  · rw [Subgroup.zpowers_one_eq_bot] at ha
exact absurd ha.symm (H.nontrivial_iff_ne_bot).mp inferInstance
  · use a⁻¹, Left.inv_lt_one_iff.mpr ha1
    rw [Subgroup.

Depends on / 依赖: H.isCyclic_iff_exists_zpowers_eq_top.mp, H.nontrivial_iff_ne_bot, Left.inv_lt_one_iff.mpr, Subgroup, Subgroup.zpowers_inv, Subgroup.zpowers_one_eq_bot, absurd, ha.symm, inv_lt_one_iff, isCyclic_iff_exists_zpowers_eq_top, lt_trichotomy, nontrivial_iff_ne_bot, zpowers_inv, zpowers_one_eq_bot
-/
lemma exists_generator_lt_one : exists (a : G), a < 1 ∧ Subgroup.zpowers a = H := by
  obtain ⟨a, ha⟩ := H.isCyclic_iff_exists_zpowers_eq_top.mp hH
  obtain ha1 | rfl | ha1 := lt_trichotomy a 1
  · exact ⟨a, ha1, ha⟩
  · rw [Subgroup.zpowers_one_eq_bot] at ha
exact absurd ha.symm (H.nontrivial_iff_ne_bot).mp inferInstance
  · use a⁻¹, Left.inv_lt_one_iff.mpr ha1
    rw [Subgroup.zpowers_inv]; rw [ha]

/-- Given a subgroup of a cyclic linearly ordered commutative group, this is a generator of
the subgroup that is `< 1`. -/
@[to_additive negGen /-- Given an additive subgroup of an additive cyclic linearly ordered
commutative group, this is a negative generator of the subgroup. -/]
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def genLTOne
  body: H.exists_generator_lt_one.choose

@[to_additive negGen_neg]

中文:
定义 noncomputable
  签名: def genLTOne
  定义体: H.exists_generator_lt_one.choose

@[to_additive negGen_neg]
-/
protected noncomputable def genLTOne : G := H.exists_generator_lt_one.choose

@[to_additive negGen_neg]
/--
lemma `genLTOne_lt_one` / 引理 `genLTOne_lt_one`

English:
lemma genLTOne_lt_one
  statement: H.genLTOne < 1
  proof: H.exists_generator_lt_one.choose_spec.1

@[to_additive (attr := simp) negGen_zmultiples_eq_top]

中文:
引理 genLTOne_lt_one
  结论: H.genLTOne < 1
  证明: H.exists_generator_lt_one.choose_spec.1

@[to_additive (attr := simp) negGen_zmultiples_eq_top]

Depends on / 依赖: H.exists_generator_lt_one.choose_spec, choose_spec, exists_generator_lt_one
-/
lemma genLTOne_lt_one : H.genLTOne < 1 :=
  H.exists_generator_lt_one.choose_spec.1

@[to_additive (attr := simp) negGen_zmultiples_eq_top]
/--
lemma `genLTOne_zpowers_eq_top` / 引理 `genLTOne_zpowers_eq_top`

English:
lemma genLTOne_zpowers_eq_top
  statement: Subgroup.zpowers H.genLTOne = H
  proof: H.exists_generator_lt_one.choose_spec.2

中文:
引理 genLTOne_zpowers_eq_top
  结论: Subgroup.zpowers H.genLTOne = H
  证明: H.exists_generator_lt_one.choose_spec.2

Depends on / 依赖: H.exists_generator_lt_one.choose_spec, choose_spec, exists_generator_lt_one
-/
lemma genLTOne_zpowers_eq_top : Subgroup.zpowers H.genLTOne = H :=
  H.exists_generator_lt_one.choose_spec.2

/--
lemma `genLTOne_mem` / 引理 `genLTOne_mem`

English:
lemma genLTOne_mem
  statement: H.genLTOne in H
  proof: by
  nth_rewrite 1 [← H.genLTOne_zpowers_eq_top]
  exact Subgroup.mem_zpowers (Subgroup.genLTOne H)

中文:
引理 genLTOne_mem
  结论: H.genLTOne in H
  证明: by
  nth_rewrite 1 [← H.genLTOne_zpowers_eq_top]
  exact Subgroup.mem_zpowers (Subgroup.genLTOne H)

Depends on / 依赖: H.genLTOne_zpowers_eq_top, Subgroup, Subgroup.genLTOne, Subgroup.mem_zpowers, genLTOne, genLTOne_zpowers_eq_top, mem_zpowers, nth_rewrite
-/
lemma genLTOne_mem : H.genLTOne in H := by
  nth_rewrite 1 [← H.genLTOne_zpowers_eq_top]
  exact Subgroup.mem_zpowers (Subgroup.genLTOne H)

/--
lemma `genLTOne_unique` / 引理 `genLTOne_unique`

English:
lemma genLTOne_unique
  given: {g : G} (hg : g < 1) (hH : Subgroup.zpowers g = H)
  statement: g = H.genLTOne
  proof: by
  have hg' : ¬ IsOfFinOrder g := not_isOfFinOrder_of_isMulTorsionFree (ne_of_lt hg)
  rw [← H.genLTOne_zpowers_eq_top] at hH
  rcases (Subgroup.zpowers_eq_zpowers_iff hg').mp hH with _ | h
  · assumption
  rw [← one_lt_inv']; rw [h] at hg
  exact (not_lt_of_gt hg <| Subgroup.genLTOne_lt_one _).el

中文:
引理 genLTOne_unique
  条件: {g : G} (hg : g < 1) (hH : Subgroup.zpowers g = H)
  结论: g = H.genLTOne
  证明: by
  have hg' : ¬ IsOfFinOrder g := not_isOfFinOrder_of_isMulTorsionFree (ne_of_lt hg)
  rw [← H.genLTOne_zpowers_eq_top] at hH
  rcases (Subgroup.zpowers_eq_zpowers_iff hg').mp hH with _ | h
  · assumption
  rw [← one_lt_inv']; rw [h] at hg
  exact (not_lt_of_gt hg <| Subgroup.genLTOne_lt_one _).el

Depends on / 依赖: H.genLTOne_zpowers_eq_top, IsOfFinOrder, Subgroup, Subgroup.genLTOne_lt_one, Subgroup.zpowers_eq_zpowers_iff, genLTOne_lt_one, genLTOne_zpowers_eq_top, ne_of_lt, not_isOfFinOrder_of_isMulTorsionFree, not_lt_of_gt, one_lt_inv, zpowers_eq_zpowers_iff
-/
lemma genLTOne_unique {g : G} (hg : g < 1) (hH : Subgroup.zpowers g = H) : g = H.genLTOne := by
  have hg' : ¬ IsOfFinOrder g := not_isOfFinOrder_of_isMulTorsionFree (ne_of_lt hg)
  rw [← H.genLTOne_zpowers_eq_top] at hH
  rcases (Subgroup.zpowers_eq_zpowers_iff hg').mp hH with _ | h
  · assumption
  rw [← one_lt_inv']; rw [h] at hg
  exact (not_lt_of_gt hg <| Subgroup.genLTOne_lt_one _).elim

/--
lemma `genLTOne_unique_of_zpowers_eq` / 引理 `genLTOne_unique_of_zpowers_eq`

English:
lemma genLTOne_unique_of_zpowers_eq
  statement: {g1 g2 : G} (hg1 : g1 < 1) (hg2 : g2 < 1)
  proof: by
  rcases (Subgroup.zpowers g2).bot_or_nontrivial with (h' | h')
  · rw [h'] at h
    simp_all only [Subgroup.zpowers_eq_bot]
  · have h1 : IsCyclic ↥(Subgroup.zpowers g2) := by
      rw [Subgroup.isCyclic_iff_exists_zpowers_eq_top]; use g2
    have h2 : Nontrivial ↥(Subgroup.zpowers g1) := by rw 

中文:
引理 genLTOne_unique_of_zpowers_eq
  结论: {g1 g2 : G} (hg1 : g1 < 1) (hg2 : g2 < 1)
  证明: by
  rcases (Subgroup.zpowers g2).bot_or_nontrivial with (h' | h')
  · rw [h'] at h
    simp_all only [Subgroup.zpowers_eq_bot]
  · have h1 : IsCyclic ↥(Subgroup.zpowers g2) := by
      rw [Subgroup.isCyclic_iff_exists_zpowers_eq_top]; use g2
    have h2 : Nontrivial ↥(Subgroup.zpowers g1) := by rw 

Depends on / 依赖: IsCyclic, Nontrivial, Subgroup, Subgroup.isCyclic_iff_exists_zpowers_eq_top, Subgroup.zpowers, Subgroup.zpowers_eq_bot, bot_or_nontrivial, genLTOne_unique, h.symm, isCyclic_iff_exists_zpowers_eq_top, zpowers, zpowers_eq_bot
-/
lemma genLTOne_unique_of_zpowers_eq {g1 g2 : G} (hg1 : g1 < 1) (hg2 : g2 < 1)
    (h : Subgroup.zpowers g1 = Subgroup.zpowers g2) : g1 = g2 := by
  rcases (Subgroup.zpowers g2).bot_or_nontrivial with (h' | h')
  · rw [h'] at h
    simp_all only [Subgroup.zpowers_eq_bot]
  · have h1 : IsCyclic ↥(Subgroup.zpowers g2) := by
      rw [Subgroup.isCyclic_iff_exists_zpowers_eq_top]; use g2
    have h2 : Nontrivial ↥(Subgroup.zpowers g1) := by rw [h]; exact h'
    have h3 : IsCyclic ↥(Subgroup.zpowers g1) := by rw [h]; exact h1
    simp only [(Subgroup.zpowers g2).genLTOne_unique hg1 h]
    simp only [← h]
    simp only [(Subgroup.zpowers g1).genLTOne_unique hg2 h.symm]

end Subgroup

section IsCyclic

variable (G) [Nontrivial G] [IsCyclic G]

/-- Given a cyclic linearly ordered commutative group, this is a generator that is `< 1`. -/
@[to_additive negGen /-- Given an additive cyclic linearly ordered commutative group, this is a
negative generator of it. -/]
/--
Definition of `genLTOne` / `genLTOne` 的定义

English:
definition genLTOne
  signature: : G
  body: (⊤ : Subgroup G).genLTOne

@[to_additive (attr := simp) negGen_eq_of_top]

中文:
定义 genLTOne
  签名: : G
  定义体: (⊤ : Subgroup G).genLTOne

@[to_additive (attr := simp) negGen_eq_of_top]

Depends on / 依赖: Subgroup, genLTOne
-/
noncomputable def genLTOne : G := (⊤ : Subgroup G).genLTOne

@[to_additive (attr := simp) negGen_eq_of_top]
/--
lemma `genLTOne_eq_of_top` / 引理 `genLTOne_eq_of_top`

English:
lemma genLTOne_eq_of_top
  statement: genLTOne G = (⊤ : Subgroup G).genLTOne
  proof: rfl

中文:
引理 genLTOne_eq_of_top
  结论: genLTOne G = (⊤ : Subgroup G).genLTOne
  证明: rfl
-/
lemma genLTOne_eq_of_top : genLTOne G = (⊤ : Subgroup G).genLTOne := rfl

/--
lemma `genLTOne_unique` / 引理 `genLTOne_unique`

English:
lemma genLTOne_unique
  given: {g : G} (hg : g < 1) (htop : Subgroup.zpowers g = ⊤)
  statement: g = genLTOne G
  proof: (⊤ : Subgroup G).genLTOne_unique hg htop

中文:
引理 genLTOne_unique
  条件: {g : G} (hg : g < 1) (htop : Subgroup.zpowers g = ⊤)
  结论: g = genLTOne G
  证明: (⊤ : Subgroup G).genLTOne_unique hg htop

Depends on / 依赖: Subgroup, genLTOne_unique
-/
lemma genLTOne_unique {g : G} (hg : g < 1) (htop : Subgroup.zpowers g = ⊤) : g = genLTOne G :=
  (⊤ : Subgroup G).genLTOne_unique hg htop

end IsCyclic

end LinearOrderedCommGroup
