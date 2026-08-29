/-
Copyright (c) 2025 Vlad Tsyrklevich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vlad Tsyrklevich
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Set.Card
public import Mathlib.SetTheory.Cardinal.NatCard

import Mathlib.Tactic.ENatToNat

/-!
# Vertex cover

A *vertex cover* of a simple graph is a set of vertices such that every edge is incident to at least
one of the vertices in the set.

## Main definitions

* `SimpleGraph.IsVertexCover G c`: Predicate that `c` is a vertex cover of `G`.
* `SimpleGraph.vertexCoverNum G`: The vertex cover number, e.g. the size of a minimal vertex cover.
-/

@[expose] public section

namespace SimpleGraph

variable {V W : Type*} {G G' : SimpleGraph V} {H : SimpleGraph W}

section IsVertexCover

/--
Definition of `IsVertexCover` / `IsVertexCover` 的定义

English:
definition IsVertexCover
  signature: (G : SimpleGraph V) (c : Set V)
  body: forall ⦃v w : V⦄, G.Adj v w -> v in c ∨ w in c

@[simp]

中文:
定义 IsVertexCover
  签名: (G : 简单图 V) (c : 集合 V)
  定义体: forall ⦃v w : V⦄, G.Adj v w -> v in c ∨ w in c

@[simp]

Depends on / 依赖: G.Adj
-/
def IsVertexCover (G : SimpleGraph V) (c : Set V) : Prop :=
  forall ⦃v w : V⦄, G.Adj v w -> v in c ∨ w in c

@[simp]
/--
theorem `isVertexCover_empty` / 定理 `isVertexCover_empty`

English:
theorem isVertexCover_empty
  statement: IsVertexCover G ∅ ↔ G = ⊥
  proof: by
  simp [IsVertexCover, eq_bot_iff_forall_not_adj]

@[simp]

中文:
定理 isVertexCover_empty
  结论: IsVertexCover G ∅ ↔ G = ⊥
  证明: by
  simp [IsVertexCover, eq_bot_iff_forall_not_adj]

@[simp]

Depends on / 依赖: IsVertexCover, eq_bot_iff_forall_not_adj
-/
theorem isVertexCover_empty : IsVertexCover G ∅ ↔ G = ⊥ := by
  simp [IsVertexCover, eq_bot_iff_forall_not_adj]

@[simp]
/--
theorem `isVertexCover_univ` / 定理 `isVertexCover_univ`

English:
theorem isVertexCover_univ
  statement: IsVertexCover G .univ
  proof: by
  simp [IsVertexCover]

@[simp]

中文:
定理 isVertexCover_univ
  结论: IsVertexCover G .univ
  证明: by
  simp [IsVertexCover]

@[simp]

Depends on / 依赖: IsVertexCover
-/
theorem isVertexCover_univ : IsVertexCover G .univ := by
  simp [IsVertexCover]

@[simp]
/--
theorem `isVertexCover_bot` / 定理 `isVertexCover_bot`

English:
theorem isVertexCover_bot
  given: (c : Set V)
  statement: IsVertexCover ⊥ c
  proof: by
  simp [IsVertexCover]

中文:
定理 isVertexCover_bot
  条件: (c : 集合 V)
  结论: IsVertexCover ⊥ c
  证明: by
  simp [IsVertexCover]

Depends on / 依赖: IsVertexCover
-/
theorem isVertexCover_bot (c : Set V) : IsVertexCover ⊥ c := by
  simp [IsVertexCover]

/--
theorem `IsVertexCover.subset` / 定理 `IsVertexCover.subset`

English:
theorem IsVertexCover.subset
  given: {c d : Set V} (hcd : c subseteq d) (hc : IsVertexCover G c)
  proof: by
  grind [IsVertexCover]

中文:
定理 IsVertexCover.subset
  条件: {c d : 集合 V} (hcd : c subseteq d) (hc : IsVertexCover G c)
  证明: by
  grind [IsVertexCover]

Depends on / 依赖: IsVertexCover
-/
theorem IsVertexCover.subset {c d : Set V} (hcd : c subseteq d) (hc : IsVertexCover G c) :
    IsVertexCover G d := by
  grind [IsVertexCover]

/--
theorem `IsVertexCover.mono` / 定理 `IsVertexCover.mono`

English:
theorem IsVertexCover.mono
  given: {c : Set V} (hG : G <= G') (hc : IsVertexCover G' c)
  proof: fun _ _ hadj => hc (hG hadj)

中文:
定理 IsVertexCover.mono
  条件: {c : 集合 V} (hG : G <= G') (hc : IsVertexCover G' c)
  证明: fun _ _ hadj => hc (hG hadj)
-/
theorem IsVertexCover.mono {c : Set V} (hG : G <= G') (hc : IsVertexCover G' c) :
    IsVertexCover G c :=
  fun _ _ hadj => hc (hG hadj)

/-- A set `c` is a vertex cover iff the complement of `c` is an independent set. -/
@[simp]
/--
theorem `isIndepSet_compl_iff_isVertexCover` / 定理 `isIndepSet_compl_iff_isVertexCover`

English:
theorem isIndepSet_compl_iff_isVertexCover
  given: {c : Set V}
  statement: G.IsIndepSet cᶜ ↔ IsVertexCover G c
  proof: by
  refine ⟨fun hi v w hadj => ?_, by grind [IsVertexCover, Set.Pairwise]⟩
  by_contra! hh
  exact hi hh.1 hh.2 (Adj.ne hadj) hadj

@[simp]

中文:
定理 isIndepSet_compl_iff_isVertexCover
  条件: {c : 集合 V}
  结论: G.IsIndepSet cᶜ ↔ IsVertexCover G c
  证明: by
  refine ⟨fun hi v w hadj => ?_, by grind [IsVertexCover, Set.Pairwise]⟩
  by_contra! hh
  exact hi hh.1 hh.2 (Adj.ne hadj) hadj

@[simp]

Depends on / 依赖: Adj.ne, IsVertexCover, Pairwise, Set.Pairwise
-/
theorem isIndepSet_compl_iff_isVertexCover {c : Set V} : G.IsIndepSet cᶜ ↔ IsVertexCover G c := by
  refine ⟨fun hi v w hadj => ?_, by grind [IsVertexCover, Set.Pairwise]⟩
  by_contra! hh
  exact hi hh.1 hh.2 (Adj.ne hadj) hadj

@[simp]
/--
theorem `isVertexCover_compl` / 定理 `isVertexCover_compl`

English:
theorem isVertexCover_compl
  given: {c : Set V}
  statement: G.IsVertexCover cᶜ ↔ G.IsIndepSet c
  proof: by
  simp [← isIndepSet_compl_iff_isVertexCover]

中文:
定理 isVertexCover_compl
  条件: {c : 集合 V}
  结论: G.IsVertexCover cᶜ ↔ G.IsIndepSet c
  证明: by
  simp [← isIndepSet_compl_iff_isVertexCover]

Depends on / 依赖: isIndepSet_compl_iff_isVertexCover
-/
theorem isVertexCover_compl {c : Set V} : G.IsVertexCover cᶜ ↔ G.IsIndepSet c := by
  simp [← isIndepSet_compl_iff_isVertexCover]

/--
theorem `IsVertexCover.preimage` / 定理 `IsVertexCover.preimage`

English:
theorem IsVertexCover.preimage
  statement: {F : Type*} [FunLike F V W] [HomClass F G H]
  proof: fun _ _ hadj => hc (map_rel f hadj)

@[simp]

中文:
定理 IsVertexCover.原像
  结论: {F : 类型} [函数状 F V W] [态射类 F G H]
  证明: fun _ _ hadj => hc (map_rel f hadj)

@[simp]

Depends on / 依赖: map_rel
-/
theorem IsVertexCover.preimage {F : Type*} [FunLike F V W] [HomClass F G H]
    (f : F) {c : Set W} (hc : IsVertexCover H c) :
    IsVertexCover G (f ⁻¹' c) :=
  fun _ _ hadj => hc (map_rel f hadj)

@[simp]
/--
theorem `isVertexCover_preimage_iso` / 定理 `isVertexCover_preimage_iso`

English:
theorem isVertexCover_preimage_iso
  given: (f : G ≃g H) {c : Set W}
  proof: by
    simpa [← RelIso.image_eq_preimage_symm, Set.image_preimage_eq _ f.surjective]
      using h.preimage f.symm
  mpr := .preimage f

@[simp]

中文:
定理 isVertexCover_preimage_iso
  条件: (f : G ≃g H) {c : 集合 W}
  证明: by
    simpa [← RelIso.image_eq_preimage_symm, Set.image_preimage_eq _ f.surjective]
      using h.preimage f.symm
  mpr := .preimage f

@[simp]

Depends on / 依赖: RelIso, RelIso.image_eq_preimage_symm, Set.image_preimage_eq, f.surjective, f.symm, h.preimage, image_eq_preimage_symm, image_preimage_eq, preimage, surjective
-/
theorem isVertexCover_preimage_iso (f : G ≃g H) {c : Set W} :
    IsVertexCover G (f ⁻¹' c) ↔ IsVertexCover H c where
  mp h := by
    simpa [← RelIso.image_eq_preimage_symm, Set.image_preimage_eq _ f.surjective]
      using h.preimage f.symm
  mpr := .preimage f

@[simp]
/--
theorem `isVertexCover_image_iso` / 定理 `isVertexCover_image_iso`

English:
theorem isVertexCover_image_iso
  given: (f : G ≃g H) {c : Set V}
  proof: by
  simp [RelIso.image_eq_preimage_symm]

中文:
定理 isVertexCover_image_iso
  条件: (f : G ≃g H) {c : 集合 V}
  证明: by
  simp [RelIso.image_eq_preimage_symm]

Depends on / 依赖: RelIso, RelIso.image_eq_preimage_symm, image_eq_preimage_symm
-/
theorem isVertexCover_image_iso (f : G ≃g H) {c : Set V} :
    IsVertexCover H (f '' c) ↔ IsVertexCover G c := by
  simp [RelIso.image_eq_preimage_symm]

end IsVertexCover

section vertexCoverNum

/--
Definition of `vertexCoverNum` / `vertexCoverNum` 的定义

English:
definition vertexCoverNum
  signature: (G : SimpleGraph V)
  body: ⨅ (s : Set V) (_ : IsVertexCover G s), s.encard

中文:
定义 vertexCoverNum
  签名: (G : 简单图 V)
  定义体: ⨅ (s : Set V) (_ : IsVertexCover G s), s.encard

Depends on / 依赖: IsVertexCover, encard, s.encard
-/
noncomputable def vertexCoverNum (G : SimpleGraph V) : Nat∞ :=
  ⨅ (s : Set V) (_ : IsVertexCover G s), s.encard

/--
theorem `vertexCoverNum_le_iff` / 定理 `vertexCoverNum_le_iff`

English:
theorem vertexCoverNum_le_iff
  given: {n : Nat∞}
  proof: by
  simp [vertexCoverNum, iInf_le_iff]

中文:
定理 vertexCoverNum_le_iff
  条件: {n : 自然数∞}
  证明: by
  simp [vertexCoverNum, iInf_le_iff]

Depends on / 依赖: iInf_le_iff, vertexCoverNum
-/
theorem vertexCoverNum_le_iff {n : Nat∞} :
    vertexCoverNum G <= n ↔ forall (m : Nat∞), (forall s, IsVertexCover G s -> m <= s.encard) -> m <= n := by
  simp [vertexCoverNum, iInf_le_iff]

/--
theorem `IsVertexCover.vertexCoverNum_le` / 定理 `IsVertexCover.vertexCoverNum_le`

English:
theorem IsVertexCover.vertexCoverNum_le
  given: {c : Set V} (hc : IsVertexCover G c)
  proof: vertexCoverNum_le_iff.mpr fun _ hm => hm c hc

中文:
定理 IsVertexCover.vertexCoverNum_le
  条件: {c : 集合 V} (hc : IsVertexCover G c)
  证明: vertexCoverNum_le_iff.mpr fun _ hm => hm c hc

Depends on / 依赖: vertexCoverNum_le_iff, vertexCoverNum_le_iff.mpr
-/
theorem IsVertexCover.vertexCoverNum_le {c : Set V} (hc : IsVertexCover G c) :
    vertexCoverNum G <= c.encard :=
  vertexCoverNum_le_iff.mpr fun _ hm => hm c hc

/--
theorem `vertexCoverNum_exists` / 定理 `vertexCoverNum_exists`

English:
theorem vertexCoverNum_exists
  given: (G)
  proof: by
  have : Nonempty {s : Set V // IsVertexCover G s} := nonempty_subtype.mpr ⟨Set.univ, by simp⟩
  obtain ⟨s, hs⟩ := @ENat.exists_eq_iInf _ this (·.val.encard)
  exact ⟨s.val, hs ▸ iInf_subtype, s.property⟩

中文:
定理 vertexCoverNum_存在
  条件: (G)
  证明: by
  have : Nonempty {s : Set V // IsVertexCover G s} := nonempty_subtype.mpr ⟨Set.univ, by simp⟩
  obtain ⟨s, hs⟩ := @ENat.exists_eq_iInf _ this (·.val.encard)
  exact ⟨s.val, hs ▸ iInf_subtype, s.property⟩

Depends on / 依赖: ENat.exists_eq_iInf, IsVertexCover, Nonempty, Set.univ, encard, exists_eq_iInf, iInf_subtype, nonempty_subtype, nonempty_subtype.mpr, property, s.property, s.val, val.encard
-/
theorem vertexCoverNum_exists (G) :
    exists s : Set V, s.encard = vertexCoverNum G ∧ IsVertexCover G s := by
  have : Nonempty {s : Set V // IsVertexCover G s} := nonempty_subtype.mpr ⟨Set.univ, by simp⟩
  obtain ⟨s, hs⟩ := @ENat.exists_eq_iInf _ this (·.val.encard)
  exact ⟨s.val, hs ▸ iInf_subtype, s.property⟩

/--
theorem `exists_of_le_vertexCoverNum` / 定理 `exists_of_le_vertexCoverNum`

English:
theorem exists_of_le_vertexCoverNum
  statement: (n : Nat) (h₁ : vertexCoverNum G <= n)
  proof: by
  obtain ⟨s, hs₁, hs₂⟩ := vertexCoverNum_exists G
  obtain ⟨r, hr₁, _, hr₃⟩ :=
    Set.exists_superset_subset_encard_eq (by simp) (le_of_eq_of_le hs₁ h₁) (Set.encard_univ _ ▸ h₂)
  exact ⟨r, hr₃, hs₂.subset hr₁⟩

@[simp]

中文:
定理 存在_of_le_vertexCoverNum
  结论: (n : 自然数) (h₁ : vertexCoverNum G <= n)
  证明: by
  obtain ⟨s, hs₁, hs₂⟩ := vertexCoverNum_exists G
  obtain ⟨r, hr₁, _, hr₃⟩ :=
    Set.exists_superset_subset_encard_eq (by simp) (le_of_eq_of_le hs₁ h₁) (Set.encard_univ _ ▸ h₂)
  exact ⟨r, hr₃, hs₂.subset hr₁⟩

@[simp]

Depends on / 依赖: Set.encard_univ, Set.exists_superset_subset_encard_eq, encard_univ, exists_superset_subset_encard_eq, le_of_eq_of_le, subset, vertexCoverNum_exists
-/
theorem exists_of_le_vertexCoverNum (n : Nat) (h₁ : vertexCoverNum G <= n)
    (h₂ : n <= ENat.card V) : exists s : Set V, s.encard = n ∧ IsVertexCover G s := by
  obtain ⟨s, hs₁, hs₂⟩ := vertexCoverNum_exists G
  obtain ⟨r, hr₁, _, hr₃⟩ :=
    Set.exists_superset_subset_encard_eq (by simp) (le_of_eq_of_le hs₁ h₁) (Set.encard_univ _ ▸ h₂)
  exact ⟨r, hr₃, hs₂.subset hr₁⟩

@[simp]
/--
theorem `vertexCoverNum_bot` / 定理 `vertexCoverNum_bot`

English:
theorem vertexCoverNum_bot
  statement: vertexCoverNum (emptyGraph V) = 0
  proof: nonpos_iff_eq_zero.mp Set.encard_empty ▸ @IsVertexCover.vertexCoverNum_le V ⊥ ∅ (by simp)

@[simp]

中文:
定理 vertexCoverNum_bot
  结论: vertexCoverNum (emptyGraph V) = 0
  证明: nonpos_iff_eq_zero.mp Set.encard_empty ▸ @IsVertexCover.vertexCoverNum_le V ⊥ ∅ (by simp)

@[simp]

Depends on / 依赖: IsVertexCover, IsVertexCover.vertexCoverNum_le, Set.encard_empty, encard_empty, nonpos_iff_eq_zero, nonpos_iff_eq_zero.mp, vertexCoverNum_le
-/
theorem vertexCoverNum_bot : vertexCoverNum (emptyGraph V) = 0 :=
nonpos_iff_eq_zero.mp Set.encard_empty ▸ @IsVertexCover.vertexCoverNum_le V ⊥ ∅ (by simp)

@[simp]
/--
theorem `vertexCoverNum_of_subsingleton` / 定理 `vertexCoverNum_of_subsingleton`

English:
theorem vertexCoverNum_of_subsingleton
  given: [Subsingleton V]
  statement: vertexCoverNum G = 0
  proof: by
  simp [SimpleGraph.subsingleton_iff.mpr _ |>.allEq G ⊥]

@[simp]

中文:
定理 vertexCoverNum_of_subsingleton
  条件: [子单例 V]
  结论: vertexCoverNum G = 0
  证明: by
  simp [SimpleGraph.subsingleton_iff.mpr _ |>.allEq G ⊥]

@[simp]

Depends on / 依赖: SimpleGraph, SimpleGraph.subsingleton_iff.mpr, subsingleton_iff
-/
theorem vertexCoverNum_of_subsingleton [Subsingleton V] : vertexCoverNum G = 0 := by
  simp [SimpleGraph.subsingleton_iff.mpr _ |>.allEq G ⊥]

@[simp]
/--
theorem `vertexCoverNum_eq_zero` / 定理 `vertexCoverNum_eq_zero`

English:
theorem vertexCoverNum_eq_zero
  statement: vertexCoverNum G = 0 ↔ G = ⊥
  proof: by
  refine ⟨fun h => ?_, by simp_all⟩
  simpa [h] using vertexCoverNum_exists G

中文:
定理 vertexCoverNum_eq_zero
  结论: vertexCoverNum G = 0 ↔ G = ⊥
  证明: by
  refine ⟨fun h => ?_, by simp_all⟩
  simpa [h] using vertexCoverNum_exists G

Depends on / 依赖: vertexCoverNum_exists
-/
theorem vertexCoverNum_eq_zero : vertexCoverNum G = 0 ↔ G = ⊥ := by
  refine ⟨fun h => ?_, by simp_all⟩
  simpa [h] using vertexCoverNum_exists G

/--
theorem `vertexCoverNum_le_card_sub_one` / 定理 `vertexCoverNum_le_card_sub_one`

English:
theorem vertexCoverNum_le_card_sub_one
  statement: vertexCoverNum G <= ENat.card V - 1
  proof: by
  nontriviality V
.to_nonempty obtain ⟨x⟩ := not_subsingleton_iff_nontrivial.mp (not_subsingleton V)
  refine ENat.forall_natCast_le_iff_le.mp fun n hn => ?_
  simp only [vertexCoverNum, le_iInf_iff] at hn
  have := hn (Set.univ \ {x}) (by grind [IsVertexCover, Adj.ne'])
  simpa [Set.encard_sdiff_singleton_of_mem (Set.mem_univ _)] using this

@[simp]

中文:
定理 vertexCoverNum_le_card_sub_one
  结论: vertexCoverNum G <= E自然数.card V - 1
  证明: by
  nontriviality V
.to_nonempty obtain ⟨x⟩ := not_subsingleton_iff_nontrivial.mp (not_subsingleton V)
  refine ENat.forall_natCast_le_iff_le.mp fun n hn => ?_
  simp only [vertexCoverNum, le_iInf_iff] at hn
  have := hn (Set.univ \ {x}) (by grind [IsVertexCover, Adj.ne'])
  simpa [Set.encard_sdiff_singleton_of_mem (Set.mem_univ _)] using this

@[simp]

Depends on / 依赖: Adj.ne, ENat.forall_natCast_le_iff_le.mp, IsVertexCover, Set.encard_sdiff_singleton_of_mem, Set.mem_univ, Set.univ, encard_sdiff_singleton_of_mem, forall_natCast_le_iff_le, le_iInf_iff, mem_univ, nontriviality, not_subsingleton, not_subsingleton_iff_nontrivial, not_subsingleton_iff_nontrivial.mp, to_nonempty, vertexCoverNum
-/
theorem vertexCoverNum_le_card_sub_one : vertexCoverNum G <= ENat.card V - 1 := by
  nontriviality V
.to_nonempty obtain ⟨x⟩ := not_subsingleton_iff_nontrivial.mp (not_subsingleton V)
  refine ENat.forall_natCast_le_iff_le.mp fun n hn => ?_
  simp only [vertexCoverNum, le_iInf_iff] at hn
  have := hn (Set.univ \ {x}) (by grind [IsVertexCover, Adj.ne'])
  simpa [Set.encard_sdiff_singleton_of_mem (Set.mem_univ _)] using this

@[simp]
/--
theorem `vertexCoverNum_ne_top_of_finite` / 定理 `vertexCoverNum_ne_top_of_finite`

English:
theorem vertexCoverNum_ne_top_of_finite
  given: [Finite V]
  statement: vertexCoverNum G != ⊤
  proof: ne_top_of_le_ne_top (by simpa) (@vertexCoverNum_le_card_sub_one V G)

中文:
定理 vertexCoverNum_ne_top_of_finite
  条件: [有限 V]
  结论: vertexCoverNum G != ⊤
  证明: ne_top_of_le_ne_top (by simpa) (@vertexCoverNum_le_card_sub_one V G)

Depends on / 依赖: ne_top_of_le_ne_top, vertexCoverNum_le_card_sub_one
-/
theorem vertexCoverNum_ne_top_of_finite [Finite V] : vertexCoverNum G != ⊤ :=
  ne_top_of_le_ne_top (by simpa) (@vertexCoverNum_le_card_sub_one V G)

/--
theorem `vertexCoverNum_lt_card` / 定理 `vertexCoverNum_lt_card`

English:
theorem vertexCoverNum_lt_card
  given: [Nonempty V] [Finite V]
  statement: vertexCoverNum G < ENat.card V
  proof: by
  refine (ENat.add_one_le_iff vertexCoverNum_ne_top_of_finite).mp ?_
  grw [vertexCoverNum_le_card_sub_one, ENat.card_eq_coe_natCard]
  enat_to_nat
  exact Nat.add_le_of_le_sub (Order.one_le_iff_pos.mpr Nat.card_pos) (le_refl _)

中文:
定理 vertexCoverNum_lt_card
  条件: [非空 V] [有限 V]
  结论: vertexCoverNum G < E自然数.card V
  证明: by
  refine (ENat.add_one_le_iff vertexCoverNum_ne_top_of_finite).mp ?_
  grw [vertexCoverNum_le_card_sub_one, ENat.card_eq_coe_natCard]
  enat_to_nat
  exact Nat.add_le_of_le_sub (Order.one_le_iff_pos.mpr Nat.card_pos) (le_refl _)

Depends on / 依赖: ENat.add_one_le_iff, ENat.card_eq_coe_natCard, Nat.add_le_of_le_sub, Nat.card_pos, Order.one_le_iff_pos.mpr, add_le_of_le_sub, add_one_le_iff, card_eq_coe_natCard, card_pos, enat_to_nat, le_refl, one_le_iff_pos, vertexCoverNum_le_card_sub_one, vertexCoverNum_ne_top_of_finite
-/
theorem vertexCoverNum_lt_card [Nonempty V] [Finite V] : vertexCoverNum G < ENat.card V := by
  refine (ENat.add_one_le_iff vertexCoverNum_ne_top_of_finite).mp ?_
  grw [vertexCoverNum_le_card_sub_one, ENat.card_eq_coe_natCard]
  enat_to_nat
  exact Nat.add_le_of_le_sub (Order.one_le_iff_pos.mpr Nat.card_pos) (le_refl _)

/--
theorem `vertexCoverNum_le_encard_edgeSet` / 定理 `vertexCoverNum_le_encard_edgeSet`

English:
theorem vertexCoverNum_le_encard_edgeSet
  statement: vertexCoverNum G <= G.edgeSet.encard
  proof: by
  by_cases h' : G.edgeSet = ∅
  · simp [h', SimpleGraph.edgeSet_eq_empty.mp]
  refine ENat.forall_natCast_le_iff_le.mp fun n hn => ?_
  simp only [vertexCoverNum, le_iInf_iff] at hn
  have := hn ((·.out.1) '' G.edgeSet)
    (fun v w _ => by grind [Sym2.out_fst_mem s(v, w), mem_edgeSet])
  grind [Set.encard_image_le]

@[simp]

中文:
定理 vertexCoverNum_le_encard_edgeSet
  结论: vertexCoverNum G <= G.edgeSet.encard
  证明: by
  by_cases h' : G.edgeSet = ∅
  · simp [h', SimpleGraph.edgeSet_eq_empty.mp]
  refine ENat.forall_natCast_le_iff_le.mp fun n hn => ?_
  simp only [vertexCoverNum, le_iInf_iff] at hn
  have := hn ((·.out.1) '' G.edgeSet)
    (fun v w _ => by grind [Sym2.out_fst_mem s(v, w), mem_edgeSet])
  grind [Set.encard_image_le]

@[simp]

Depends on / 依赖: ENat.forall_natCast_le_iff_le.mp, G.edgeSet, Set.encard_image_le, SimpleGraph, SimpleGraph.edgeSet_eq_empty.mp, Sym2.out_fst_mem, edgeSet, edgeSet_eq_empty, encard_image_le, forall_natCast_le_iff_le, le_iInf_iff, mem_edgeSet, out_fst_mem, vertexCoverNum
-/
theorem vertexCoverNum_le_encard_edgeSet : vertexCoverNum G <= G.edgeSet.encard := by
  by_cases h' : G.edgeSet = ∅
  · simp [h', SimpleGraph.edgeSet_eq_empty.mp]
  refine ENat.forall_natCast_le_iff_le.mp fun n hn => ?_
  simp only [vertexCoverNum, le_iInf_iff] at hn
  have := hn ((·.out.1) '' G.edgeSet)
    (fun v w _ => by grind [Sym2.out_fst_mem s(v, w), mem_edgeSet])
  grind [Set.encard_image_le]

@[simp]
/--
theorem `vertexCoverNum_ne_top_of_finite_edgeSet` / 定理 `vertexCoverNum_ne_top_of_finite_edgeSet`

English:
theorem vertexCoverNum_ne_top_of_finite_edgeSet
  given: (h : G.edgeSet.Finite)
  statement: vertexCoverNum G != ⊤
  proof: ne_top_of_le_ne_top (Set.encard_ne_top_iff.mpr h) vertexCoverNum_le_encard_edgeSet

@[simp]

中文:
定理 vertexCoverNum_ne_top_of_finite_edgeSet
  条件: (h : G.edgeSet.有限)
  结论: vertexCoverNum G != ⊤
  证明: ne_top_of_le_ne_top (Set.encard_ne_top_iff.mpr h) vertexCoverNum_le_encard_edgeSet

@[simp]

Depends on / 依赖: Set.encard_ne_top_iff.mpr, encard_ne_top_iff, ne_top_of_le_ne_top, vertexCoverNum_le_encard_edgeSet
-/
theorem vertexCoverNum_ne_top_of_finite_edgeSet (h : G.edgeSet.Finite) : vertexCoverNum G != ⊤ :=
  ne_top_of_le_ne_top (Set.encard_ne_top_iff.mpr h) vertexCoverNum_le_encard_edgeSet

@[simp]
/--
theorem `vertexCoverNum_top` / 定理 `vertexCoverNum_top`

English:
theorem vertexCoverNum_top
  statement: vertexCoverNum (completeGraph V) = ENat.card V - 1
  proof: by
  nontriviality V using tsub_eq_zero_of_le
  refine ENat.eq_of_forall_natCast_le_iff fun n => ⟨fun hn => ?_, fun hn => ?_⟩
  · grw [hn, vertexCoverNum_le_card_sub_one]
  by_contra! hh
  have : n - 1 <= ENat.card V := by
    grw [tsub_le_iff_right, hn]
    simp [add_assoc, one_add_one_eq_two]
  obtain ⟨t, ht₁, ht₂⟩ := exists_of_le_vertexCoverNum (n - 1) (ENat.le_sub_one_of_lt hh) this
  have : 1 < (Set.univ \ t).encard := by
.mp ?_ refine ENat.add_one_le_iff (by simp)
    rw [Set.encard_sdiff (by simp) (Set.finite_of_encard_eq_coe ht₁)]; rw [Set.encard_univ]
    refine ENat.le_sub_of_add_le_left (by simp [ht₁]) ?_
    refine add_le_of_le_tsub_right_of_le (Order.add_one_le_of_lt ENat.one_lt_card) ?_
    grw [ht₁, ENat.natCast_sub, hn]
    simp [add_assoc, one_add_one_eq_two, le_tsub_add]
obtain ⟨a, b, _, _, hne⟩ := Set.one_lt_encard_iff.mp this
  have := @ht₂ a b (by simp [hne])
  grind

中文:
定理 vertexCoverNum_top
  结论: vertexCoverNum (completeGraph V) = E自然数.card V - 1
  证明: by
  nontriviality V using tsub_eq_zero_of_le
  refine ENat.eq_of_forall_natCast_le_iff fun n => ⟨fun hn => ?_, fun hn => ?_⟩
  · grw [hn, vertexCoverNum_le_card_sub_one]
  by_contra! hh
  have : n - 1 <= ENat.card V := by
    grw [tsub_le_iff_right, hn]
    simp [add_assoc, one_add_one_eq_two]
  obtain ⟨t, ht₁, ht₂⟩ := exists_of_le_vertexCoverNum (n - 1) (ENat.le_sub_one_of_lt hh) this
  have : 1 < (Set.univ \ t).encard := by
.mp ?_ refine ENat.add_one_le_iff (by simp)
    rw [Set.encard_sdiff (by simp) (Set.finite_of_encard_eq_coe ht₁)]; rw [Set.encard_univ]
    refine ENat.le_sub_of_add_le_left (by simp [ht₁]) ?_
    refine add_le_of_le_tsub_right_of_le (Order.add_one_le_of_lt ENat.one_lt_card) ?_
    grw [ht₁, ENat.natCast_sub, hn]
    simp [add_assoc, one_add_one_eq_two, le_tsub_add]
obtain ⟨a, b, _, _, hne⟩ := Set.one_lt_encard_iff.mp this
  have := @ht₂ a b (by simp [hne])
  grind

Depends on / 依赖: ENat.add_one_le_iff, ENat.card, ENat.eq_of_forall_natCast_le_iff, ENat.le_sub_one_of_lt, Set.encard_sdiff, Set.finite_of_e, Set.univ, add_assoc, add_one_le_iff, encard, encard_sdiff, eq_of_forall_natCast_le_iff, exists_of_le_vertexCoverNum, finite_of_e, le_sub_one_of_lt, nontriviality, one_add_one_eq_two, tsub_eq_zero_of_le, tsub_le_iff_right, vertexCoverNum_le_card_sub_one
-/
theorem vertexCoverNum_top : vertexCoverNum (completeGraph V) = ENat.card V - 1 := by
  nontriviality V using tsub_eq_zero_of_le
  refine ENat.eq_of_forall_natCast_le_iff fun n => ⟨fun hn => ?_, fun hn => ?_⟩
  · grw [hn, vertexCoverNum_le_card_sub_one]
  by_contra! hh
  have : n - 1 <= ENat.card V := by
    grw [tsub_le_iff_right, hn]
    simp [add_assoc, one_add_one_eq_two]
  obtain ⟨t, ht₁, ht₂⟩ := exists_of_le_vertexCoverNum (n - 1) (ENat.le_sub_one_of_lt hh) this
  have : 1 < (Set.univ \ t).encard := by
.mp ?_ refine ENat.add_one_le_iff (by simp)
    rw [Set.encard_sdiff (by simp) (Set.finite_of_encard_eq_coe ht₁)]; rw [Set.encard_univ]
    refine ENat.le_sub_of_add_le_left (by simp [ht₁]) ?_
    refine add_le_of_le_tsub_right_of_le (Order.add_one_le_of_lt ENat.one_lt_card) ?_
    grw [ht₁, ENat.natCast_sub, hn]
    simp [add_assoc, one_add_one_eq_two, le_tsub_add]
obtain ⟨a, b, _, _, hne⟩ := Set.one_lt_encard_iff.mp this
  have := @ht₂ a b (by simp [hne])
  grind

/--
theorem `IsContained.vertexCoverNum_le_vertexCoverNum` / 定理 `IsContained.vertexCoverNum_le_vertexCoverNum`

English:
theorem IsContained.vertexCoverNum_le_vertexCoverNum
  given: (h : G ⊑ H)
  proof: by
  have ⟨f, hf⟩ := h
  obtain ⟨s, hs₁, hs₂⟩ := vertexCoverNum_exists H
have := H.isIndepSet_iff_isAntichain_adj.mp isIndepSet_compl_iff_isVertexCover.mpr hs₂
  have : IsAntichain G.Adj (f ⁻¹' sᶜ) := this.preimage hf (fun _ _ hadj => f.map_rel' hadj)
  have : G.IsVertexCover (f ⁻¹' s) :=
isIndepSet_compl_iff_isVertexCover.mp G.isIndepSet_iff_isAntichain_adj.mpr this
  grw [this.vertexCoverNum_le, ← hs₁]
exact Function.Embedding.encard_le .subtypeMap (by simp) Function.Embedding.mk f hf

@[deprecated IsContained.vertexCoverNum_le_vertexCoverNum (since := "2026-01-07")]

中文:
定理 IsContained.vertexCoverNum_le_vertexCoverNum
  条件: (h : G ⊑ H)
  证明: by
  have ⟨f, hf⟩ := h
  obtain ⟨s, hs₁, hs₂⟩ := vertexCoverNum_exists H
have := H.isIndepSet_iff_isAntichain_adj.mp isIndepSet_compl_iff_isVertexCover.mpr hs₂
  have : IsAntichain G.Adj (f ⁻¹' sᶜ) := this.preimage hf (fun _ _ hadj => f.map_rel' hadj)
  have : G.IsVertexCover (f ⁻¹' s) :=
isIndepSet_compl_iff_isVertexCover.mp G.isIndepSet_iff_isAntichain_adj.mpr this
  grw [this.vertexCoverNum_le, ← hs₁]
exact Function.Embedding.encard_le .subtypeMap (by simp) Function.Embedding.mk f hf

@[deprecated IsContained.vertexCoverNum_le_vertexCoverNum (since := "2026-01-07")]

Depends on / 依赖: Embedding, Function, Function.Embedding.encard_le, Function.Embedding.mk, G.Adj, G.IsVertexCover, G.isIndepSet_iff_isAntichain_adj.mpr, H.isIndepSet_iff_isAntichain_adj.mp, IsAntichain, IsVertexCover, encard_le, f.map_rel, isIndepSet_compl_iff_isVertexCover, isIndepSet_compl_iff_isVertexCover.mp, isIndepSet_compl_iff_isVertexCover.mpr, isIndepSet_iff_isAntichain_adj, map_rel, preimage, subtypeMap, this.preimage
-/
theorem IsContained.vertexCoverNum_le_vertexCoverNum (h : G ⊑ H) :
    vertexCoverNum G <= vertexCoverNum H := by
  have ⟨f, hf⟩ := h
  obtain ⟨s, hs₁, hs₂⟩ := vertexCoverNum_exists H
have := H.isIndepSet_iff_isAntichain_adj.mp isIndepSet_compl_iff_isVertexCover.mpr hs₂
  have : IsAntichain G.Adj (f ⁻¹' sᶜ) := this.preimage hf (fun _ _ hadj => f.map_rel' hadj)
  have : G.IsVertexCover (f ⁻¹' s) :=
isIndepSet_compl_iff_isVertexCover.mp G.isIndepSet_iff_isAntichain_adj.mpr this
  grw [this.vertexCoverNum_le, ← hs₁]
exact Function.Embedding.encard_le .subtypeMap (by simp) Function.Embedding.mk f hf

@[deprecated IsContained.vertexCoverNum_le_vertexCoverNum (since := "2026-01-07")]
/--
theorem `vertexCoverNum_le_vertexCoverNum_of_injective` / 定理 `vertexCoverNum_le_vertexCoverNum_of_injective`

English:
theorem vertexCoverNum_le_vertexCoverNum_of_injective
  given: (f : G ->g H) (hf : Function.Injective f)
  proof: IsContained.vertexCoverNum_le_vertexCoverNum ⟨f, hf⟩

@[gcongr]

中文:
定理 vertexCoverNum_le_vertexCoverNum_of_injective
  条件: (f : G ->g H) (hf : 函数.单射 f)
  证明: IsContained.vertexCoverNum_le_vertexCoverNum ⟨f, hf⟩

@[gcongr]

Depends on / 依赖: IsContained, IsContained.vertexCoverNum_le_vertexCoverNum, vertexCoverNum_le_vertexCoverNum
-/
theorem vertexCoverNum_le_vertexCoverNum_of_injective (f : G ->g H) (hf : Function.Injective f) :
    vertexCoverNum G <= vertexCoverNum H :=
  IsContained.vertexCoverNum_le_vertexCoverNum ⟨f, hf⟩

@[gcongr]
/--
theorem `vertexCoverNum_mono` / 定理 `vertexCoverNum_mono`

English:
theorem vertexCoverNum_mono
  given: (h : G <= G')
  statement: vertexCoverNum G <= vertexCoverNum G'
  proof: (IsContained.of_le h).vertexCoverNum_le_vertexCoverNum

中文:
定理 vertexCoverNum_mono
  条件: (h : G <= G')
  结论: vertexCoverNum G <= vertexCoverNum G'
  证明: (IsContained.of_le h).vertexCoverNum_le_vertexCoverNum

Depends on / 依赖: IsContained, IsContained.of_le, of_le, vertexCoverNum_le_vertexCoverNum
-/
theorem vertexCoverNum_mono (h : G <= G') : vertexCoverNum G <= vertexCoverNum G' :=
  (IsContained.of_le h).vertexCoverNum_le_vertexCoverNum

/--
theorem `vertexCoverNum_congr` / 定理 `vertexCoverNum_congr`

English:
theorem vertexCoverNum_congr
  given: (f : G ≃g H)
  statement: vertexCoverNum G = vertexCoverNum H
  proof: le_antisymm f.isContained.vertexCoverNum_le_vertexCoverNum
    f.symm.isContained.vertexCoverNum_le_vertexCoverNum

中文:
定理 vertexCoverNum_congr
  条件: (f : G ≃g H)
  结论: vertexCoverNum G = vertexCoverNum H
  证明: le_antisymm f.isContained.vertexCoverNum_le_vertexCoverNum
    f.symm.isContained.vertexCoverNum_le_vertexCoverNum

Depends on / 依赖: f.isContained.vertexCoverNum_le_vertexCoverNum, f.symm.isContained.vertexCoverNum_le_vertexCoverNum, isContained, le_antisymm, vertexCoverNum_le_vertexCoverNum
-/
theorem vertexCoverNum_congr (f : G ≃g H) : vertexCoverNum G = vertexCoverNum H :=
  le_antisymm f.isContained.vertexCoverNum_le_vertexCoverNum
    f.symm.isContained.vertexCoverNum_le_vertexCoverNum

end vertexCoverNum
end SimpleGraph
