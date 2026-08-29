/-
Copyright (c) 2024 Antoine Chambert-Loir, Richard Copley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, Richard Copley
-/
module

public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.GroupTheory.Complement
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Lemma of B. H. Neumann on coverings of a group by cosets.

Let the group $G$ be the union of finitely many, let us say $n$, left cosets
of subgroups $C₁$, $C₂$, ..., $Cₙ$:
$$ G = ⋃_{i = 1}^n C_i g_i. $$

* `Subgroup.exists_finiteIndex_of_leftCoset_cover`
  at least one subgroup $C_i$ has finite index in $G$.

* `Subgroup.leftCoset_cover_filter_FiniteIndex`
  the cosets of subgroups of infinite index may be omitted from the covering.

* `Subgroup.exists_index_le_card_of_leftCoset_cover` :
  the index of (at least) one of these subgroups does not exceed $n$.

* `Subgroup.one_le_sum_inv_index_of_leftCoset_cover` :
  the sum of the inverses of the indexes of the $C_i$ is greater than or equal to 1.

* `Subgroup.pairwiseDisjoint_leftCoset_cover_of_sum_inv_index_eq_one`
  If the sum of the inverses of the indexes of the subgroups $C_i$ is equal to 1,
  then the cosets of the subgroups of finite index are pairwise disjoint.

A corollary of `Subgroup.exists_finiteIndex_of_leftCoset_cover` is:

* `Subspace.biUnion_ne_univ_of_ne_top` :
  a vector space over an infinite field cannot be a finite union of proper subspaces.

This can be used to show that an algebraic extension of fields is determined by the
set of all minimal polynomials (not proved here).

[1] [Neumann-1954], *Groups Covered By Permutable Subsets*, Lemma 4.1
[2] <https://mathoverflow.net/a/17398/3332>
[3] <http://alpha.math.uga.edu/~pete/Neumann54.pdf>

-/

public section

open scoped Pointwise

namespace Subgroup

variable {G : Type*} [Group G]

section leftCoset_cover_const

@[to_additive]
/--
theorem `exists_leftTransversal_of_FiniteIndex` / 定理 `exists_leftTransversal_of_FiniteIndex`

English:
theorem exists_leftTransversal_of_FiniteIndex
  proof: by
  have ⟨t, ht⟩ := (D.subgroupOf H).exists_isComplement_left 1
  have hf : t.Finite := ht.1.finite_left_iff.mpr inferInstance
  refine ⟨hf.toFinset, hf.coe_toFinset.symm ▸ ht.1, ?_⟩
  ext x
  suffices (exists y in t, exists d in D, y * d = x) ↔ x in H by simpa using! this
  constructor
  · rintro 

中文:
定理 存在_leftTransversal_of_FiniteIndex
  证明: by
  have ⟨t, ht⟩ := (D.subgroupOf H).exists_isComplement_left 1
  have hf : t.Finite := ht.1.finite_left_iff.mpr inferInstance
  refine ⟨hf.toFinset, hf.coe_toFinset.symm ▸ ht.1, ?_⟩
  ext x
  suffices (exists y in t, exists d in D, y * d = x) ↔ x in H by simpa using! this
  constructor
  · rintro 

Depends on / 依赖: D.subgroupOf, Finite, H.mul_mem, _apply, _toMatrix, coe_toFinset, exists_isComplement_left, finite_left_iff, finite_left_iff.mpr, hD_le_H, hf.coe_toFinset.symm, hf.toFinset, inv_toLeftFun_mul_mem, mul_inv_cancel_left, mul_mem, subgroupOf, t.Finite, toFinset, toLeftFun
-/
theorem exists_leftTransversal_of_FiniteIndex
    {D H : Subgroup G} [D.FiniteIndex] (hD_le_H : D <= H) :
    exists t : Finset H,
      IsComplement (t : Set H) (D.subgroupOf H) ∧
        ⋃ g in t, (g : G) • (D : Set G) = H := by
  have ⟨t, ht⟩ := (D.subgroupOf H).exists_isComplement_left 1
  have hf : t.Finite := ht.1.finite_left_iff.mpr inferInstance
  refine ⟨hf.toFinset, hf.coe_toFinset.symm ▸ ht.1, ?_⟩
  ext x
  suffices (exists y in t, exists d in D, y * d = x) ↔ x in H by simpa using! this
  constructor
  · rintro ⟨⟨y, hy⟩, -, d, h, rfl⟩
    exact H.mul_mem hy (hD_le_H h)
  · intro hx
    exact ⟨_, (ht.1.toLeftFun ⟨x, hx⟩).2, _,
      ht.1.inv_toLeftFun_mul_mem ⟨x, hx⟩, mul_inv_cancel_left _ _⟩

variable {ι : Type*} {s : Finset ι} {H : Subgroup G} {g : ι -> G}

@[to_additive]
/--
theorem `leftCoset_cover_const_iff_surjOn` / 定理 `leftCoset_cover_const_iff_surjOn`

English:
theorem leftCoset_cover_const_iff_surjOn
  proof: by
  simp [Set.eq_univ_iff_forall, mem_leftCoset_iff, Set.SurjOn,
    QuotientGroup.forall_mk, QuotientGroup.eq]

中文:
定理 leftCoset_cover_const_iff_surjOn
  证明: by
  simp [Set.eq_univ_iff_forall, mem_leftCoset_iff, Set.SurjOn,
    QuotientGroup.forall_mk, QuotientGroup.eq]

Depends on / 依赖: Matrix, Matrix.mulVecLin_one, QuotientGroup, QuotientGroup.eq, QuotientGroup.forall_mk, Set.SurjOn, Set.eq_univ_iff_forall, SurjOn, eq_univ_iff_forall, forall_mk, mem_leftCoset_iff, mulVecLin_one
-/
theorem leftCoset_cover_const_iff_surjOn :
    ⋃ i in s, g i • (H : Set G) = Set.univ ↔ Set.SurjOn (g · : ι -> G ⧸ H) s Set.univ := by
  simp [Set.eq_univ_iff_forall, mem_leftCoset_iff, Set.SurjOn,
    QuotientGroup.forall_mk, QuotientGroup.eq]

variable (hcovers : ⋃ i in s, g i • (H : Set G) = Set.univ)
include hcovers

/-- If `H` is a subgroup of `G` and `G` is the union of a finite family of left cosets of `H`
then `H` has finite index. -/
@[to_additive]
/--
theorem `finiteIndex_of_leftCoset_cover_const` / 定理 `finiteIndex_of_leftCoset_cover_const`

English:
theorem finiteIndex_of_leftCoset_cover_const
  statement: H.FiniteIndex
  proof: by
  simp_rw [leftCoset_cover_const_iff_surjOn] at hcovers
have := Set.finite_univ_iff.mp Set.Finite.of_surjOn _ hcovers s.finite_toSet
  exact H.finiteIndex_of_finite_quotient

@[to_additive]

中文:
定理 finiteIndex_of_leftCoset_cover_const
  结论: H.FiniteIndex
  证明: by
  simp_rw [leftCoset_cover_const_iff_surjOn] at hcovers
have := Set.finite_univ_iff.mp Set.Finite.of_surjOn _ hcovers s.finite_toSet
  exact H.finiteIndex_of_finite_quotient

@[to_additive]

Depends on / 依赖: Finite, H.finiteIndex_of_finite_quotient, LinearMap, LinearMap.toMatrix, Matrix, Matrix.one_apply, Pi.single_apply, Set.Finite.of_surjOn, Set.finite_univ_iff.mp, _apply, finiteIndex_of_finite_quotient, finite_toSet, finite_univ_iff, hcovers, id_apply, leftCoset_cover_const_iff_surjOn, of_surjOn, one_apply, s.finite_toSet, simp_rw
-/
theorem finiteIndex_of_leftCoset_cover_const : H.FiniteIndex := by
  simp_rw [leftCoset_cover_const_iff_surjOn] at hcovers
have := Set.finite_univ_iff.mp Set.Finite.of_surjOn _ hcovers s.finite_toSet
  exact H.finiteIndex_of_finite_quotient

@[to_additive]
/--
theorem `index_le_of_leftCoset_cover_const` / 定理 `index_le_of_leftCoset_cover_const`

English:
theorem index_le_of_leftCoset_cover_const
  statement: H.index <= s.card
  proof: by
  cases H.index.eq_zero_or_pos with
  | inl h => exact h ▸ s.card.zero_le
  | inr h =>
    rw [leftCoset_cover_const_iff_surjOn]; rw [Set.surjOn_iff_surjective] at hcovers
    exact (Nat.card_le_card_of_surjective _ hcovers).trans_eq (Nat.card_eq_finsetCard _)

@[to_additive]

中文:
定理 index_le_of_leftCoset_cover_const
  结论: H.index <= s.card
  证明: by
  cases H.index.eq_zero_or_pos with
  | inl h => exact h ▸ s.card.zero_le
  | inr h =>
    rw [leftCoset_cover_const_iff_surjOn]; rw [Set.surjOn_iff_surjective] at hcovers
    exact (Nat.card_le_card_of_surjective _ hcovers).trans_eq (Nat.card_eq_finsetCard _)

@[to_additive]

Depends on / 依赖: H.index.eq_zero_or_pos, LinearMap, LinearMap.toMatrix, Nat.card_eq_finsetCard, Nat.card_le_card_of_surjective, Set.surjOn_iff_surjective, card_eq_finsetCard, card_le_card_of_surjective, eq_zero_or_pos, hcovers, leftCoset_cover_const_iff_surjOn, s.card.zero_le, surjOn_iff_surjective, toMatrix, trans_eq, zero_le
-/
theorem index_le_of_leftCoset_cover_const : H.index <= s.card := by
  cases H.index.eq_zero_or_pos with
  | inl h => exact h ▸ s.card.zero_le
  | inr h =>
    rw [leftCoset_cover_const_iff_surjOn]; rw [Set.surjOn_iff_surjective] at hcovers
    exact (Nat.card_le_card_of_surjective _ hcovers).trans_eq (Nat.card_eq_finsetCard _)

@[to_additive]
/--
theorem `pairwiseDisjoint_leftCoset_cover_const_of_index_eq` / 定理 `pairwiseDisjoint_leftCoset_cover_const_of_index_eq`

English:
theorem pairwiseDisjoint_leftCoset_cover_const_of_index_eq
  given: (hind : H.index = s.card)
  proof: by
  have : Fintype (G ⧸ H) := fintypeOfIndexNeZero fun h => by
    rw [hind]; rw [Finset.card_eq_zero] at h
    rw [h]; rw [← Finset.set_biUnion_coe]; rw [Finset.coe_empty]; rw [Set.biUnion_empty] at hcovers
    exact Set.empty_ne_univ hcovers
  suffices Function.Bijective (g · : s -> G ⧸ H) by
   

中文:
定理 pairwiseDisjoint_leftCoset_cover_const_of_index_eq
  条件: (hind : H.index = s.card)
  证明: by
  have : Fintype (G ⧸ H) := fintypeOfIndexNeZero fun h => by
    rw [hind]; rw [Finset.card_eq_zero] at h
    rw [h]; rw [← Finset.set_biUnion_coe]; rw [Finset.coe_empty]; rw [Set.biUnion_empty] at hcovers
    exact Set.empty_ne_univ hcovers
  suffices Function.Bijective (g · : s -> G ⧸ H) by
   

Depends on / 依赖: Bijective, Finset, Finset.card_eq_zero, Finset.coe_empty, Finset.set_biUnion_coe, Fintype, Function, Function.Bijective, Matrix, Matrix.mulVecLin_mul, QuotientGroup, QuotientGroup.eq, Set.biUnion_empty, Set.empty_ne_univ, SetLike, SetLike.mem_coe, Subtype, Subtype.mk.injEq, biUnion_empty, card_eq_zero
-/
theorem pairwiseDisjoint_leftCoset_cover_const_of_index_eq (hind : H.index = s.card) :
    Set.PairwiseDisjoint s (g · • (H : Set G)) := by
  have : Fintype (G ⧸ H) := fintypeOfIndexNeZero fun h => by
    rw [hind]; rw [Finset.card_eq_zero] at h
    rw [h]; rw [← Finset.set_biUnion_coe]; rw [Finset.coe_empty]; rw [Set.biUnion_empty] at hcovers
    exact Set.empty_ne_univ hcovers
  suffices Function.Bijective (g · : s -> G ⧸ H) by
    intro i hi j hj h' c hi' hj' x hx
    specialize hi' hx
    specialize hj' hx
    rw [mem_leftCoset_iff]; rw [SetLike.mem_coe]; rw [← QuotientGroup.eq] at hi' hj'
    rw [ne_eq]; rw [← Subtype.mk.injEq (p := (· in (s : Set ι))) i hi j hj] at h'
exact h' this.injective by simp only [hi', hj']
  rw [Fintype.bijective_iff_surjective_and_card]
  constructor
  · rwa [leftCoset_cover_const_iff_surjOn, Set.surjOn_iff_surjective] at hcovers
  · simp only [Fintype.card_coe, ← hind, index_eq_card, Nat.card_eq_fintype_card]

end leftCoset_cover_const

section

variable {ι : Type*} {H : ι -> Subgroup G} {g : ι -> G} {s : Finset ι}
    (hcovers : ⋃ i in s, (g i) • (H i : Set G) = Set.univ)
include hcovers

-- Inductive inner part of `Subgroup.exists_finiteIndex_of_leftCoset_cover`
@[to_additive]
/--
theorem `exists_finiteIndex_of_leftCoset_cover_aux` / 定理 `exists_finiteIndex_of_leftCoset_cover_aux`

English:
theorem exists_finiteIndex_of_leftCoset_cover_aux
  statement: [DecidableEq (Subgroup G)]
  proof: by
  classical
  have ⟨n, hn⟩ : exists n, n = (s.image H).card := exists_eq
  induction n using Nat.strongRec generalizing ι with
  | ind n ih =>
    -- Every left coset of `H j` is contained in a finite union of
    -- left cosets of the other subgroups `H k ≠ H j` of the covering.
    have ⟨x, hx⟩

中文:
定理 存在_finiteIndex_of_leftCoset_cover_aux
  结论: [DecidableEq (子群 G)]
  证明: by
  classical
  have ⟨n, hn⟩ : exists n, n = (s.image H).card := exists_eq
  induction n using Nat.strongRec generalizing ι with
  | ind n ih =>
    -- Every left coset of `H j` is contained in a finite union of
    -- left cosets of the other subgroups `H k ≠ H j` of the covering.
    have ⟨x, hx⟩

Depends on / 依赖: End.one_eq_id, Module, Module.End.mul_eq_comp, Nat.strongRec, _mul, classical, exists_eq, generalizing, mul_eq_comp, one_eq_id, pow_succ, s.image, strongRec
-/
theorem exists_finiteIndex_of_leftCoset_cover_aux [DecidableEq (Subgroup G)]
    (j : ι) (hj : j in s) (hcovers' : ⋃ i in s.filter (H · = H j), g i • (H i : Set G) != Set.univ) :
    exists i in s, H i != H j ∧ (H i).FiniteIndex := by
  classical
  have ⟨n, hn⟩ : exists n, n = (s.image H).card := exists_eq
  induction n using Nat.strongRec generalizing ι with
  | ind n ih =>
    -- Every left coset of `H j` is contained in a finite union of
    -- left cosets of the other subgroups `H k ≠ H j` of the covering.
    have ⟨x, hx⟩ : exists (x : G), forall i in s, H i = H j -> (g i : G ⧸ H i) != ↑x := by
      simpa [Set.eq_univ_iff_forall, mem_leftCoset_iff, ← QuotientGroup.eq] using hcovers'
    replace hx : forall (y : G), y • (H j : Set G) subseteq
        ⋃ i in s.filter (H · != H j), (y * x⁻¹ * g i) • (H i : Set G) := by
      intro y z hz
      simp_rw [Finset.mem_filter, Set.mem_iUnion]
      have ⟨i, hi, hmem⟩ : exists i in s, x * (y⁻¹ * z) in g i • (H i : Set G) := by
        simpa using Set.eq_univ_iff_forall.mp hcovers (x * (y⁻¹ * z))
      rw [mem_leftCoset_iff]; rw [SetLike.mem_coe]; rw [← QuotientGroup.eq] at hmem
      refine ⟨i, ⟨hi, fun hij => hx i hi hij ?_⟩, ?_⟩
      · rwa [hmem, eq_comm, QuotientGroup.eq, hij, inv_mul_cancel_left,
          ← SetLike.mem_coe, ← mem_leftCoset_iff]
      · simpa [mem_leftCoset_iff, SetLike.mem_coe, QuotientGroup.eq, mul_assoc] using hmem
    -- Thus `G` can also be covered by a finite union `U k, f k • K k` of left cosets
    -- of the subgroups `H k ≠ H j`.
    let κ := ↥(s.filter (H · != H j)) × Option ↥(s.filter (H · = H j))
    let f : κ -> G
    | ⟨k₁, some k₂⟩ => g k₂ * x⁻¹ * g k₁
    | ⟨k₁, none⟩ => g k₁
    let K (k : κ) : Subgroup G := H k.1.val
    have hK' (k : κ) : K k in (s.image H).erase (H j) := by
      have := Finset.mem_filter.mp k.1.property
      exact Finset.mem_erase.mpr ⟨this.2, Finset.mem_image_of_mem H this.1⟩
    have hK (k : κ) : K k != H j := ((Finset.mem_erase.mp (hK' k)).left ·)
    replace hcovers : ⋃ k in Finset.univ, f k • (K k : Set G) = Set.univ :=
        Set.iUnion₂_eq_univ_iff.mpr fun y => by
      rw [← s.filter_union_filter_not_eq (H · = H j)]; rw [Finset.set_biUnion_union] at hcovers
      cases (Set.mem_union _ _ _).mp (hcovers.superset (Set.mem_univ y)) with
      | inl hy =>
        have ⟨k, hk, hy⟩ := Set.mem_iUnion₂.mp hy
have hk' : H k = H j := And.right by simpa using hk
        have ⟨i, hi, hy⟩ := Set.mem_iUnion₂.mp (hx (g k) (hk' ▸ hy))
        exact ⟨⟨⟨i, hi⟩, some ⟨k, hk⟩⟩, Finset.mem_univ _, hy⟩
      | inr hy =>
        have ⟨i, hi, hy⟩ := Set.mem_iUnion₂.mp hy
        exact ⟨⟨⟨i, hi⟩, none⟩, Finset.mem_univ _, hy⟩
    -- Let `H k` be one of the subgroups in this covering.
    have ⟨k⟩ : Nonempty κ := not_isEmpty_iff.mp fun hempty => by
      rw [Set.iUnion_of_empty] at hcovers
      exact Set.empty_ne_univ hcovers
    -- If `G` is the union of the cosets of `H k` in the new covering, we are done.
    by_cases hcovers' : ⋃ i in Finset.filter (K · = K k) Finset.univ, f i • (K i : Set G) = Set.univ
    · rw [Set.iUnion₂_congr fun i hi => by rw [(Finset.mem_filter.mp hi).right]] at hcovers'
      exact ⟨k.1, Finset.mem_of_mem_filter k.1.1 k.1.2, hK k,
        finiteIndex_of_leftCoset_cover_const hcovers'⟩
    -- Otherwise, by the induction hypothesis, one of the subgroups `H k ≠ H j` has finite index.
    have hn' : (Finset.univ.image K).card < n := hn ▸ by
      refine ((Finset.card_le_card fun x => ?_).trans_lt <|
        Finset.card_erase_lt_of_mem (Finset.mem_image_of_mem H hj))
      rw [mem_image_univ_iff_mem_range]; rw [Set.mem_range]
      exact fun ⟨k, hk⟩ => hk ▸ hK' k
    have ⟨k', hk'⟩ := ih _ hn' hcovers k (Finset.mem_univ k) hcovers' rfl
    exact ⟨k'.1.1, Finset.mem_of_mem_filter k'.1.1 k'.1.2, hK k', hk'.2.2⟩

/-- Let the group `G` be the union of finitely many left cosets `g i • H i`.
Then at least one subgroup `H i` has finite index in `G`. -/
@[to_additive]
/--
theorem `exists_finiteIndex_of_leftCoset_cover` / 定理 `exists_finiteIndex_of_leftCoset_cover`

English:
theorem exists_finiteIndex_of_leftCoset_cover
  statement: exists k in s, (H k).FiniteIndex
  proof: by
  classical
  have ⟨j, hj⟩ : s.Nonempty := by
    by_contra! rfl
    rw [← Finset.set_biUnion_coe]; rw [Finset.coe_empty]; rw [Set.biUnion_empty] at hcovers
    exact Set.empty_ne_univ hcovers
  by_cases hcovers' : ⋃ i in s.filter (H · = H j), g i • (H i : Set G) = Set.univ
  · rw [Set.iUnion₂_co

中文:
定理 存在_finiteIndex_of_leftCoset_cover
  结论: 存在 k in s, (H k).FiniteIndex
  证明: by
  classical
  have ⟨j, hj⟩ : s.Nonempty := by
    by_contra! rfl
    rw [← Finset.set_biUnion_coe]; rw [Finset.coe_empty]; rw [Set.biUnion_empty] at hcovers
    exact Set.empty_ne_univ hcovers
  by_cases hcovers' : ⋃ i in s.filter (H · = H j), g i • (H i : Set G) = Set.univ
  · rw [Set.iUnion₂_co

Depends on / 依赖: Finset, Finset.coe_empty, Finset.mem_filter.mp, Finset.set_biUnion_coe, Matrix, Matrix.mulVecLin_submatrix, Nonempty, Set.biUnion_empty, Set.empty_ne_univ, Set.iUnion, Set.univ, biUnion_empty, classical, coe_empty, empty_ne_univ, exists_finiteIndex_of_leftCoset_cover_aux, filter, finiteIndex_of_leftCoset_cover_const, hcovers, mem_filter
-/
theorem exists_finiteIndex_of_leftCoset_cover : exists k in s, (H k).FiniteIndex := by
  classical
  have ⟨j, hj⟩ : s.Nonempty := by
    by_contra! rfl
    rw [← Finset.set_biUnion_coe]; rw [Finset.coe_empty]; rw [Set.biUnion_empty] at hcovers
    exact Set.empty_ne_univ hcovers
  by_cases hcovers' : ⋃ i in s.filter (H · = H j), g i • (H i : Set G) = Set.univ
  · rw [Set.iUnion₂_congr fun i hi => by rw [(Finset.mem_filter.mp hi).right]] at hcovers'
    exact ⟨j, hj, finiteIndex_of_leftCoset_cover_const hcovers'⟩
  · have ⟨i, hi, _, hfi⟩ :=
      exists_finiteIndex_of_leftCoset_cover_aux hcovers j hj hcovers'
    exact ⟨i, hi, hfi⟩

-- Auxiliary to `leftCoset_cover_filter_FiniteIndex` and `one_le_sum_inv_index_of_leftCoset_cover`.
@[to_additive]
/--
theorem `leftCoset_cover_filter_FiniteIndex_aux` / 定理 `leftCoset_cover_filter_FiniteIndex_aux`

English:
theorem leftCoset_cover_filter_FiniteIndex_aux
  proof: by
  classical
  let D := ⨅ k in s.filter (fun i => (H i).FiniteIndex), H k
  -- `D`, as the finite intersection of subgroups of finite index, also has finite index.
have hD : D.FiniteIndex := finiteIndex_iInf' _ by simp
  have hD_le {i} (hi : i in s) (hfi : (H i).FiniteIndex) : D <= H i :=
    iInf

中文:
定理 leftCoset_cover_filter_FiniteIndex_aux
  证明: by
  classical
  let D := ⨅ k in s.filter (fun i => (H i).FiniteIndex), H k
  -- `D`, as the finite intersection of subgroups of finite index, also has finite index.
have hD : D.FiniteIndex := finiteIndex_iInf' _ by simp
  have hD_le {i} (hi : i in s) (hfi : (H i).FiniteIndex) : D <= H i :=
    iInf

Depends on / 依赖: FiniteIndex, Matrix, Matrix.mulVecLin_reindex, classical, filter, mulVecLin_reindex, s.filter
-/
theorem leftCoset_cover_filter_FiniteIndex_aux
    [DecidablePred (FiniteIndex : Subgroup G -> Prop)] :
    (⋃ k in s.filter (fun i => (H i).FiniteIndex), g k • (H k : Set G) = Set.univ) ∧
      (1 <= ∑ i in s, ((H i).index : Rat)⁻¹) ∧
      (∑ i in s, ((H i).index : Rat)⁻¹ = 1 -> Set.PairwiseDisjoint
        (s.filter (fun i => (H i).FiniteIndex)) (fun i => g i • (H i : Set G))) := by
  classical
  let D := ⨅ k in s.filter (fun i => (H i).FiniteIndex), H k
  -- `D`, as the finite intersection of subgroups of finite index, also has finite index.
have hD : D.FiniteIndex := finiteIndex_iInf' _ by simp
  have hD_le {i} (hi : i in s) (hfi : (H i).FiniteIndex) : D <= H i :=
    iInf₂_le i (Finset.mem_filter.mpr ⟨hi, hfi⟩)
  -- Each subgroup of finite index in the covering is the union of finitely many cosets of `D`.
  choose t ht using fun i hi hfi =>
    exists_leftTransversal_of_FiniteIndex (H := H i) (hD_le hi hfi)
  -- We construct a cover of `G` by the cosets of subgroups of infinite index and of `D`.
  let κ := (i : s) × { x // x in if h : (H i.1).FiniteIndex then t i.1 i.2 h else {1} }
  let f (k : κ) : G := g k.1 * k.2.val
  let K (k : κ) : Subgroup G := if (H k.1).FiniteIndex then D else H k.1
  have hcovers' : ⋃ k in Finset.univ, f k • (K k : Set G) = Set.univ := by
    rw [← s.filter_union_filter_not_eq (fun i => (H i).FiniteIndex)] at hcovers
    rw [← hcovers]; rw [← Finset.univ.filter_union_filter_not_eq (fun k => (H k.1).FiniteIndex)]; rw [Finset.set_biUnion_union]; rw [Finset.set_biUnion_union]
    apply congrArg₂ (· union ·) <;> rw [Set.iUnion_sigma, Set.iUnion_subtype] <;>
        refine Set.iUnion_congr fun i => ?_
    · by_cases hfi : (H i).FiniteIndex <;>
        simp [← Set.smul_set_iUnion₂, Set.iUnion_subtype, ← leftCoset_assoc, f, K, ht, hfi]
    · by_cases hfi : (H i).FiniteIndex <;>
        simp [Set.iUnion_subtype, f, K, hfi]
  -- There is at least one coset of a subgroup of finite index in the original covering.
  -- Therefore a coset of `D` occurs in the new covering.
  have ⟨k, hkfi, hk⟩ : exists k, (H k.1.1).FiniteIndex ∧ K k = D :=
    have ⟨j, hj, hjfi⟩ := exists_finiteIndex_of_leftCoset_cover hcovers
    have ⟨x, hx⟩ : (t j hj hjfi).Nonempty := Finset.nonempty_coe_sort.mp
      (ht j hj hjfi).1.leftQuotientEquiv.symm.nonempty
    ⟨⟨⟨j, hj⟩, ⟨x, dif_pos hjfi ▸ hx⟩⟩, hjfi, if_pos hjfi⟩
  -- Since `D` is the unique subgroup of finite index whose cosets occur in the new covering,
  -- the cosets of the other subgroups can be omitted.
  replace hcovers' : ⋃ i in Finset.univ.filter (K · = D), f i • (D : Set G) = Set.univ := by
    rw [← hk]; rw [Set.iUnion₂_congr fun i hi => by rw [← (Finset.mem_filter.mp hi).2]]
    by_contra! h
    obtain ⟨i, -, hi⟩ :=
      exists_finiteIndex_of_leftCoset_cover_aux hcovers' k (Finset.mem_univ k) h
    by_cases hfi : (H i.1.1).FiniteIndex <;> simp [K, hfi, hkfi] at hi
  -- The result follows by restoring the original cosets of subgroups of finite index
  -- from the cosets of `D` into which they have been decomposed.
  have hHD (i) : ¬(H i).FiniteIndex -> H i != D := fun hfi hD' => (hD' ▸ hfi) hD
  have hdensity : ∑ i in s, ((H i).index : Rat)⁻¹ =
      (Finset.univ.filter (K · = D)).card * (D.index : Rat)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ (Nat.cast_ne_zero.mpr hD.index_ne_zero)]; rw [Finset.sum_mul]; rw [← Finset.sum_attach]; rw [eq_comm]; rw [Finset.card_filter]; rw [Nat.cast_sum]; rw [← Finset.univ_sigma_univ]; rw [Finset.sum_sigma]; rw [Finset.sum_coe_sort_eq_attach]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hfi : (H i).FiniteIndex
    · rw [← relIndex_mul_index (hD_le i.2 hfi), Nat.cast_mul, mul_comm,
        mul_inv_cancel_right₀ (Nat.cast_ne_zero.mpr hfi.index_ne_zero)]
      simpa [K, hfi] using! (ht i.1 i.2 hfi).1.card_left
    · rw [of_not_not (FiniteIndex.mk.mt hfi), Nat.cast_zero, inv_zero, zero_mul]
      simpa [K, hfi] using! hHD i hfi
  refine ⟨?_, ?_, ?_⟩
  · rw [← hcovers', Set.iUnion_sigma, Set.iUnion_subtype]
    refine Set.iUnion_congr fun i => ?_
    rw [Finset.mem_filter]; rw [Set.iUnion_and]
    refine Set.iUnion_congr fun hi => ?_
    by_cases hfi : (H i).FiniteIndex <;>
      simp [Set.smul_set_iUnion, Set.iUnion_subtype, ← leftCoset_assoc,
        f, K, hHD, ← (ht i hi _).2, hfi]
  · rw [hdensity]
    refine le_of_mul_le_mul_right ?_ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hD.index_ne_zero))
    rw [one_mul]; rw [mul_assoc]; rw [inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hD.index_ne_zero)]; rw [mul_one]; rw [Nat.cast_le]
    exact index_le_of_leftCoset_cover_const hcovers'
  · rw [hdensity, mul_inv_eq_one₀ (Nat.cast_ne_zero.mpr hD.index_ne_zero),
      Nat.cast_inj, Finset.coe_filter]
    intro h i hi j hj hij c hi' hj' x hx
    have hdisjoint := pairwiseDisjoint_leftCoset_cover_const_of_index_eq hcovers' h.symm
    -- We know the `f k • K k` are pairwise disjoint and need to prove that the `g i • H i` are.
    rw [Set.mem_ofPred_eq] at hi hj
    have hk' (i) (hi : i in s ∧ (H i).FiniteIndex) (hi' : c <= g i • (H i : Set G)) :
        exists (k : κ), k.1.1 = i ∧ K k = D ∧ x in f k • (D : Set G) := by
      rw [← (ht i hi.1 hi.2).2] at hi'
      suffices exists r : H i, r in t i hi.1 hi.2 ∧ x in (g i * r) • (D : Set G) by
        have ⟨r, hr, hxr⟩ := this
        refine ⟨⟨⟨i, hi.1⟩, ⟨r, dif_pos hi.2 ▸ hr⟩⟩, rfl, ?_⟩
        simpa [K, f, if_pos hi.2] using! hxr
      simpa [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, mul_assoc] using! hi' hx
    have ⟨k₁, hik₁, hk₁, hxk₁⟩ := hk' i hi hi'
    have ⟨k₂, hjk₂, hk₂, hxk₂⟩ := hk' j hj hj'
    rw [← Set.singleton_subset_iff] at hxk₁ hxk₂ ⊢
    exact hdisjoint
      (Finset.mem_filter.mpr ⟨Finset.mem_univ k₁, hk₁⟩)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ k₂, hk₂⟩)
      (ne_of_apply_ne Sigma.fst (ne_of_apply_ne Subtype.val (hik₁ ▸ hjk₂ ▸ hij)))
      hxk₁ hxk₂

/-- Let the group `G` be the union of finitely many left cosets `g i • H i`.
Then the cosets of subgroups of infinite index may be omitted from the covering. -/
@[to_additive]
/--
theorem `leftCoset_cover_filter_FiniteIndex` / 定理 `leftCoset_cover_filter_FiniteIndex`

English:
theorem leftCoset_cover_filter_FiniteIndex
  proof: (leftCoset_cover_filter_FiniteIndex_aux hcovers).1

中文:
定理 leftCoset_cover_filter_FiniteIndex
  证明: (leftCoset_cover_filter_FiniteIndex_aux hcovers).1

Depends on / 依赖: LinearMap, LinearMap.comp_apply, Matrix, Matrix.toLin, _mul, comp_apply, hcovers, leftCoset_cover_filter_FiniteIndex_aux
-/
theorem leftCoset_cover_filter_FiniteIndex
    [DecidablePred (FiniteIndex : Subgroup G -> Prop)] :
    ⋃ k in s.filter (fun i => (H i).FiniteIndex), g k • (H k : Set G) = Set.univ :=
  (leftCoset_cover_filter_FiniteIndex_aux hcovers).1

/-- Let the group `G` be the union of finitely many left cosets `g i • H i`. Then the
sum of the inverses of the indexes of the subgroups `H i` is greater than or equal to 1. -/
@[to_additive one_le_sum_inv_index_of_leftCoset_cover]
/--
theorem `one_le_sum_inv_index_of_leftCoset_cover` / 定理 `one_le_sum_inv_index_of_leftCoset_cover`

English:
theorem one_le_sum_inv_index_of_leftCoset_cover
  proof: have := Classical.decPred (FiniteIndex : Subgroup G -> Prop)
  (leftCoset_cover_filter_FiniteIndex_aux hcovers).2.1

中文:
定理 one_le_sum_inv_index_of_leftCoset_cover
  证明: have := Classical.decPred (FiniteIndex : Subgroup G -> Prop)
  (leftCoset_cover_filter_FiniteIndex_aux hcovers).2.1

Depends on / 依赖: Classical, Classical.decPred, FiniteIndex, LinearMap, LinearMap.toMatrix, Matrix, Matrix.toLin, Subgroup, _mul, _toLin, _toMatrix, decPred, f.comp, hcovers, leftCoset_cover_filter_FiniteIndex_aux, toMatrix
-/
theorem one_le_sum_inv_index_of_leftCoset_cover :
    1 <= ∑ i in s, ((H i).index : Rat)⁻¹ :=
  have := Classical.decPred (FiniteIndex : Subgroup G -> Prop)
  (leftCoset_cover_filter_FiniteIndex_aux hcovers).2.1

/-- Let the group `G` be the union of finitely many left cosets `g i • H i`.
If the sum of the inverses of the indexes of the subgroups `H i` is equal to 1,
then the cosets of the subgroups of finite index are pairwise disjoint. -/
@[to_additive]
/--
theorem `pairwiseDisjoint_leftCoset_cover_of_sum_inv_index_eq_one` / 定理 `pairwiseDisjoint_leftCoset_cover_of_sum_inv_index_eq_one`

English:
theorem pairwiseDisjoint_leftCoset_cover_of_sum_inv_index_eq_one
  proof: (leftCoset_cover_filter_FiniteIndex_aux hcovers).2.2

中文:
定理 pairwiseDisjoint_leftCoset_cover_of_sum_inv_index_eq_one
  证明: (leftCoset_cover_filter_FiniteIndex_aux hcovers).2.2

Depends on / 依赖: LinearMap, LinearMap.toMatrix, _comp, hcovers, leftCoset_cover_filter_FiniteIndex_aux, toMatrix
-/
theorem pairwiseDisjoint_leftCoset_cover_of_sum_inv_index_eq_one
    [DecidablePred (FiniteIndex : Subgroup G -> Prop)] :
    ∑ i in s, ((H i).index : Rat)⁻¹ = 1 ->
      Set.PairwiseDisjoint (s.filter (fun i => (H i).FiniteIndex))
        (fun i => g i • (H i : Set G)) :=
  (leftCoset_cover_filter_FiniteIndex_aux hcovers).2.2

/-- B. H. Neumann Lemma :
If a finite family of cosets of subgroups covers the group, then at least one
of these subgroups has index not exceeding the number of cosets. -/
@[to_additive]
/--
theorem `exists_index_le_card_of_leftCoset_cover` / 定理 `exists_index_le_card_of_leftCoset_cover`

English:
theorem exists_index_le_card_of_leftCoset_cover
  proof: by
  by_contra! h
  apply (one_le_sum_inv_index_of_leftCoset_cover hcovers).not_gt
  cases s.eq_empty_or_nonempty with
  | inl hs => simp only [hs, Finset.sum_empty, zero_lt_one]
  | inr hs =>
  have hs' : 0 < s.card := hs.card_pos
  have hlt : forall i in s, ((H i).index : Rat)⁻¹ < (s.card : Rat)⁻¹

中文:
定理 存在_index_le_card_of_leftCoset_cover
  证明: by
  by_contra! h
  apply (one_le_sum_inv_index_of_leftCoset_cover hcovers).not_gt
  cases s.eq_empty_or_nonempty with
  | inl hs => simp only [hs, Finset.sum_empty, zero_lt_one]
  | inr hs =>
  have hs' : 0 < s.card := hs.card_pos
  have hlt : forall i in s, ((H i).index : Rat)⁻¹ < (s.card : Rat)⁻¹

Depends on / 依赖: Finset, Finset.sum_empty, Module, Module.algebraMap_end_eq_smul_id, Nat.cast_pos, Nat.cast_zero, algebraMap_end_eq_smul_id, card_pos, cast_pos, cast_zero, eq_empty_or_nonempty, eq_or_ne, hcovers, hindex, hs.card_pos, inv_pos, inv_zero, not_gt, one_le_sum_inv_index_of_leftCoset_cover, s.card
-/
theorem exists_index_le_card_of_leftCoset_cover :
    exists i in s, (H i).FiniteIndex ∧ (H i).index <= s.card := by
  by_contra! h
  apply (one_le_sum_inv_index_of_leftCoset_cover hcovers).not_gt
  cases s.eq_empty_or_nonempty with
  | inl hs => simp only [hs, Finset.sum_empty, zero_lt_one]
  | inr hs =>
  have hs' : 0 < s.card := hs.card_pos
  have hlt : forall i in s, ((H i).index : Rat)⁻¹ < (s.card : Rat)⁻¹ := fun i hi => by
    cases eq_or_ne (H i).index 0 with
    | inl hindex =>
      rwa [hindex, Nat.cast_zero, inv_zero, inv_pos, Nat.cast_pos]
    | inr hindex =>
      exact inv_strictAnti₀ (by exact_mod_cast hs') (by exact_mod_cast h i hi ⟨hindex⟩)
  apply (Finset.sum_lt_sum_of_nonempty hs hlt).trans_eq
  rw [Finset.sum_const]; rw [nsmul_eq_mul]; rw [mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hs'.ne')]

end

end Subgroup

section Submodule

variable {R M ι : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {p : ι -> Submodule R M} {s : Finset ι}

/--
theorem `Submodule.exists_finiteIndex_of_cover` / 定理 `Submodule.exists_finiteIndex_of_cover`

English:
theorem Submodule.exists_finiteIndex_of_cover
  given: (hcovers : ⋃ i in s, (p i : Set M) = Set.univ)
  proof: have hcovers' : ⋃ i in s, (0 : M) +ᵥ ((p i).toAddSubgroup : Set M) = Set.univ := by
    simpa only [zero_vadd] using! hcovers
  AddSubgroup.exists_finiteIndex_of_leftCoset_cover hcovers'

中文:
定理 子模.存在_finiteIndex_of_cover
  条件: (hcovers : ⋃ i in s, (p i : 集合 M) = 集合.univ)
  证明: have hcovers' : ⋃ i in s, (0 : M) +ᵥ ((p i).toAddSubgroup : Set M) = Set.univ := by
    simpa only [zero_vadd] using! hcovers
  AddSubgroup.exists_finiteIndex_of_leftCoset_cover hcovers'

Depends on / 依赖: AddSubgroup, AddSubgroup.exists_finiteIndex_of_leftCoset_cover, Set.univ, exists_finiteIndex_of_leftCoset_cover, hcovers, toAddSubgroup, zero_vadd
-/
theorem Submodule.exists_finiteIndex_of_cover (hcovers : ⋃ i in s, (p i : Set M) = Set.univ) :
    exists k in s, (p k).toAddSubgroup.FiniteIndex :=
  have hcovers' : ⋃ i in s, (0 : M) +ᵥ ((p i).toAddSubgroup : Set M) = Set.univ := by
    simpa only [zero_vadd] using! hcovers
  AddSubgroup.exists_finiteIndex_of_leftCoset_cover hcovers'

end Submodule

section Subspace

variable {k E : Type*} [DivisionRing k] [Infinite k] [AddCommGroup E] [Module k E]
    {s : Finset (Subspace k E)}

/--
theorem `Subspace.biUnion_ne_univ_of_top_notMem` / 定理 `Subspace.biUnion_ne_univ_of_top_notMem`

English:
theorem Subspace.biUnion_ne_univ_of_top_notMem
  given: (hs : ⊤ ∉ s)
  statement: ⋃ p in s, (p : Set E) != Set.univ
  proof: by
  intro hcovers
  have ⟨p, hp, hfi⟩ := Submodule.exists_finiteIndex_of_cover hcovers
  have : Finite (E ⧸ p) := AddSubgroup.finite_quotient_of_finiteIndex
  have : Nontrivial (E ⧸ p) := Submodule.Quotient.nontrivial_iff.mpr (ne_of_mem_of_not_mem hp hs)
  have : Infinite (E ⧸ p) := Module.Free.inf

中文:
定理 子空间.biUnion_ne_univ_of_top_notMem
  条件: (hs : ⊤ ∉ s)
  结论: ⋃ p in s, (p : 集合 E) != 集合.univ
  证明: by
  intro hcovers
  have ⟨p, hp, hfi⟩ := Submodule.exists_finiteIndex_of_cover hcovers
  have : Finite (E ⧸ p) := AddSubgroup.finite_quotient_of_finiteIndex
  have : Nontrivial (E ⧸ p) := Submodule.Quotient.nontrivial_iff.mpr (ne_of_mem_of_not_mem hp hs)
  have : Infinite (E ⧸ p) := Module.Free.inf

Depends on / 依赖: AddSubgroup, AddSubgroup.finite_quotient_of_finiteIndex, Finite, Infinite, Module, Module.Free.infinite, Nontrivial, Quotient, Submodule, Submodule.Quotient.nontrivial_iff.mpr, Submodule.exists_finiteIndex_of_cover, exists_finiteIndex_of_cover, finite_quotient_of_finiteIndex, hcovers, infinite, ne_of_mem_of_not_mem, nontrivial_iff, not_finite
-/
theorem Subspace.biUnion_ne_univ_of_top_notMem (hs : ⊤ ∉ s) : ⋃ p in s, (p : Set E) != Set.univ := by
  intro hcovers
  have ⟨p, hp, hfi⟩ := Submodule.exists_finiteIndex_of_cover hcovers
  have : Finite (E ⧸ p) := AddSubgroup.finite_quotient_of_finiteIndex
  have : Nontrivial (E ⧸ p) := Submodule.Quotient.nontrivial_iff.mpr (ne_of_mem_of_not_mem hp hs)
  have : Infinite (E ⧸ p) := Module.Free.infinite k (E ⧸ p)
  exact not_finite (E ⧸ p)

/--
theorem `Subspace.top_mem_of_biUnion_eq_univ` / 定理 `Subspace.top_mem_of_biUnion_eq_univ`

English:
theorem Subspace.top_mem_of_biUnion_eq_univ
  given: (hcovers : ⋃ p in s, (p : Set E) = Set.univ)
  proof: by
  contrapose! hcovers
  exact Subspace.biUnion_ne_univ_of_top_notMem hcovers

中文:
定理 子空间.top_mem_of_biUnion_eq_univ
  条件: (hcovers : ⋃ p in s, (p : 集合 E) = 集合.univ)
  证明: by
  contrapose! hcovers
  exact Subspace.biUnion_ne_univ_of_top_notMem hcovers

Depends on / 依赖: Matrix, Matrix.toLin, Subspace, Subspace.biUnion_ne_univ_of_top_notMem, _mul_apply, _one, biUnion_ne_univ_of_top_notMem, contrapose, hcovers, id_apply, invFun, left_inv, right_inv
-/
theorem Subspace.top_mem_of_biUnion_eq_univ (hcovers : ⋃ p in s, (p : Set E) = Set.univ) :
    ⊤ in s := by
  contrapose! hcovers
  exact Subspace.biUnion_ne_univ_of_top_notMem hcovers

/--
theorem `Subspace.exists_eq_top_of_iUnion_eq_univ` / 定理 `Subspace.exists_eq_top_of_iUnion_eq_univ`

English:
theorem Subspace.exists_eq_top_of_iUnion_eq_univ
  statement: {ι} [Finite ι] {p : ι -> Subspace k E}
  proof: by
  have := Fintype.ofFinite (Set.range p)
  simp_rw [← Set.biUnion_range (f := p), ← Set.mem_toFinset] at hcovers
  apply Set.mem_toFinset.mp (Subspace.top_mem_of_biUnion_eq_univ hcovers)

中文:
定理 子空间.存在_eq_top_of_iUnion_eq_univ
  结论: {ι} [有限 ι] {p : ι -> 子空间 k E}
  证明: by
  have := Fintype.ofFinite (Set.range p)
  simp_rw [← Set.biUnion_range (f := p), ← Set.mem_toFinset] at hcovers
  apply Set.mem_toFinset.mp (Subspace.top_mem_of_biUnion_eq_univ hcovers)

Depends on / 依赖: Fintype, Fintype.ofFinite, Set.biUnion_range, Set.mem_toFinset, Set.mem_toFinset.mp, Set.range, Subspace, Subspace.top_mem_of_biUnion_eq_univ, biUnion_range, hcovers, mem_toFinset, ofFinite, simp_rw, top_mem_of_biUnion_eq_univ
-/
theorem Subspace.exists_eq_top_of_iUnion_eq_univ {ι} [Finite ι] {p : ι -> Subspace k E}
    (hcovers : ⋃ i, (p i : Set E) = Set.univ) : exists i, p i = ⊤ := by
  have := Fintype.ofFinite (Set.range p)
  simp_rw [← Set.biUnion_range (f := p), ← Set.mem_toFinset] at hcovers
  apply Set.mem_toFinset.mp (Subspace.top_mem_of_biUnion_eq_univ hcovers)

end Subspace
