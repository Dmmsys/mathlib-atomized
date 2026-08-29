/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kim Morrison
-/
module

public import Mathlib.Analysis.Convex.Combination
public import Mathlib.LinearAlgebra.AffineSpace.Independent
public import Mathlib.Tactic.FieldSimp

/-!
# Carathéodory's convexity theorem

Convex hull can be regarded as a refinement of affine span. Both are closure operators but whereas
convex hull takes values in the lattice of convex subsets, affine span takes values in the much
coarser sublattice of affine subspaces.

The cost of this refinement is that one no longer has bases. However Carathéodory's convexity
theorem offers some compensation. Given a set `s` together with a point `x` in its convex hull,
Carathéodory says that one may find an affine-independent family of elements `s` whose convex hull
contains `x`. Thus the difference from the case of affine span is that the affine-independent family
depends on `x`.

In particular, in finite dimensions Carathéodory's theorem implies that the convex hull of a set `s`
in `𝕜ᵈ` is the union of the convex hulls of the `(d + 1)`-tuples in `s`.

## Main results

* `convexHull_eq_union`: Carathéodory's convexity theorem

## Implementation details

This theorem was formalized as part of the Sphere Eversion project.

## Tags
convex hull, caratheodory

-/

@[expose] public section


open Set Finset

universe u

variable {𝕜 : Type*} {E : Type u} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E]

namespace Caratheodory

/--
theorem `mem_convexHull_erase` / 定理 `mem_convexHull_erase`

English:
theorem mem_convexHull_erase
  statement: [DecidableEq E] {t : Finset E} (h : ¬AffineIndependent 𝕜 ((↑) : t -> E))
  proof: by
  simp only [Finset.convexHull_eq, mem_ofPred_eq] at m ⊢
  obtain ⟨f, fpos, fsum, rfl⟩ := m
  obtain ⟨g, gcombo, gsum, gpos⟩ := exists_nontrivial_relation_sum_zero_of_not_affine_ind h
  replace gpos := exists_pos_of_sum_zero_of_exists_nonzero g gsum gpos
  clear h
  let s := {z in t | 0 < g z}
  

中文:
定理 mem_convexHull_erase
  结论: [DecidableEq E] {t : Finset E} (h : ¬AffineIndependent 𝕜 ((↑) : t -> E))
  证明: by
  simp only [Finset.convexHull_eq, mem_ofPred_eq] at m ⊢
  obtain ⟨f, fpos, fsum, rfl⟩ := m
  obtain ⟨g, gcombo, gsum, gpos⟩ := exists_nontrivial_relation_sum_zero_of_not_affine_ind h
  replace gpos := exists_pos_of_sum_zero_of_exists_nonzero g gsum gpos
  clear h
  let s := {z in t | 0 < g z}
  

Depends on / 依赖: Finset, Finset.convexHull_eq, convexHull_eq, exists_min_image, exists_nontrivial_relation_sum_zero_of_not_affine_ind, exists_pos_of_sum_zero_of_exists_nonzero, gcombo, mem_filter, mem_filter.mpr, mem_ofPred_eq, replace, s.exists_min_image
-/
theorem mem_convexHull_erase [DecidableEq E] {t : Finset E} (h : ¬AffineIndependent 𝕜 ((↑) : t -> E))
    {x : E} (m : x in convexHull 𝕜 (↑t : Set E)) :
    exists y : (↑t : Set E), x in convexHull 𝕜 (↑(t.erase y) : Set E) := by
  simp only [Finset.convexHull_eq, mem_ofPred_eq] at m ⊢
  obtain ⟨f, fpos, fsum, rfl⟩ := m
  obtain ⟨g, gcombo, gsum, gpos⟩ := exists_nontrivial_relation_sum_zero_of_not_affine_ind h
  replace gpos := exists_pos_of_sum_zero_of_exists_nonzero g gsum gpos
  clear h
  let s := {z in t | 0 < g z}
  obtain ⟨i₀, mem, w⟩ : exists i₀ in s, forall i in s, f i₀ / g i₀ <= f i / g i := by
    apply s.exists_min_image fun z => f z / g z
    obtain ⟨x, hx, hgx⟩ : exists x in t, 0 < g x := gpos
    exact ⟨x, mem_filter.mpr ⟨hx, hgx⟩⟩
  have hg : 0 < g i₀ := by
    rw [mem_filter] at mem
    exact mem.2
  have hi₀ : i₀ in t := filter_subset _ _ mem
  let k : E -> 𝕜 := fun z => f z - f i₀ / g i₀ * g z
  have hk : k i₀ = 0 := by simp [k, ne_of_gt hg]
  have ksum : ∑ e in t.erase i₀, k e = 1 := by
    calc
      ∑ e in t.erase i₀, k e = ∑ e in t, k e := by
        conv_rhs => rw [← insert_erase hi₀, sum_insert (notMem_erase i₀ t), hk, zero_add]
      _ = ∑ e in t, (f e - f i₀ / g i₀ * g e) := rfl
      _ = 1 := by rw [sum_sub_distrib, fsum, ← mul_sum, gsum, mul_zero, sub_zero]
  refine ⟨⟨i₀, hi₀⟩, k, ?_, by convert! ksum, ?_⟩
  · simp only [k, and_imp, sub_nonneg, mem_erase, Ne]
    intro e _ het
    by_cases hes : e in s
    · have hge : 0 < g e := by
        rw [mem_filter] at hes
        exact hes.2
      rw [← le_div_iff₀ hge]
      exact w _ hes
    · calc
        _ <= 0 := by
          apply mul_nonpos_of_nonneg_of_nonpos
          · apply div_nonneg (fpos i₀ (mem_of_subset (filter_subset _ t) mem)) (le_of_lt hg)
          · simpa only [s, mem_filter, het, true_and, not_lt] using hes
        _ <= f e := fpos e het
  · rw [Subtype.coe_mk, centerMass_eq_of_sum_1 _ id ksum]
    calc
      ∑ e in t.erase i₀, k e • e = ∑ e in t, k e • e := sum_erase _ (by rw [hk, zero_smul])
      _ = ∑ e in t, (f e - f i₀ / g i₀ * g e) • e := rfl
      _ = t.centerMass f id := by
        simp only [sub_smul, mul_smul, sum_sub_distrib, ← smul_sum, gcombo, smul_zero, sub_zero,
          centerMass, fsum, inv_one, one_smul, id]

variable {s : Set E} {x : E}

/--
Definition of `minCardFinsetOfMemConvexHull` / `minCardFinsetOfMemConvexHull` 的定义

English:
definition minCardFinsetOfMemConvexHull
  signature: (hx : x in convexHull 𝕜 s)
  body: Function.argminOn Finset.card { t | ↑t subseteq s ∧ x in convexHull 𝕜 (t : Set E) } by
    simpa only [convexHull_eq_union_convexHull_finite_subsets s, exists_prop, mem_iUnion] using! hx

中文:
定义 minCardFinsetOfMemConvexHull
  签名: (hx : x in convexHull 𝕜 s)
  定义体: Function.argminOn Finset.card { t | ↑t subseteq s ∧ x in convexHull 𝕜 (t : Set E) } by
    simpa only [convexHull_eq_union_convexHull_finite_subsets s, exists_prop, mem_iUnion] using! hx

Depends on / 依赖: Finset, Finset.card, Function, Function.argminOn, argminOn, convexHull, convexHull_eq_union_convexHull_finite_subsets, exists_prop, mem_iUnion, subseteq
-/
noncomputable def minCardFinsetOfMemConvexHull (hx : x in convexHull 𝕜 s) : Finset E :=
Function.argminOn Finset.card { t | ↑t subseteq s ∧ x in convexHull 𝕜 (t : Set E) } by
    simpa only [convexHull_eq_union_convexHull_finite_subsets s, exists_prop, mem_iUnion] using! hx

variable (hx : x in convexHull 𝕜 s)

/--
theorem `minCardFinsetOfMemConvexHull_subseteq` / 定理 `minCardFinsetOfMemConvexHull_subseteq`

English:
theorem minCardFinsetOfMemConvexHull_subseteq
  statement: ↑(minCardFinsetOfMemConvexHull hx) subseteq s
  proof: (Function.argminOn_mem _ { t : Finset E | ↑t subseteq s ∧ x in convexHull 𝕜 (t : Set E) } _).1

中文:
定理 minCardFinsetOfMemConvexHull_subseteq
  结论: ↑(minCardFinsetOfMemConvexHull hx) subseteq s
  证明: (Function.argminOn_mem _ { t : Finset E | ↑t subseteq s ∧ x in convexHull 𝕜 (t : Set E) } _).1

Depends on / 依赖: Finset, Function, Function.argminOn_mem, argminOn_mem, convexHull, subseteq
-/
theorem minCardFinsetOfMemConvexHull_subseteq : ↑(minCardFinsetOfMemConvexHull hx) subseteq s :=
  (Function.argminOn_mem _ { t : Finset E | ↑t subseteq s ∧ x in convexHull 𝕜 (t : Set E) } _).1

/--
theorem `mem_minCardFinsetOfMemConvexHull` / 定理 `mem_minCardFinsetOfMemConvexHull`

English:
theorem mem_minCardFinsetOfMemConvexHull
  proof: (Function.argminOn_mem _ { t : Finset E | ↑t subseteq s ∧ x in convexHull 𝕜 (t : Set E) } _).2

中文:
定理 mem_minCardFinsetOfMemConvexHull
  证明: (Function.argminOn_mem _ { t : Finset E | ↑t subseteq s ∧ x in convexHull 𝕜 (t : Set E) } _).2

Depends on / 依赖: Finset, Function, Function.argminOn_mem, argminOn_mem, convexHull, subseteq
-/
theorem mem_minCardFinsetOfMemConvexHull :
    x in convexHull 𝕜 (minCardFinsetOfMemConvexHull hx : Set E) :=
  (Function.argminOn_mem _ { t : Finset E | ↑t subseteq s ∧ x in convexHull 𝕜 (t : Set E) } _).2

/--
theorem `minCardFinsetOfMemConvexHull_nonempty` / 定理 `minCardFinsetOfMemConvexHull_nonempty`

English:
theorem minCardFinsetOfMemConvexHull_nonempty
  statement: (minCardFinsetOfMemConvexHull hx).Nonempty
  proof: by
  rw [← Finset.coe_nonempty]; rw [← @convexHull_nonempty_iff 𝕜]
  exact ⟨x, mem_minCardFinsetOfMemConvexHull hx⟩

中文:
定理 minCardFinsetOfMemConvexHull_nonempty
  结论: (minCardFinsetOfMemConvexHull hx).Nonempty
  证明: by
  rw [← Finset.coe_nonempty]; rw [← @convexHull_nonempty_iff 𝕜]
  exact ⟨x, mem_minCardFinsetOfMemConvexHull hx⟩

Depends on / 依赖: Finset, Finset.coe_nonempty, coe_nonempty, convexHull_nonempty_iff, mem_minCardFinsetOfMemConvexHull
-/
theorem minCardFinsetOfMemConvexHull_nonempty : (minCardFinsetOfMemConvexHull hx).Nonempty := by
  rw [← Finset.coe_nonempty]; rw [← @convexHull_nonempty_iff 𝕜]
  exact ⟨x, mem_minCardFinsetOfMemConvexHull hx⟩

/--
theorem `minCardFinsetOfMemConvexHull_card_le_card` / 定理 `minCardFinsetOfMemConvexHull_card_le_card`

English:
theorem minCardFinsetOfMemConvexHull_card_le_card
  statement: {t : Finset E} (ht₁ : ↑t subseteq s)
  proof: Function.argminOn_le _ _ (by exact ⟨ht₁, ht₂⟩)

中文:
定理 minCardFinsetOfMemConvexHull_card_le_card
  结论: {t : Finset E} (ht₁ : ↑t subseteq s)
  证明: Function.argminOn_le _ _ (by exact ⟨ht₁, ht₂⟩)

Depends on / 依赖: Function, Function.argminOn_le, argminOn_le
-/
theorem minCardFinsetOfMemConvexHull_card_le_card {t : Finset E} (ht₁ : ↑t subseteq s)
    (ht₂ : x in convexHull 𝕜 (t : Set E)) : #(minCardFinsetOfMemConvexHull hx) <= #t :=
  Function.argminOn_le _ _ (by exact ⟨ht₁, ht₂⟩)

/--
theorem `affineIndependent_minCardFinsetOfMemConvexHull` / 定理 `affineIndependent_minCardFinsetOfMemConvexHull`

English:
theorem affineIndependent_minCardFinsetOfMemConvexHull
  proof: by
  let k := #(minCardFinsetOfMemConvexHull hx) - 1
  have hk : #(minCardFinsetOfMemConvexHull hx) = k + 1 :=
    (Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr (minCardFinsetOfMemConvexHull_nonempty hx))).symm
  classical
  by_contra h
  obtain ⟨p, hp⟩ := mem_convexHull_erase h (mem_minCardFinsetOf

中文:
定理 affineIndependent_minCardFinsetOfMemConvexHull
  证明: by
  let k := #(minCardFinsetOfMemConvexHull hx) - 1
  have hk : #(minCardFinsetOfMemConvexHull hx) = k + 1 :=
    (Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr (minCardFinsetOfMemConvexHull_nonempty hx))).symm
  classical
  by_contra h
  obtain ⟨p, hp⟩ := mem_convexHull_erase h (mem_minCardFinsetOf

Depends on / 依赖: Finset, Finset.card_pos.mpr, Finset.erase_subset, Nat.succ_pred_eq_of_pos, Set.Subset.trans, Subset, card_pos, classical, contra, erase_subset, mem_convexHull_erase, mem_minCardFinsetOfMemConvexHull, minCardFinsetOfMemConvexHull, minCardFinsetOfMemConvexHull_card_le_card, minCardFinsetOfMemConvexHull_nonempty, minCardFinsetOfMemConvexHull_subseteq, succ_pred_eq_of_pos
-/
theorem affineIndependent_minCardFinsetOfMemConvexHull :
    AffineIndependent 𝕜 ((↑) : minCardFinsetOfMemConvexHull hx -> E) := by
  let k := #(minCardFinsetOfMemConvexHull hx) - 1
  have hk : #(minCardFinsetOfMemConvexHull hx) = k + 1 :=
    (Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr (minCardFinsetOfMemConvexHull_nonempty hx))).symm
  classical
  by_contra h
  obtain ⟨p, hp⟩ := mem_convexHull_erase h (mem_minCardFinsetOfMemConvexHull hx)
  have contra := minCardFinsetOfMemConvexHull_card_le_card hx (Set.Subset.trans
    (Finset.erase_subset (p : E) (minCardFinsetOfMemConvexHull hx))
    (minCardFinsetOfMemConvexHull_subseteq hx)) hp
  rw [← not_lt] at contra
  apply contra
  rw [card_erase_of_mem p.2]; rw [hk]
  exact lt_add_one _

end Caratheodory

variable {s : Set E}

/--
theorem `convexHull_eq_union` / 定理 `convexHull_eq_union`

English:
theorem convexHull_eq_union
  statement: convexHull 𝕜 s =
  proof: by
  apply Set.Subset.antisymm
  · intro x hx
    simp only [exists_prop, Set.mem_iUnion]
    exact ⟨Caratheodory.minCardFinsetOfMemConvexHull hx,
      Caratheodory.minCardFinsetOfMemConvexHull_subseteq hx,
      Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hx,
      Caratheodory.mem

中文:
定理 convexHull_eq_union
  结论: convexHull 𝕜 s =
  证明: by
  apply Set.Subset.antisymm
  · intro x hx
    simp only [exists_prop, Set.mem_iUnion]
    exact ⟨Caratheodory.minCardFinsetOfMemConvexHull hx,
      Caratheodory.minCardFinsetOfMemConvexHull_subseteq hx,
      Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hx,
      Caratheodory.mem

Depends on / 依赖: Caratheodory, Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull, Caratheodory.mem_minCardFinsetOfMemConvexHull, Caratheodory.minCardFinsetOfMemConvexHull, Caratheodory.minCardFinsetOfMemConvexHull_subseteq, Set.Subset.antisymm, Set.iUnion_subset, Set.mem_iUnion, Subset, affineIndependent_minCardFinsetOfMemConvexHull, antisymm, convert, convexHull_mono, exists_prop, iUnion_subset, iterate, mem_iUnion, mem_minCardFinsetOfMemConvexHull, minCardFinsetOfMemConvexHull, minCardFinsetOfMemConvexHull_subseteq
-/
theorem convexHull_eq_union : convexHull 𝕜 s =
    ⋃ (t : Finset E) (_ : ↑t subseteq s) (_ : AffineIndependent 𝕜 ((↑) : t -> E)), convexHull 𝕜 ↑t := by
  apply Set.Subset.antisymm
  · intro x hx
    simp only [exists_prop, Set.mem_iUnion]
    exact ⟨Caratheodory.minCardFinsetOfMemConvexHull hx,
      Caratheodory.minCardFinsetOfMemConvexHull_subseteq hx,
      Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hx,
      Caratheodory.mem_minCardFinsetOfMemConvexHull hx⟩
  · iterate 3 convert! Set.iUnion_subset _; intro
    exact convexHull_mono ‹_›

/--
theorem `eq_pos_convex_span_of_mem_convexHull` / 定理 `eq_pos_convex_span_of_mem_convexHull`

English:
theorem eq_pos_convex_span_of_mem_convexHull
  given: {x : E} (hx : x in convexHull 𝕜 s)
  proof: by
  rw [convexHull_eq_union] at hx
  simp only [exists_prop, Set.mem_iUnion] at hx
  obtain ⟨t, ht₁, ht₂, ht₃⟩ := hx
  simp only [t.convexHull_eq, Set.mem_ofPred_eq] at ht₃
  obtain ⟨w, hw₁, hw₂, hw₃⟩ := ht₃
  let t' := {i in t | w i != 0}
  refine ⟨t', t'.fintypeCoeSort, ((↑) : t' -> E), w ∘ ((↑) 

中文:
定理 eq_pos_convex_span_of_mem_convexHull
  条件: {x : E} (hx : x in convexHull 𝕜 s)
  证明: by
  rw [convexHull_eq_union] at hx
  simp only [exists_prop, Set.mem_iUnion] at hx
  obtain ⟨t, ht₁, ht₂, ht₃⟩ := hx
  simp only [t.convexHull_eq, Set.mem_ofPred_eq] at ht₃
  obtain ⟨w, hw₁, hw₂, hw₃⟩ := ht₃
  let t' := {i in t | w i != 0}
  refine ⟨t', t'.fintypeCoeSort, ((↑) : t' -> E), w ∘ ((↑) 

Depends on / 依赖: Finset, Finset.filter_subset, Set.mem_iUnion, Set.mem_ofPred_eq, Subset, Subset.trans, Subtype, Subtype.range_coe_subtype, comp_embedding, convexHull_eq, convexHull_eq_union, exists_prop, filter_subset, fintypeCoeSort, inclusion_injective, mem_iUnion, mem_ofPred_eq, range_coe_subtype, t.convexHull_eq
-/
theorem eq_pos_convex_span_of_mem_convexHull {x : E} (hx : x in convexHull 𝕜 s) :
    exists (ι : Sort (u + 1)) (_ : Fintype ι),
      exists (z : ι -> E) (w : ι -> 𝕜), Set.range z subseteq s ∧ AffineIndependent 𝕜 z ∧ (forall i, 0 < w i) ∧
        ∑ i, w i = 1 ∧ ∑ i, w i • z i = x := by
  rw [convexHull_eq_union] at hx
  simp only [exists_prop, Set.mem_iUnion] at hx
  obtain ⟨t, ht₁, ht₂, ht₃⟩ := hx
  simp only [t.convexHull_eq, Set.mem_ofPred_eq] at ht₃
  obtain ⟨w, hw₁, hw₂, hw₃⟩ := ht₃
  let t' := {i in t | w i != 0}
  refine ⟨t', t'.fintypeCoeSort, ((↑) : t' -> E), w ∘ ((↑) : t' -> E), ?_, ?_, ?_, ?_, ?_⟩
  · rw [Subtype.range_coe_subtype]
    exact Subset.trans (Finset.filter_subset _ t) ht₁
  · exact ht₂.comp_embedding ⟨_, inclusion_injective (Finset.filter_subset (fun i => w i != 0) t)⟩
  · exact fun i =>
      (hw₁ _ (Finset.mem_filter.mp i.2).1).lt_of_ne (Finset.mem_filter.mp i.property).2.symm
  · simp only [univ_eq_attach, Function.comp_apply]
    rw [Finset.sum_attach]; rw [Finset.sum_filter_ne_zero]; rw [hw₂]
  · change (∑ i in t'.attach, (fun e => w e • e) ↑i) = x
    rw [Finset.sum_attach (f := fun e => w e • e)]; rw [Finset.sum_filter_of_ne]
    · rw [t.centerMass_eq_of_sum_1 id hw₂] at hw₃
      exact hw₃
    · intro e _ hwe contra
      apply hwe
      rw [contra]; rw [zero_smul]
