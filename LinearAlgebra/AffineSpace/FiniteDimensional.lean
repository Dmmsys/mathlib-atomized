/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.AffineSpace.Basis
public import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic
public import Mathlib.LinearAlgebra.AffineSpace.Simplex.Centroid
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty

import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.RingTheory.Finiteness.Prod

/-!
# Finite-dimensional subspaces of affine spaces.

This file provides a few results relating to finite-dimensional
subspaces of affine spaces.

## Main definitions

* `Collinear` defines collinear sets of points as those that span a
  subspace of dimension at most 1.

-/

@[expose] public section


noncomputable section

open Affine
open scoped Finset

section AffineSpace'

variable (k : Type*) {V : Type*} {P : Type*}
variable {ι : Type*}

open AffineSubspace Module

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AffineSpace V P]

/--
theorem `finiteDimensional_vectorSpan_of_finite` / 定理 `finiteDimensional_vectorSpan_of_finite`

English:
theorem finiteDimensional_vectorSpan_of_finite
  given: {s : Set P} (h : Set.Finite s)
  proof: .span_of_finite k h.vsub h

中文:
定理 finiteDimensional_vectorSpan_of_finite
  条件: {s : Set P} (h : Set.Finite s)
  证明: .span_of_finite k h.vsub h

Depends on / 依赖: h.vsub, span_of_finite
-/
theorem finiteDimensional_vectorSpan_of_finite {s : Set P} (h : Set.Finite s) :
    FiniteDimensional k (vectorSpan k s) :=
.span_of_finite k h.vsub h

/--
Instance `finiteDimensional_vectorSpan_singleton` / 实例 `finiteDimensional_vectorSpan_singleton`

English:
instance finiteDimensional_vectorSpan_singleton
  signature: (p : P)
  body: finiteDimensional_vectorSpan_of_finite _ (Set.finite_singleton p)

中文:
实例 finiteDimensional_vectorSpan_singleton
  签名: (p : P)
  定义体: finiteDimensional_vectorSpan_of_finite _ (Set.finite_singleton p)

Depends on / 依赖: Set.finite_singleton, finiteDimensional_vectorSpan_of_finite, finite_singleton
-/
instance finiteDimensional_vectorSpan_singleton (p : P) :
    FiniteDimensional k (vectorSpan k {p}) :=
  finiteDimensional_vectorSpan_of_finite _ (Set.finite_singleton p)

/--
Instance `finiteDimensional_vectorSpan_range` / 实例 `finiteDimensional_vectorSpan_range`

English:
instance finiteDimensional_vectorSpan_range
  signature: [Finite ι] (p : ι -> P)
  body: finiteDimensional_vectorSpan_of_finite k (Set.finite_range _)

中文:
实例 finiteDimensional_vectorSpan_range
  签名: [Finite ι] (p : ι -> P)
  定义体: finiteDimensional_vectorSpan_of_finite k (Set.finite_range _)

Depends on / 依赖: Set.finite_range, finiteDimensional_vectorSpan_of_finite, finite_range
-/
instance finiteDimensional_vectorSpan_range [Finite ι] (p : ι -> P) :
    FiniteDimensional k (vectorSpan k (Set.range p)) :=
  finiteDimensional_vectorSpan_of_finite k (Set.finite_range _)

/--
Instance `finiteDimensional_vectorSpan_image_of_finite` / 实例 `finiteDimensional_vectorSpan_image_of_finite`

English:
instance finiteDimensional_vectorSpan_image_of_finite
  signature: [Finite ι] (p : ι -> P) (s : Set ι)
  body: finiteDimensional_vectorSpan_of_finite k (Set.toFinite _)

中文:
实例 finiteDimensional_vectorSpan_image_of_finite
  签名: [Finite ι] (p : ι -> P) (s : Set ι)
  定义体: finiteDimensional_vectorSpan_of_finite k (Set.toFinite _)

Depends on / 依赖: Set.toFinite, finiteDimensional_vectorSpan_of_finite, toFinite
-/
instance finiteDimensional_vectorSpan_image_of_finite [Finite ι] (p : ι -> P) (s : Set ι) :
    FiniteDimensional k (vectorSpan k (p '' s)) :=
  finiteDimensional_vectorSpan_of_finite k (Set.toFinite _)

/--
theorem `finiteDimensional_direction_affineSpan_of_finite` / 定理 `finiteDimensional_direction_affineSpan_of_finite`

English:
theorem finiteDimensional_direction_affineSpan_of_finite
  given: {s : Set P} (h : Set.Finite s)
  proof: (direction_affineSpan k s).symm ▸ finiteDimensional_vectorSpan_of_finite k h

中文:
定理 finiteDimensional_direction_affineSpan_of_finite
  条件: {s : Set P} (h : Set.Finite s)
  证明: (direction_affineSpan k s).symm ▸ finiteDimensional_vectorSpan_of_finite k h

Depends on / 依赖: direction_affineSpan, finiteDimensional_vectorSpan_of_finite
-/
theorem finiteDimensional_direction_affineSpan_of_finite {s : Set P} (h : Set.Finite s) :
    FiniteDimensional k (affineSpan k s).direction :=
  (direction_affineSpan k s).symm ▸ finiteDimensional_vectorSpan_of_finite k h

/--
Instance `finiteDimensional_direction_affineSpan_singleton` / 实例 `finiteDimensional_direction_affineSpan_singleton`

English:
instance finiteDimensional_direction_affineSpan_singleton
  signature: (p : P)
  body: by
  rw [direction_affineSpan]
  infer_instance

中文:
实例 finiteDimensional_direction_affineSpan_singleton
  签名: (p : P)
  定义体: by
  rw [direction_affineSpan]
  infer_instance

Depends on / 依赖: direction_affineSpan, infer_instance
-/
instance finiteDimensional_direction_affineSpan_singleton (p : P) :
    FiniteDimensional k (affineSpan k {p}).direction := by
  rw [direction_affineSpan]
  infer_instance

/--
Instance `finiteDimensional_direction_affineSpan_range` / 实例 `finiteDimensional_direction_affineSpan_range`

English:
instance finiteDimensional_direction_affineSpan_range
  signature: [Finite ι] (p : ι -> P)
  body: finiteDimensional_direction_affineSpan_of_finite k (Set.finite_range _)

中文:
实例 finiteDimensional_direction_affineSpan_range
  签名: [Finite ι] (p : ι -> P)
  定义体: finiteDimensional_direction_affineSpan_of_finite k (Set.finite_range _)

Depends on / 依赖: Set.finite_range, finiteDimensional_direction_affineSpan_of_finite, finite_range
-/
instance finiteDimensional_direction_affineSpan_range [Finite ι] (p : ι -> P) :
    FiniteDimensional k (affineSpan k (Set.range p)).direction :=
  finiteDimensional_direction_affineSpan_of_finite k (Set.finite_range _)

/--
Instance `finiteDimensional_direction_affineSpan_image_of_finite` / 实例 `finiteDimensional_direction_affineSpan_image_of_finite`

English:
instance finiteDimensional_direction_affineSpan_image_of_finite
  signature: [Finite ι] (p : ι -> P) (s : Set ι)
  body: finiteDimensional_direction_affineSpan_of_finite k (Set.toFinite _)

中文:
实例 finiteDimensional_direction_affineSpan_image_of_finite
  签名: [Finite ι] (p : ι -> P) (s : Set ι)
  定义体: finiteDimensional_direction_affineSpan_of_finite k (Set.toFinite _)

Depends on / 依赖: Set.toFinite, finiteDimensional_direction_affineSpan_of_finite, toFinite
-/
instance finiteDimensional_direction_affineSpan_image_of_finite [Finite ι] (p : ι -> P) (s : Set ι) :
    FiniteDimensional k (affineSpan k (p '' s)).direction :=
  finiteDimensional_direction_affineSpan_of_finite k (Set.toFinite _)

/--
theorem `finite_of_fin_dim_affineIndependent` / 定理 `finite_of_fin_dim_affineIndependent`

English:
theorem finite_of_fin_dim_affineIndependent
  statement: [FiniteDimensional k V] {p : ι -> P}
  proof: by
  nontriviality ι; inhabit ι
  rw [affineIndependent_iff_linearIndependent_vsub k p default] at hi
  let : IsNoetherian k V := IsNoetherian.iff_fg.2 inferInstance
  exact
    (Set.finite_singleton default).finite_of_compl (Set.finite_coe_iff.1 hi.finite_of_isNoetherian)

中文:
定理 finite_of_fin_dim_affineIndependent
  结论: [FiniteDimensional k V] {p : ι -> P}
  证明: by
  nontriviality ι; inhabit ι
  rw [affineIndependent_iff_linearIndependent_vsub k p default] at hi
  let : IsNoetherian k V := IsNoetherian.iff_fg.2 inferInstance
  exact
    (Set.finite_singleton default).finite_of_compl (Set.finite_coe_iff.1 hi.finite_of_isNoetherian)

Depends on / 依赖: IsNoetherian, IsNoetherian.iff_fg, Set.finite_coe_iff, Set.finite_singleton, affineIndependent_iff_linearIndependent_vsub, finite_coe_iff, finite_of_compl, finite_of_isNoetherian, finite_singleton, hi.finite_of_isNoetherian, iff_fg, inhabit, nontriviality
-/
theorem finite_of_fin_dim_affineIndependent [FiniteDimensional k V] {p : ι -> P}
    (hi : AffineIndependent k p) : Finite ι := by
  nontriviality ι; inhabit ι
  rw [affineIndependent_iff_linearIndependent_vsub k p default] at hi
  let : IsNoetherian k V := IsNoetherian.iff_fg.2 inferInstance
  exact
    (Set.finite_singleton default).finite_of_compl (Set.finite_coe_iff.1 hi.finite_of_isNoetherian)

/--
theorem `finite_set_of_fin_dim_affineIndependent` / 定理 `finite_set_of_fin_dim_affineIndependent`

English:
theorem finite_set_of_fin_dim_affineIndependent
  statement: [FiniteDimensional k V] {s : Set ι} {f : s -> P}
  proof: @Set.toFinite _ s (finite_of_fin_dim_affineIndependent k hi)

中文:
定理 finite_set_of_fin_dim_affineIndependent
  结论: [FiniteDimensional k V] {s : Set ι} {f : s -> P}
  证明: @Set.toFinite _ s (finite_of_fin_dim_affineIndependent k hi)

Depends on / 依赖: Set.toFinite, finite_of_fin_dim_affineIndependent, toFinite
-/
theorem finite_set_of_fin_dim_affineIndependent [FiniteDimensional k V] {s : Set ι} {f : s -> P}
    (hi : AffineIndependent k f) : s.Finite :=
  @Set.toFinite _ s (finite_of_fin_dim_affineIndependent k hi)

variable {k}

/--
Instance `AffineSubspace.finiteDimensional_sup` / 实例 `AffineSubspace.finiteDimensional_sup`

English:
instance AffineSubspace.finiteDimensional_sup
  signature: (s₁ s₂ : AffineSubspace k P)
  body: by
  rcases eq_bot_or_nonempty s₁ with rfl | ⟨p₁, hp₁⟩
  · rwa [bot_sup_eq]
  rcases eq_bot_or_nonempty s₂ with rfl | ⟨p₂, hp₂⟩
  · rwa [sup_bot_eq]
  rw [AffineSubspace.direction_sup hp₁ hp₂]
  infer_instance

中文:
实例 AffineSubspace.finiteDimensional_sup
  签名: (s₁ s₂ : AffineSubspace k P)
  定义体: by
  rcases eq_bot_or_nonempty s₁ with rfl | ⟨p₁, hp₁⟩
  · rwa [bot_sup_eq]
  rcases eq_bot_or_nonempty s₂ with rfl | ⟨p₂, hp₂⟩
  · rwa [sup_bot_eq]
  rw [AffineSubspace.direction_sup hp₁ hp₂]
  infer_instance

Depends on / 依赖: AffineSubspace, AffineSubspace.direction_sup, bot_sup_eq, direction_sup, eq_bot_or_nonempty, infer_instance, sup_bot_eq
-/
instance AffineSubspace.finiteDimensional_sup (s₁ s₂ : AffineSubspace k P)
    [FiniteDimensional k s₁.direction] [FiniteDimensional k s₂.direction] :
    FiniteDimensional k (s₁ ⊔ s₂).direction := by
  rcases eq_bot_or_nonempty s₁ with rfl | ⟨p₁, hp₁⟩
  · rwa [bot_sup_eq]
  rcases eq_bot_or_nonempty s₂ with rfl | ⟨p₂, hp₂⟩
  · rwa [sup_bot_eq]
  rw [AffineSubspace.direction_sup hp₁ hp₂]
  infer_instance

/--
Instance `finiteDimensional_direction_map` / 实例 `finiteDimensional_direction_map`

English:
instance finiteDimensional_direction_map
  signature: {V₂ P₂ : Type*} [AddCommGroup V₂] [Module k V₂]
  body: by
  rw [map_direction]
  infer_instance

中文:
实例 finiteDimensional_direction_map
  签名: {V₂ P₂ : 类型} [AddCommGroup V₂] [Module k V₂]
  定义体: by
  rw [map_direction]
  infer_instance

Depends on / 依赖: infer_instance, map_direction
-/
instance finiteDimensional_direction_map {V₂ P₂ : Type*} [AddCommGroup V₂] [Module k V₂]
    [AffineSpace V₂ P₂] (s : AffineSubspace k P) [FiniteDimensional k s.direction]
    (f : P ->ᵃ[k] P₂) : FiniteDimensional k (s.map f).direction := by
  rw [map_direction]
  infer_instance

/--
theorem `AffineIndependent.finrank_vectorSpan_image_finset` / 定理 `AffineIndependent.finrank_vectorSpan_image_finset`

English:
theorem AffineIndependent.finrank_vectorSpan_image_finset
  statement: [DecidableEq P]
  proof: by
  classical
  have hi' := hi.range.mono (Set.image_subset_range p ↑s)
  have hc' : #(s.image p) = n + 1 := by rwa [s.card_image_of_injective hi.injective]
  have hn : (s.image p).Nonempty := by simp [hc', ← Finset.card_pos]
  rcases hn with ⟨p₁, hp₁⟩
  have hp₁' : p₁ in p '' s := by simpa using h

中文:
定理 AffineIndependent.finrank_vectorSpan_image_finset
  结论: [DecidableEq P]
  证明: by
  classical
  have hi' := hi.range.mono (Set.image_subset_range p ↑s)
  have hc' : #(s.image p) = n + 1 := by rwa [s.card_image_of_injective hi.injective]
  have hn : (s.image p).Nonempty := by simp [hc', ← Finset.card_pos]
  rcases hn with ⟨p₁, hp₁⟩
  have hp₁' : p₁ in p '' s := by simpa using h

Depends on / 依赖: Finset, Finset.card_pos, Finset.coe_image, Finset.coe_sdiff, Finset.coe_singleton, Finset.sdiff_singleton_eq_erase, Nonempty, Set.image_subset_range, affineIndependent_set_iff_linearIndependent_vsub, card_image_of_injective, card_pos, classical, coe_image, coe_sdiff, coe_singleton, hi.injective, hi.range.mono, image_subset_range, injective, s.card_image_of_injective
-/
theorem AffineIndependent.finrank_vectorSpan_image_finset [DecidableEq P]
    {p : ι -> P} (hi : AffineIndependent k p) {s : Finset ι} {n : Nat} (hc : #s = n + 1) :
    finrank k (vectorSpan k (s.image p : Set P)) = n := by
  classical
  have hi' := hi.range.mono (Set.image_subset_range p ↑s)
  have hc' : #(s.image p) = n + 1 := by rwa [s.card_image_of_injective hi.injective]
  have hn : (s.image p).Nonempty := by simp [hc', ← Finset.card_pos]
  rcases hn with ⟨p₁, hp₁⟩
  have hp₁' : p₁ in p '' s := by simpa using hp₁
  rw [affineIndependent_set_iff_linearIndependent_vsub k hp₁']; rw [← Finset.coe_singleton]; rw [← Finset.coe_image]; rw [← Finset.coe_sdiff]; rw [Finset.sdiff_singleton_eq_erase]; rw [← Finset.coe_image]
    at hi'
  have hc : #(((s.image p).erase p₁).image (· -ᵥ p₁)) = n := by
    rw [Finset.card_image_of_injective _ (vsub_left_injective _)]; rw [Finset.card_erase_of_mem hp₁]
    exact Nat.pred_eq_of_eq_succ hc'
  rwa [vectorSpan_eq_span_vsub_finset_right_ne k hp₁, finrank_span_finset_eq_card, hc]

/--
theorem `AffineIndependent.finrank_vectorSpan` / 定理 `AffineIndependent.finrank_vectorSpan`

English:
theorem AffineIndependent.finrank_vectorSpan
  statement: [Fintype ι] {p : ι -> P} (hi : AffineIndependent k p)
  proof: by
  classical
  rw [← Finset.card_univ] at hc
  rw [← Set.image_univ]; rw [← Finset.coe_univ]; rw [← Finset.coe_image]
  exact hi.finrank_vectorSpan_image_finset hc

中文:
定理 AffineIndependent.finrank_vectorSpan
  结论: [Fintype ι] {p : ι -> P} (hi : AffineIndependent k p)
  证明: by
  classical
  rw [← Finset.card_univ] at hc
  rw [← Set.image_univ]; rw [← Finset.coe_univ]; rw [← Finset.coe_image]
  exact hi.finrank_vectorSpan_image_finset hc

Depends on / 依赖: Finset, Finset.card_univ, Finset.coe_image, Finset.coe_univ, Set.image_univ, card_univ, classical, coe_image, coe_univ, finrank_vectorSpan_image_finset, hi.finrank_vectorSpan_image_finset, image_univ
-/
theorem AffineIndependent.finrank_vectorSpan [Fintype ι] {p : ι -> P} (hi : AffineIndependent k p)
    {n : Nat} (hc : Fintype.card ι = n + 1) : finrank k (vectorSpan k (Set.range p)) = n := by
  classical
  rw [← Finset.card_univ] at hc
  rw [← Set.image_univ]; rw [← Finset.coe_univ]; rw [← Finset.coe_image]
  exact hi.finrank_vectorSpan_image_finset hc

/--
lemma `AffineIndependent.finrank_vectorSpan_add_one` / 引理 `AffineIndependent.finrank_vectorSpan_add_one`

English:
lemma AffineIndependent.finrank_vectorSpan_add_one
  statement: [Fintype ι] [Nonempty ι] {p : ι -> P}
  proof: by
  rw [hi.finrank_vectorSpan (tsub_add_cancel_of_le _).symm]; rw [tsub_add_cancel_of_le] <;>
    exact Fintype.card_pos

中文:
引理 AffineIndependent.finrank_vectorSpan_add_one
  结论: [Fintype ι] [Nonempty ι] {p : ι -> P}
  证明: by
  rw [hi.finrank_vectorSpan (tsub_add_cancel_of_le _).symm]; rw [tsub_add_cancel_of_le] <;>
    exact Fintype.card_pos

Depends on / 依赖: Fintype, Fintype.card_pos, card_pos, finrank_vectorSpan, hi.finrank_vectorSpan, tsub_add_cancel_of_le
-/
lemma AffineIndependent.finrank_vectorSpan_add_one [Fintype ι] [Nonempty ι] {p : ι -> P}
    (hi : AffineIndependent k p) : finrank k (vectorSpan k (Set.range p)) + 1 = Fintype.card ι := by
  rw [hi.finrank_vectorSpan (tsub_add_cancel_of_le _).symm]; rw [tsub_add_cancel_of_le] <;>
    exact Fintype.card_pos

/--
theorem `AffineIndependent.vectorSpan_eq_top_of_card_eq_finrank_add_one` / 定理 `AffineIndependent.vectorSpan_eq_top_of_card_eq_finrank_add_one`

English:
theorem AffineIndependent.vectorSpan_eq_top_of_card_eq_finrank_add_one
  statement: [FiniteDimensional k V]
  proof: Submodule.eq_top_of_finrank_eq hi.finrank_vectorSpan hc

中文:
定理 AffineIndependent.vectorSpan_eq_top_of_card_eq_finrank_add_one
  结论: [FiniteDimensional k V]
  证明: Submodule.eq_top_of_finrank_eq hi.finrank_vectorSpan hc

Depends on / 依赖: Submodule, Submodule.eq_top_of_finrank_eq, eq_top_of_finrank_eq, finrank_vectorSpan, hi.finrank_vectorSpan
-/
theorem AffineIndependent.vectorSpan_eq_top_of_card_eq_finrank_add_one [FiniteDimensional k V]
    [Fintype ι] {p : ι -> P} (hi : AffineIndependent k p) (hc : Fintype.card ι = finrank k V + 1) :
    vectorSpan k (Set.range p) = ⊤ :=
Submodule.eq_top_of_finrank_eq hi.finrank_vectorSpan hc

variable (k)

/--
theorem `finrank_vectorSpan_image_finset_le` / 定理 `finrank_vectorSpan_image_finset_le`

English:
theorem finrank_vectorSpan_image_finset_le
  statement: [DecidableEq P] (p : ι -> P) (s : Finset ι) {n : Nat}
  proof: by
  classical
  have hn : (s.image p).Nonempty := by
    rw [Finset.image_nonempty]; rw [← Finset.card_pos]; rw [hc]
    apply Nat.succ_pos
  rcases hn with ⟨p₁, hp₁⟩
  rw [vectorSpan_eq_span_vsub_finset_right_ne k hp₁]
  refine le_trans (finrank_span_finset_le_card (((s.image p).erase p₁).image fu

中文:
定理 finrank_vectorSpan_image_finset_le
  结论: [DecidableEq P] (p : ι -> P) (s : Finset ι) {n : 自然数}
  证明: by
  classical
  have hn : (s.image p).Nonempty := by
    rw [Finset.image_nonempty]; rw [← Finset.card_pos]; rw [hc]
    apply Nat.succ_pos
  rcases hn with ⟨p₁, hp₁⟩
  rw [vectorSpan_eq_span_vsub_finset_right_ne k hp₁]
  refine le_trans (finrank_span_finset_le_card (((s.image p).erase p₁).image fu

Depends on / 依赖: Finset, Finset.card_erase_of_mem, Finset.card_image_le, Finset.card_image_of_injective, Finset.card_pos, Finset.image_nonempty, Nat.succ_pos, Nonempty, card_erase_of_mem, card_image_le, card_image_of_injective, card_pos, classical, finrank_span_finset_le_card, image_nonempty, le_trans, s.image, succ_pos, tsub_le_iff_right, vectorSpan_eq_span_vsub_finset_right_ne
-/
theorem finrank_vectorSpan_image_finset_le [DecidableEq P] (p : ι -> P) (s : Finset ι) {n : Nat}
    (hc : #s = n + 1) : finrank k (vectorSpan k (s.image p : Set P)) <= n := by
  classical
  have hn : (s.image p).Nonempty := by
    rw [Finset.image_nonempty]; rw [← Finset.card_pos]; rw [hc]
    apply Nat.succ_pos
  rcases hn with ⟨p₁, hp₁⟩
  rw [vectorSpan_eq_span_vsub_finset_right_ne k hp₁]
  refine le_trans (finrank_span_finset_le_card (((s.image p).erase p₁).image fun p => p -ᵥ p₁)) ?_
  rw [Finset.card_image_of_injective _ (vsub_left_injective p₁)]; rw [Finset.card_erase_of_mem hp₁]; rw [tsub_le_iff_right]; rw [← hc]
  apply Finset.card_image_le

/--
theorem `finrank_vectorSpan_range_le` / 定理 `finrank_vectorSpan_range_le`

English:
theorem finrank_vectorSpan_range_le
  given: [Fintype ι] (p : ι -> P) {n : Nat} (hc : Fintype.card ι = n + 1)
  proof: by
  classical
  rw [← Set.image_univ]; rw [← Finset.coe_univ]; rw [← Finset.coe_image]
  rw [← Finset.card_univ] at hc
  exact finrank_vectorSpan_image_finset_le _ _ _ hc

中文:
定理 finrank_vectorSpan_range_le
  条件: [Fintype ι] (p : ι -> P) {n : 自然数} (hc : Fintype.card ι = n + 1)
  证明: by
  classical
  rw [← Set.image_univ]; rw [← Finset.coe_univ]; rw [← Finset.coe_image]
  rw [← Finset.card_univ] at hc
  exact finrank_vectorSpan_image_finset_le _ _ _ hc

Depends on / 依赖: Finset, Finset.card_univ, Finset.coe_image, Finset.coe_univ, Set.image_univ, card_univ, classical, coe_image, coe_univ, finrank_vectorSpan_image_finset_le, image_univ
-/
theorem finrank_vectorSpan_range_le [Fintype ι] (p : ι -> P) {n : Nat} (hc : Fintype.card ι = n + 1) :
    finrank k (vectorSpan k (Set.range p)) <= n := by
  classical
  rw [← Set.image_univ]; rw [← Finset.coe_univ]; rw [← Finset.coe_image]
  rw [← Finset.card_univ] at hc
  exact finrank_vectorSpan_image_finset_le _ _ _ hc

/--
lemma `finrank_vectorSpan_range_add_one_le` / 引理 `finrank_vectorSpan_range_add_one_le`

English:
lemma finrank_vectorSpan_range_add_one_le
  given: [Fintype ι] [Nonempty ι] (p : ι -> P)
  proof: (le_tsub_iff_right <| Nat.succ_le_iff.2 Fintype.card_pos).1 finrank_vectorSpan_range_le _ _
    (tsub_add_cancel_of_le <| Nat.succ_le_iff.2 Fintype.card_pos).symm

中文:
引理 finrank_vectorSpan_range_add_one_le
  条件: [Fintype ι] [Nonempty ι] (p : ι -> P)
  证明: (le_tsub_iff_right <| Nat.succ_le_iff.2 Fintype.card_pos).1 finrank_vectorSpan_range_le _ _
    (tsub_add_cancel_of_le <| Nat.succ_le_iff.2 Fintype.card_pos).symm

Depends on / 依赖: Fintype, Fintype.card_pos, Nat.succ_le_iff, card_pos, finrank_vectorSpan_range_le, le_tsub_iff_right, succ_le_iff, tsub_add_cancel_of_le
-/
lemma finrank_vectorSpan_range_add_one_le [Fintype ι] [Nonempty ι] (p : ι -> P) :
    finrank k (vectorSpan k (Set.range p)) + 1 <= Fintype.card ι :=
(le_tsub_iff_right <| Nat.succ_le_iff.2 Fintype.card_pos).1 finrank_vectorSpan_range_le _ _
    (tsub_add_cancel_of_le <| Nat.succ_le_iff.2 Fintype.card_pos).symm

/--
theorem `affineIndependent_iff_finrank_vectorSpan_eq` / 定理 `affineIndependent_iff_finrank_vectorSpan_eq`

English:
theorem affineIndependent_iff_finrank_vectorSpan_eq
  statement: [Fintype ι] (p : ι -> P) {n : Nat}
  proof: by
  classical
  have hn : Nonempty ι := by simp [← Fintype.card_pos_iff, hc]
  obtain ⟨i₁⟩ := hn
  rw [affineIndependent_iff_linearIndependent_vsub _ _ i₁]; rw [linearIndependent_iff_card_eq_finrank_span]; rw [eq_comm]; rw [vectorSpan_range_eq_span_range_vsub_right_ne k p i₁]; rw [Set.finrank]
  rw

中文:
定理 affineIndependent_iff_finrank_vectorSpan_eq
  结论: [Fintype ι] (p : ι -> P) {n : 自然数}
  证明: by
  classical
  have hn : Nonempty ι := by simp [← Fintype.card_pos_iff, hc]
  obtain ⟨i₁⟩ := hn
  rw [affineIndependent_iff_linearIndependent_vsub _ _ i₁]; rw [linearIndependent_iff_card_eq_finrank_span]; rw [eq_comm]; rw [vectorSpan_range_eq_span_range_vsub_right_ne k p i₁]; rw [Set.finrank]
  rw

Depends on / 依赖: Finset, Finset.card_erase_of_mem, Finset.card_univ, Finset.filter_ne, Fintype, Fintype.card_pos_iff, Fintype.subtype_card, Nonempty, Set.finrank, affineIndependent_iff_linearIndependent_vsub, card_erase_of_mem, card_pos_iff, card_univ, classical, eq_comm, filter_ne, finrank, linearIndependent_iff_card_eq_finrank_span, subtype_card, vectorSpan_range_eq_span_range_vsub_right_ne
-/
theorem affineIndependent_iff_finrank_vectorSpan_eq [Fintype ι] (p : ι -> P) {n : Nat}
    (hc : Fintype.card ι = n + 1) :
    AffineIndependent k p ↔ finrank k (vectorSpan k (Set.range p)) = n := by
  classical
  have hn : Nonempty ι := by simp [← Fintype.card_pos_iff, hc]
  obtain ⟨i₁⟩ := hn
  rw [affineIndependent_iff_linearIndependent_vsub _ _ i₁]; rw [linearIndependent_iff_card_eq_finrank_span]; rw [eq_comm]; rw [vectorSpan_range_eq_span_range_vsub_right_ne k p i₁]; rw [Set.finrank]
  rw [← Finset.card_univ] at hc
  rw [Fintype.subtype_card]
  simp [Finset.filter_ne', Finset.card_erase_of_mem, hc]

/--
theorem `affineIndependent_iff_le_finrank_vectorSpan` / 定理 `affineIndependent_iff_le_finrank_vectorSpan`

English:
theorem affineIndependent_iff_le_finrank_vectorSpan
  statement: [Fintype ι] (p : ι -> P) {n : Nat}
  proof: by
  rw [affineIndependent_iff_finrank_vectorSpan_eq k p hc]
  constructor
  · rintro rfl
    rfl
  · exact fun hle => le_antisymm (finrank_vectorSpan_range_le k p hc) hle

中文:
定理 affineIndependent_iff_le_finrank_vectorSpan
  结论: [Fintype ι] (p : ι -> P) {n : 自然数}
  证明: by
  rw [affineIndependent_iff_finrank_vectorSpan_eq k p hc]
  constructor
  · rintro rfl
    rfl
  · exact fun hle => le_antisymm (finrank_vectorSpan_range_le k p hc) hle

Depends on / 依赖: affineIndependent_iff_finrank_vectorSpan_eq, finrank_vectorSpan_range_le, le_antisymm
-/
theorem affineIndependent_iff_le_finrank_vectorSpan [Fintype ι] (p : ι -> P) {n : Nat}
    (hc : Fintype.card ι = n + 1) :
    AffineIndependent k p ↔ n <= finrank k (vectorSpan k (Set.range p)) := by
  rw [affineIndependent_iff_finrank_vectorSpan_eq k p hc]
  constructor
  · rintro rfl
    rfl
  · exact fun hle => le_antisymm (finrank_vectorSpan_range_le k p hc) hle

/--
theorem `affineIndependent_iff_not_finrank_vectorSpan_le` / 定理 `affineIndependent_iff_not_finrank_vectorSpan_le`

English:
theorem affineIndependent_iff_not_finrank_vectorSpan_le
  statement: [Fintype ι] (p : ι -> P) {n : Nat}
  proof: by
  rw [affineIndependent_iff_le_finrank_vectorSpan k p hc]; rw [← Nat.lt_iff_add_one_le]; rw [lt_iff_not_ge]

中文:
定理 affineIndependent_iff_not_finrank_vectorSpan_le
  结论: [Fintype ι] (p : ι -> P) {n : 自然数}
  证明: by
  rw [affineIndependent_iff_le_finrank_vectorSpan k p hc]; rw [← Nat.lt_iff_add_one_le]; rw [lt_iff_not_ge]

Depends on / 依赖: Nat.lt_iff_add_one_le, affineIndependent_iff_le_finrank_vectorSpan, lt_iff_add_one_le, lt_iff_not_ge
-/
theorem affineIndependent_iff_not_finrank_vectorSpan_le [Fintype ι] (p : ι -> P) {n : Nat}
    (hc : Fintype.card ι = n + 2) :
    AffineIndependent k p ↔ ¬finrank k (vectorSpan k (Set.range p)) <= n := by
  rw [affineIndependent_iff_le_finrank_vectorSpan k p hc]; rw [← Nat.lt_iff_add_one_le]; rw [lt_iff_not_ge]

/--
theorem `finrank_vectorSpan_le_iff_not_affineIndependent` / 定理 `finrank_vectorSpan_le_iff_not_affineIndependent`

English:
theorem finrank_vectorSpan_le_iff_not_affineIndependent
  statement: [Fintype ι] (p : ι -> P) {n : Nat}
  proof: (not_iff_comm.1 (affineIndependent_iff_not_finrank_vectorSpan_le k p hc).symm).symm

中文:
定理 finrank_vectorSpan_le_iff_not_affineIndependent
  结论: [Fintype ι] (p : ι -> P) {n : 自然数}
  证明: (not_iff_comm.1 (affineIndependent_iff_not_finrank_vectorSpan_le k p hc).symm).symm

Depends on / 依赖: affineIndependent_iff_not_finrank_vectorSpan_le, not_iff_comm
-/
theorem finrank_vectorSpan_le_iff_not_affineIndependent [Fintype ι] (p : ι -> P) {n : Nat}
    (hc : Fintype.card ι = n + 2) :
    finrank k (vectorSpan k (Set.range p)) <= n ↔ ¬AffineIndependent k p :=
  (not_iff_comm.1 (affineIndependent_iff_not_finrank_vectorSpan_le k p hc).symm).symm

variable {k}

/--
lemma `AffineIndependent.card_le_finrank_succ` / 引理 `AffineIndependent.card_le_finrank_succ`

English:
lemma AffineIndependent.card_le_finrank_succ
  given: [Fintype ι] {p : ι -> P} (hp : AffineIndependent k p)
  proof: by
  cases isEmpty_or_nonempty ι
  · simp [Fintype.card_eq_zero]
  rw [← tsub_le_iff_right]
  exact (affineIndependent_iff_le_finrank_vectorSpan _ _
    (tsub_add_cancel_of_le <| Nat.one_le_iff_ne_zero.2 Fintype.card_ne_zero).symm).1 hp

中文:
引理 AffineIndependent.card_le_finrank_succ
  条件: [Fintype ι] {p : ι -> P} (hp : AffineIndependent k p)
  证明: by
  cases isEmpty_or_nonempty ι
  · simp [Fintype.card_eq_zero]
  rw [← tsub_le_iff_right]
  exact (affineIndependent_iff_le_finrank_vectorSpan _ _
    (tsub_add_cancel_of_le <| Nat.one_le_iff_ne_zero.2 Fintype.card_ne_zero).symm).1 hp

Depends on / 依赖: Fintype, Fintype.card_eq_zero, Fintype.card_ne_zero, Nat.one_le_iff_ne_zero, affineIndependent_iff_le_finrank_vectorSpan, card_eq_zero, card_ne_zero, isEmpty_or_nonempty, one_le_iff_ne_zero, tsub_add_cancel_of_le, tsub_le_iff_right
-/
lemma AffineIndependent.card_le_finrank_succ [Fintype ι] {p : ι -> P} (hp : AffineIndependent k p) :
    Fintype.card ι <= Module.finrank k (vectorSpan k (Set.range p)) + 1 := by
  cases isEmpty_or_nonempty ι
  · simp [Fintype.card_eq_zero]
  rw [← tsub_le_iff_right]
  exact (affineIndependent_iff_le_finrank_vectorSpan _ _
    (tsub_add_cancel_of_le <| Nat.one_le_iff_ne_zero.2 Fintype.card_ne_zero).symm).1 hp

open Finset in
/--
lemma `AffineIndependent.card_le_card_of_subset_affineSpan` / 引理 `AffineIndependent.card_le_card_of_subset_affineSpan`

English:
lemma AffineIndependent.card_le_card_of_subset_affineSpan
  statement: {s t : Finset V}
  proof: by
  obtain rfl | hs' := s.eq_empty_or_nonempty
  · simp
  obtain rfl | ht' := t.eq_empty_or_nonempty
  · simpa [Set.subset_empty_iff] using hst
  have := hs'.to_subtype
  have := ht'.to_set.to_subtype
  have direction_le := AffineSubspace.direction_le (affineSpan_mono k hst)
  rw [AffineSubspace.af

中文:
引理 AffineIndependent.card_le_card_of_subset_affineSpan
  结论: {s t : Finset V}
  证明: by
  obtain rfl | hs' := s.eq_empty_or_nonempty
  · simp
  obtain rfl | ht' := t.eq_empty_or_nonempty
  · simpa [Set.subset_empty_iff] using hst
  have := hs'.to_subtype
  have := ht'.to_set.to_subtype
  have direction_le := AffineSubspace.direction_le (affineSpan_mono k hst)
  rw [AffineSubspace.af

Depends on / 依赖: AffineSubspace, AffineSubspace.affineSpan_coe, AffineSubspace.direction_le, Set.subset_empty_iff, Submodule, Submodule.finr, Subtype, Subtype.range_coe, add_le_add_left, affineSpan_coe, affineSpan_mono, direction_affineSpan, direction_le, eq_empty_or_nonempty, finrank_le, range_coe, s.eq_empty_or_nonempty, subset_empty_iff, t.eq_empty_or_nonempty, to_set
-/
lemma AffineIndependent.card_le_card_of_subset_affineSpan {s t : Finset V}
    (hs : AffineIndependent k ((↑) : s -> V)) (hst : (s : Set V) subseteq affineSpan k (t : Set V)) :
    #s <= #t := by
  obtain rfl | hs' := s.eq_empty_or_nonempty
  · simp
  obtain rfl | ht' := t.eq_empty_or_nonempty
  · simpa [Set.subset_empty_iff] using hst
  have := hs'.to_subtype
  have := ht'.to_set.to_subtype
  have direction_le := AffineSubspace.direction_le (affineSpan_mono k hst)
  rw [AffineSubspace.affineSpan_coe]; rw [direction_affineSpan]; rw [direction_affineSpan]; rw [← @Subtype.range_coe _ (s : Set V)]; rw [← @Subtype.range_coe _ (t : Set V)] at direction_le
  have finrank_le := add_le_add_left (Submodule.finrank_mono direction_le) 1
  -- We use `erw` to elide the difference between `↥s` and `↥(s : Set V)}`
  erw [hs.finrank_vectorSpan_add_one] at finrank_le
simpa using finrank_le.trans finrank_vectorSpan_range_add_one_le _ _

open Finset in
/--
lemma `AffineIndependent.card_lt_card_of_affineSpan_lt_affineSpan` / 引理 `AffineIndependent.card_lt_card_of_affineSpan_lt_affineSpan`

English:
lemma AffineIndependent.card_lt_card_of_affineSpan_lt_affineSpan
  statement: {s t : Finset V}
  proof: by
  obtain rfl | hs' := s.eq_empty_or_nonempty
  · simpa [card_pos] using hst
  obtain rfl | ht' := t.eq_empty_or_nonempty
  · simp at hst
  have := hs'.to_subtype
  have := ht'.to_set.to_subtype
have dir_lt := AffineSubspace.direction_lt_of_nonempty (k := k) hst hs'.to_set.affineSpan k
  rw [direc

中文:
引理 AffineIndependent.card_lt_card_of_affineSpan_lt_affineSpan
  结论: {s t : Finset V}
  证明: by
  obtain rfl | hs' := s.eq_empty_or_nonempty
  · simpa [card_pos] using hst
  obtain rfl | ht' := t.eq_empty_or_nonempty
  · simp at hst
  have := hs'.to_subtype
  have := ht'.to_set.to_subtype
have dir_lt := AffineSubspace.direction_lt_of_nonempty (k := k) hst hs'.to_set.affineSpan k
  rw [direc

Depends on / 依赖: AffineSubspace, AffineSubspace.direction_lt_of_nonempty, Submodule, Submodule.finrank_lt_finrank_of_lt, Subtype, Subtype.range_coe, add_lt_add_left, affineSpan, card_pos, dir_lt, direction_affineSpan, direction_lt_of_nonempty, eq_empty_or_nonempty, finrank_lt, finrank_lt_finrank_of_lt, range_coe, s.eq_empty_or_nonempty, t.eq_empty_or_nonempty, to_set, to_set.affineSpan
-/
lemma AffineIndependent.card_lt_card_of_affineSpan_lt_affineSpan {s t : Finset V}
    (hs : AffineIndependent k ((↑) : s -> V))
    (hst : affineSpan k (s : Set V) < affineSpan k (t : Set V)) : #s < #t := by
  obtain rfl | hs' := s.eq_empty_or_nonempty
  · simpa [card_pos] using hst
  obtain rfl | ht' := t.eq_empty_or_nonempty
  · simp at hst
  have := hs'.to_subtype
  have := ht'.to_set.to_subtype
have dir_lt := AffineSubspace.direction_lt_of_nonempty (k := k) hst hs'.to_set.affineSpan k
  rw [direction_affineSpan]; rw [direction_affineSpan]; rw [← @Subtype.range_coe _ (s : Set V)]; rw [← @Subtype.range_coe _ (t : Set V)] at dir_lt
  have finrank_lt := add_lt_add_left (Submodule.finrank_lt_finrank_of_lt dir_lt) 1
  -- We use `erw` to elide the difference between `↥s` and `↥(s : Set V)}`
  erw [hs.finrank_vectorSpan_add_one] at finrank_lt
simpa using finrank_lt.trans_le finrank_vectorSpan_range_add_one_le _ _

/--
theorem `AffineIndependent.vectorSpan_image_finset_eq_of_le_of_card_eq_finrank_add_one` / 定理 `AffineIndependent.vectorSpan_image_finset_eq_of_le_of_card_eq_finrank_add_one`

English:
theorem AffineIndependent.vectorSpan_image_finset_eq_of_le_of_card_eq_finrank_add_one
  proof: Submodule.eq_of_le_of_finrank_eq hle hi.finrank_vectorSpan_image_finset hc

中文:
定理 AffineIndependent.vectorSpan_image_finset_eq_of_le_of_card_eq_finrank_add_one
  证明: Submodule.eq_of_le_of_finrank_eq hle hi.finrank_vectorSpan_image_finset hc

Depends on / 依赖: Submodule, Submodule.eq_of_le_of_finrank_eq, eq_of_le_of_finrank_eq, finrank_vectorSpan_image_finset, hi.finrank_vectorSpan_image_finset
-/
theorem AffineIndependent.vectorSpan_image_finset_eq_of_le_of_card_eq_finrank_add_one
    [DecidableEq P] {p : ι -> P}
    (hi : AffineIndependent k p) {s : Finset ι} {sm : Submodule k V} [FiniteDimensional k sm]
    (hle : vectorSpan k (s.image p : Set P) <= sm) (hc : #s = finrank k sm + 1) :
    vectorSpan k (s.image p : Set P) = sm :=
Submodule.eq_of_le_of_finrank_eq hle hi.finrank_vectorSpan_image_finset hc

/--
theorem `AffineIndependent.vectorSpan_eq_of_le_of_card_eq_finrank_add_one` / 定理 `AffineIndependent.vectorSpan_eq_of_le_of_card_eq_finrank_add_one`

English:
theorem AffineIndependent.vectorSpan_eq_of_le_of_card_eq_finrank_add_one
  statement: [Fintype ι] {p : ι -> P}
  proof: Submodule.eq_of_le_of_finrank_eq hle hi.finrank_vectorSpan hc

中文:
定理 AffineIndependent.vectorSpan_eq_of_le_of_card_eq_finrank_add_one
  结论: [Fintype ι] {p : ι -> P}
  证明: Submodule.eq_of_le_of_finrank_eq hle hi.finrank_vectorSpan hc

Depends on / 依赖: Submodule, Submodule.eq_of_le_of_finrank_eq, eq_of_le_of_finrank_eq, finrank_vectorSpan, hi.finrank_vectorSpan
-/
theorem AffineIndependent.vectorSpan_eq_of_le_of_card_eq_finrank_add_one [Fintype ι] {p : ι -> P}
    (hi : AffineIndependent k p) {sm : Submodule k V} [FiniteDimensional k sm]
    (hle : vectorSpan k (Set.range p) <= sm) (hc : Fintype.card ι = finrank k sm + 1) :
    vectorSpan k (Set.range p) = sm :=
Submodule.eq_of_le_of_finrank_eq hle hi.finrank_vectorSpan hc

/--
theorem `AffineIndependent.affineSpan_image_finset_eq_of_le_of_card_eq_finrank_add_one` / 定理 `AffineIndependent.affineSpan_image_finset_eq_of_le_of_card_eq_finrank_add_one`

English:
theorem AffineIndependent.affineSpan_image_finset_eq_of_le_of_card_eq_finrank_add_one
  proof: by
  have hn : s.Nonempty := by
    rw [← Finset.card_pos]; rw [hc]
    apply Nat.succ_pos
  refine eq_of_direction_eq_of_nonempty_of_le ?_ ((hn.image p).to_set.affineSpan k) hle
  have hd := direction_le hle
  rw [direction_affineSpan] at hd ⊢
  exact hi.vectorSpan_image_finset_eq_of_le_of_card_eq_

中文:
定理 AffineIndependent.affineSpan_image_finset_eq_of_le_of_card_eq_finrank_add_one
  证明: by
  have hn : s.Nonempty := by
    rw [← Finset.card_pos]; rw [hc]
    apply Nat.succ_pos
  refine eq_of_direction_eq_of_nonempty_of_le ?_ ((hn.image p).to_set.affineSpan k) hle
  have hd := direction_le hle
  rw [direction_affineSpan] at hd ⊢
  exact hi.vectorSpan_image_finset_eq_of_le_of_card_eq_

Depends on / 依赖: Finset, Finset.card_pos, Nat.succ_pos, Nonempty, affineSpan, card_pos, direction_affineSpan, direction_le, eq_of_direction_eq_of_nonempty_of_le, hi.vectorSpan_image_finset_eq_of_le_of_card_eq_finrank_add_one, hn.image, s.Nonempty, succ_pos, to_set, to_set.affineSpan, vectorSpan_image_finset_eq_of_le_of_card_eq_finrank_add_one
-/
theorem AffineIndependent.affineSpan_image_finset_eq_of_le_of_card_eq_finrank_add_one
    [DecidableEq P] {p : ι -> P}
    (hi : AffineIndependent k p) {s : Finset ι} {sp : AffineSubspace k P}
    [FiniteDimensional k sp.direction] (hle : affineSpan k (s.image p : Set P) <= sp)
    (hc : #s = finrank k sp.direction + 1) : affineSpan k (s.image p : Set P) = sp := by
  have hn : s.Nonempty := by
    rw [← Finset.card_pos]; rw [hc]
    apply Nat.succ_pos
  refine eq_of_direction_eq_of_nonempty_of_le ?_ ((hn.image p).to_set.affineSpan k) hle
  have hd := direction_le hle
  rw [direction_affineSpan] at hd ⊢
  exact hi.vectorSpan_image_finset_eq_of_le_of_card_eq_finrank_add_one hd hc

/--
theorem `AffineIndependent.affineSpan_eq_of_le_of_card_eq_finrank_add_one` / 定理 `AffineIndependent.affineSpan_eq_of_le_of_card_eq_finrank_add_one`

English:
theorem AffineIndependent.affineSpan_eq_of_le_of_card_eq_finrank_add_one
  statement: [Fintype ι] {p : ι -> P}
  proof: by
  classical
  rw [← Finset.card_univ] at hc
  rw [← Set.image_univ]; rw [← Finset.coe_univ]; rw [← Finset.coe_image] at hle ⊢
  exact hi.affineSpan_image_finset_eq_of_le_of_card_eq_finrank_add_one hle hc

中文:
定理 AffineIndependent.affineSpan_eq_of_le_of_card_eq_finrank_add_one
  结论: [Fintype ι] {p : ι -> P}
  证明: by
  classical
  rw [← Finset.card_univ] at hc
  rw [← Set.image_univ]; rw [← Finset.coe_univ]; rw [← Finset.coe_image] at hle ⊢
  exact hi.affineSpan_image_finset_eq_of_le_of_card_eq_finrank_add_one hle hc

Depends on / 依赖: Finset, Finset.card_univ, Finset.coe_image, Finset.coe_univ, Set.image_univ, affineSpan_image_finset_eq_of_le_of_card_eq_finrank_add_one, card_univ, classical, coe_image, coe_univ, hi.affineSpan_image_finset_eq_of_le_of_card_eq_finrank_add_one, image_univ
-/
theorem AffineIndependent.affineSpan_eq_of_le_of_card_eq_finrank_add_one [Fintype ι] {p : ι -> P}
    (hi : AffineIndependent k p) {sp : AffineSubspace k P} [FiniteDimensional k sp.direction]
    (hle : affineSpan k (Set.range p) <= sp) (hc : Fintype.card ι = finrank k sp.direction + 1) :
    affineSpan k (Set.range p) = sp := by
  classical
  rw [← Finset.card_univ] at hc
  rw [← Set.image_univ]; rw [← Finset.coe_univ]; rw [← Finset.coe_image] at hle ⊢
  exact hi.affineSpan_image_finset_eq_of_le_of_card_eq_finrank_add_one hle hc

/--
theorem `AffineIndependent.affineSpan_eq_top_iff_card_eq_finrank_add_one` / 定理 `AffineIndependent.affineSpan_eq_top_iff_card_eq_finrank_add_one`

English:
theorem AffineIndependent.affineSpan_eq_top_iff_card_eq_finrank_add_one
  statement: [FiniteDimensional k V]
  proof: by
  constructor
  · intro h_tot
    let n := Fintype.card ι - 1
    have hn : Fintype.card ι = n + 1 :=
      (Nat.succ_pred_eq_of_pos (card_pos_of_affineSpan_eq_top k V P h_tot)).symm
    rw [hn]; rw [← finrank_top]; rw [← (vectorSpan_eq_top_of_affineSpan_eq_top k V P) h_tot]; rw [← hi.finrank_vec

中文:
定理 AffineIndependent.affineSpan_eq_top_iff_card_eq_finrank_add_one
  结论: [FiniteDimensional k V]
  证明: by
  constructor
  · intro h_tot
    let n := Fintype.card ι - 1
    have hn : Fintype.card ι = n + 1 :=
      (Nat.succ_pred_eq_of_pos (card_pos_of_affineSpan_eq_top k V P h_tot)).symm
    rw [hn]; rw [← finrank_top]; rw [← (vectorSpan_eq_top_of_affineSpan_eq_top k V P) h_tot]; rw [← hi.finrank_vec

Depends on / 依赖: Fintype, Fintype.card, Nat.succ_pred_eq_of_pos, affineSpan_eq_of_le_of_card_eq_finrank_add_one, card_pos_of_affineSpan_eq_top, direction_top, finrank_top, finrank_vectorSpan, h_tot, hi.affineSpan_eq_of_le_of_card_eq_finrank_add_one, hi.finrank_vectorSpan, le_top, succ_pred_eq_of_pos, vectorSpan_eq_top_of_affineSpan_eq_top
-/
theorem AffineIndependent.affineSpan_eq_top_iff_card_eq_finrank_add_one [FiniteDimensional k V]
    [Fintype ι] {p : ι -> P} (hi : AffineIndependent k p) :
    affineSpan k (Set.range p) = ⊤ ↔ Fintype.card ι = finrank k V + 1 := by
  constructor
  · intro h_tot
    let n := Fintype.card ι - 1
    have hn : Fintype.card ι = n + 1 :=
      (Nat.succ_pred_eq_of_pos (card_pos_of_affineSpan_eq_top k V P h_tot)).symm
    rw [hn]; rw [← finrank_top]; rw [← (vectorSpan_eq_top_of_affineSpan_eq_top k V P) h_tot]; rw [← hi.finrank_vectorSpan hn]
  · intro hc
    rw [← finrank_top]; rw [← direction_top k V P] at hc
    exact hi.affineSpan_eq_of_le_of_card_eq_finrank_add_one le_top hc

/--
theorem `Affine.Simplex.span_eq_top` / 定理 `Affine.Simplex.span_eq_top`

English:
theorem Affine.Simplex.span_eq_top
  statement: [FiniteDimensional k V] {n : Nat} (T : Affine.Simplex k V n)
  proof: by
  rw [AffineIndependent.affineSpan_eq_top_iff_card_eq_finrank_add_one T.independent]; rw [Fintype.card_fin]; rw [hrank]

中文:
定理 Affine.Simplex.span_eq_top
  结论: [FiniteDimensional k V] {n : 自然数} (T : Affine.Simplex k V n)
  证明: by
  rw [AffineIndependent.affineSpan_eq_top_iff_card_eq_finrank_add_one T.independent]; rw [Fintype.card_fin]; rw [hrank]

Depends on / 依赖: AffineIndependent, AffineIndependent.affineSpan_eq_top_iff_card_eq_finrank_add_one, Fintype, Fintype.card_fin, T.independent, affineSpan_eq_top_iff_card_eq_finrank_add_one, card_fin, independent
-/
theorem Affine.Simplex.span_eq_top [FiniteDimensional k V] {n : Nat} (T : Affine.Simplex k V n)
    (hrank : finrank k V = n) : affineSpan k (Set.range T.points) = ⊤ := by
  rw [AffineIndependent.affineSpan_eq_top_iff_card_eq_finrank_add_one T.independent]; rw [Fintype.card_fin]; rw [hrank]

/--
Instance `finiteDimensional_vectorSpan_insert` / 实例 `finiteDimensional_vectorSpan_insert`

English:
instance finiteDimensional_vectorSpan_insert
  signature: (s : AffineSubspace k P)
  body: by
  rw [← direction_affineSpan]; rw [← affineSpan_insert_affineSpan]
  rcases (s : Set P).eq_empty_or_nonempty with (hs | ⟨p₀, hp₀⟩)
  · rw [coe_eq_bot_iff] at hs
    rw [hs]; rw [bot_coe]; rw [span_empty]; rw [bot_coe]; rw [direction_affineSpan]
    convert! finiteDimensional_bot k V <;> simp
  · 

中文:
实例 finiteDimensional_vectorSpan_insert
  签名: (s : AffineSubspace k P)
  定义体: by
  rw [← direction_affineSpan]; rw [← affineSpan_insert_affineSpan]
  rcases (s : Set P).eq_empty_or_nonempty with (hs | ⟨p₀, hp₀⟩)
  · rw [coe_eq_bot_iff] at hs
    rw [hs]; rw [bot_coe]; rw [span_empty]; rw [bot_coe]; rw [direction_affineSpan]
    convert! finiteDimensional_bot k V <;> simp
  · 

Depends on / 依赖: affineSpan_coe, affineSpan_insert_affineSpan, bot_coe, coe_eq_bot_iff, convert, direction_affineSpan, direction_affineSpan_insert, eq_empty_or_nonempty, finiteDimensional_bot, infer_instance, span_empty
-/
instance finiteDimensional_vectorSpan_insert (s : AffineSubspace k P)
    [FiniteDimensional k s.direction] (p : P) :
    FiniteDimensional k (vectorSpan k (insert p (s : Set P))) := by
  rw [← direction_affineSpan]; rw [← affineSpan_insert_affineSpan]
  rcases (s : Set P).eq_empty_or_nonempty with (hs | ⟨p₀, hp₀⟩)
  · rw [coe_eq_bot_iff] at hs
    rw [hs]; rw [bot_coe]; rw [span_empty]; rw [bot_coe]; rw [direction_affineSpan]
    convert! finiteDimensional_bot k V <;> simp
  · rw [affineSpan_coe, direction_affineSpan_insert hp₀]
    infer_instance

/--
Instance `finiteDimensional_direction_affineSpan_insert` / 实例 `finiteDimensional_direction_affineSpan_insert`

English:
instance finiteDimensional_direction_affineSpan_insert
  signature: (s : AffineSubspace k P)
  body: (direction_affineSpan k (insert p (s : Set P))).symm ▸ finiteDimensional_vectorSpan_insert s p

中文:
实例 finiteDimensional_direction_affineSpan_insert
  签名: (s : AffineSubspace k P)
  定义体: (direction_affineSpan k (insert p (s : Set P))).symm ▸ finiteDimensional_vectorSpan_insert s p

Depends on / 依赖: direction_affineSpan, finiteDimensional_vectorSpan_insert, insert
-/
instance finiteDimensional_direction_affineSpan_insert (s : AffineSubspace k P)
    [FiniteDimensional k s.direction] (p : P) :
    FiniteDimensional k (affineSpan k (insert p (s : Set P))).direction :=
  (direction_affineSpan k (insert p (s : Set P))).symm ▸ finiteDimensional_vectorSpan_insert s p

variable (k)

/--
Instance `finiteDimensional_vectorSpan_insert_set` / 实例 `finiteDimensional_vectorSpan_insert_set`

English:
instance finiteDimensional_vectorSpan_insert_set
  signature: (s : Set P) [FiniteDimensional k (vectorSpan k s)]
  body: by
  have : FiniteDimensional k (affineSpan k s).direction :=
    (direction_affineSpan k s).symm ▸ inferInstance
  rw [← direction_affineSpan]; rw [← affineSpan_insert_affineSpan]; rw [direction_affineSpan]
  exact finiteDimensional_vectorSpan_insert (affineSpan k s) p

中文:
实例 finiteDimensional_vectorSpan_insert_set
  签名: (s : Set P) [FiniteDimensional k (vectorSpan k s)]
  定义体: by
  have : FiniteDimensional k (affineSpan k s).direction :=
    (direction_affineSpan k s).symm ▸ inferInstance
  rw [← direction_affineSpan]; rw [← affineSpan_insert_affineSpan]; rw [direction_affineSpan]
  exact finiteDimensional_vectorSpan_insert (affineSpan k s) p

Depends on / 依赖: FiniteDimensional, affineSpan, affineSpan_insert_affineSpan, direction, direction_affineSpan, finiteDimensional_vectorSpan_insert
-/
instance finiteDimensional_vectorSpan_insert_set (s : Set P) [FiniteDimensional k (vectorSpan k s)]
    (p : P) : FiniteDimensional k (vectorSpan k (insert p s)) := by
  have : FiniteDimensional k (affineSpan k s).direction :=
    (direction_affineSpan k s).symm ▸ inferInstance
  rw [← direction_affineSpan]; rw [← affineSpan_insert_affineSpan]; rw [direction_affineSpan]
  exact finiteDimensional_vectorSpan_insert (affineSpan k s) p

/--
Instance `finiteDimensional_direction_affineSpan_insert_set` / 实例 `finiteDimensional_direction_affineSpan_insert_set`

English:
instance finiteDimensional_direction_affineSpan_insert_set
  signature: (s : Set P)
  body: by
  have : FiniteDimensional k (vectorSpan k s) := (direction_affineSpan k s) ▸ inferInstance
  rw [direction_affineSpan]
  infer_instance

中文:
实例 finiteDimensional_direction_affineSpan_insert_set
  签名: (s : Set P)
  定义体: by
  have : FiniteDimensional k (vectorSpan k s) := (direction_affineSpan k s) ▸ inferInstance
  rw [direction_affineSpan]
  infer_instance

Depends on / 依赖: FiniteDimensional, direction_affineSpan, infer_instance, vectorSpan
-/
instance finiteDimensional_direction_affineSpan_insert_set (s : Set P)
    [FiniteDimensional k (affineSpan k s).direction] (p : P) :
    FiniteDimensional k (affineSpan k (insert p s)).direction := by
  have : FiniteDimensional k (vectorSpan k s) := (direction_affineSpan k s) ▸ inferInstance
  rw [direction_affineSpan]
  infer_instance

/--
Definition of `Collinear` / `Collinear` 的定义

English:
definition Collinear
  signature: (s : Set P)
  body: Module.rank k (vectorSpan k s) <= 1

中文:
定义 Collinear
  签名: (s : Set P)
  定义体: Module.rank k (vectorSpan k s) <= 1

Depends on / 依赖: Module, Module.rank, vectorSpan
-/
def Collinear (s : Set P) : Prop :=
  Module.rank k (vectorSpan k s) <= 1

/--
theorem `collinear_iff_rank_le_one` / 定理 `collinear_iff_rank_le_one`

English:
theorem collinear_iff_rank_le_one
  given: (s : Set P)
  proof: Iff.rfl

中文:
定理 collinear_iff_rank_le_one
  条件: (s : Set P)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem collinear_iff_rank_le_one (s : Set P) :
    Collinear k s ↔ Module.rank k (vectorSpan k s) <= 1 := Iff.rfl

variable {k}

/--
theorem `collinear_iff_finrank_le_one` / 定理 `collinear_iff_finrank_le_one`

English:
theorem collinear_iff_finrank_le_one
  given: {s : Set P} [FiniteDimensional k (vectorSpan k s)]
  proof: by
  have h := collinear_iff_rank_le_one k s
  rw [← finrank_eq_rank] at h
  exact mod_cast h

alias ⟨Collinear.finrank_le_one, _⟩ := collinear_iff_finrank_le_one

中文:
定理 collinear_iff_finrank_le_one
  条件: {s : Set P} [FiniteDimensional k (vectorSpan k s)]
  证明: by
  have h := collinear_iff_rank_le_one k s
  rw [← finrank_eq_rank] at h
  exact mod_cast h

alias ⟨Collinear.finrank_le_one, _⟩ := collinear_iff_finrank_le_one

Depends on / 依赖: collinear_iff_rank_le_one, finrank_eq_rank, mod_cast
-/
theorem collinear_iff_finrank_le_one {s : Set P} [FiniteDimensional k (vectorSpan k s)] :
    Collinear k s ↔ finrank k (vectorSpan k s) <= 1 := by
  have h := collinear_iff_rank_le_one k s
  rw [← finrank_eq_rank] at h
  exact mod_cast h

alias ⟨Collinear.finrank_le_one, _⟩ := collinear_iff_finrank_le_one

/--
theorem `Collinear.subset` / 定理 `Collinear.subset`

English:
theorem Collinear.subset
  given: {s₁ s₂ : Set P} (hs : s₁ subseteq s₂) (h : Collinear k s₂)
  statement: Collinear k s₁
  proof: (Submodule.rank_mono (vectorSpan_mono k hs)).trans h

中文:
定理 Collinear.subset
  条件: {s₁ s₂ : Set P} (hs : s₁ subseteq s₂) (h : Collinear k s₂)
  结论: Collinear k s₁
  证明: (Submodule.rank_mono (vectorSpan_mono k hs)).trans h

Depends on / 依赖: Submodule, Submodule.rank_mono, rank_mono, vectorSpan_mono
-/
theorem Collinear.subset {s₁ s₂ : Set P} (hs : s₁ subseteq s₂) (h : Collinear k s₂) : Collinear k s₁ :=
  (Submodule.rank_mono (vectorSpan_mono k hs)).trans h

/--
theorem `Collinear.finiteDimensional_vectorSpan` / 定理 `Collinear.finiteDimensional_vectorSpan`

English:
theorem Collinear.finiteDimensional_vectorSpan
  given: {s : Set P} (h : Collinear k s)
  proof: IsNoetherian.iff_fg.1
    (IsNoetherian.iff_rank_lt_aleph0.2 (lt_of_le_of_lt h Cardinal.one_lt_aleph0))

中文:
定理 Collinear.finiteDimensional_vectorSpan
  条件: {s : Set P} (h : Collinear k s)
  证明: IsNoetherian.iff_fg.1
    (IsNoetherian.iff_rank_lt_aleph0.2 (lt_of_le_of_lt h Cardinal.one_lt_aleph0))

Depends on / 依赖: Cardinal, Cardinal.one_lt_aleph0, IsNoetherian, IsNoetherian.iff_fg, IsNoetherian.iff_rank_lt_aleph0, iff_fg, iff_rank_lt_aleph0, lt_of_le_of_lt, one_lt_aleph0
-/
theorem Collinear.finiteDimensional_vectorSpan {s : Set P} (h : Collinear k s) :
    FiniteDimensional k (vectorSpan k s) :=
  IsNoetherian.iff_fg.1
    (IsNoetherian.iff_rank_lt_aleph0.2 (lt_of_le_of_lt h Cardinal.one_lt_aleph0))

/--
theorem `Collinear.finiteDimensional_direction_affineSpan` / 定理 `Collinear.finiteDimensional_direction_affineSpan`

English:
theorem Collinear.finiteDimensional_direction_affineSpan
  given: {s : Set P} (h : Collinear k s)
  proof: (direction_affineSpan k s).symm ▸ h.finiteDimensional_vectorSpan

中文:
定理 Collinear.finiteDimensional_direction_affineSpan
  条件: {s : Set P} (h : Collinear k s)
  证明: (direction_affineSpan k s).symm ▸ h.finiteDimensional_vectorSpan

Depends on / 依赖: direction_affineSpan, finiteDimensional_vectorSpan, h.finiteDimensional_vectorSpan
-/
theorem Collinear.finiteDimensional_direction_affineSpan {s : Set P} (h : Collinear k s) :
    FiniteDimensional k (affineSpan k s).direction :=
  (direction_affineSpan k s).symm ▸ h.finiteDimensional_vectorSpan

variable (k P)

/--
theorem `collinear_empty` / 定理 `collinear_empty`

English:
theorem collinear_empty
  statement: Collinear k (∅ : Set P)
  proof: by
  rw [collinear_iff_rank_le_one]; rw [vectorSpan_empty]
  simp

中文:
定理 collinear_empty
  结论: Collinear k (∅ : Set P)
  证明: by
  rw [collinear_iff_rank_le_one]; rw [vectorSpan_empty]
  simp

Depends on / 依赖: collinear_iff_rank_le_one, vectorSpan_empty
-/
theorem collinear_empty : Collinear k (∅ : Set P) := by
  rw [collinear_iff_rank_le_one]; rw [vectorSpan_empty]
  simp

variable {P}

/--
theorem `collinear_singleton` / 定理 `collinear_singleton`

English:
theorem collinear_singleton
  given: (p : P)
  statement: Collinear k ({p} : Set P)
  proof: by
  rw [collinear_iff_rank_le_one]; rw [vectorSpan_singleton]
  simp

中文:
定理 collinear_singleton
  条件: (p : P)
  结论: Collinear k ({p} : Set P)
  证明: by
  rw [collinear_iff_rank_le_one]; rw [vectorSpan_singleton]
  simp

Depends on / 依赖: collinear_iff_rank_le_one, vectorSpan_singleton
-/
theorem collinear_singleton (p : P) : Collinear k ({p} : Set P) := by
  rw [collinear_iff_rank_le_one]; rw [vectorSpan_singleton]
  simp

variable {k}

/--
theorem `collinear_iff_of_mem` / 定理 `collinear_iff_of_mem`

English:
theorem collinear_iff_of_mem
  given: {s : Set P} {p₀ : P} (h : p₀ in s)
  proof: by
  simp_rw [collinear_iff_rank_le_one, rank_submodule_le_one_iff', Submodule.le_span_singleton_iff]
  constructor
  · rintro ⟨v₀, hv⟩
    use v₀
    intro p hp
    obtain ⟨r, hr⟩ := hv (p -ᵥ p₀) (vsub_mem_vectorSpan k hp h)
    use r
    rw [eq_vadd_iff_vsub_eq]
    exact hr.symm
  · rintro ⟨v, hp

中文:
定理 collinear_iff_of_mem
  条件: {s : Set P} {p₀ : P} (h : p₀ in s)
  证明: by
  simp_rw [collinear_iff_rank_le_one, rank_submodule_le_one_iff', Submodule.le_span_singleton_iff]
  constructor
  · rintro ⟨v₀, hv⟩
    use v₀
    intro p hp
    obtain ⟨r, hr⟩ := hv (p -ᵥ p₀) (vsub_mem_vectorSpan k hp h)
    use r
    rw [eq_vadd_iff_vsub_eq]
    exact hr.symm
  · rintro ⟨v, hp

Depends on / 依赖: Set.mem_imag, Set.subset_def, SetLike, SetLike.mem_coe, Submodule, Submodule.le_span_singleton_iff, Submodule.mem_span_singleton, Submodule.span_le, collinear_iff_rank_le_one, eq_vadd_iff_vsub_eq, hr.symm, le_span_singleton_iff, mem_coe, mem_imag, mem_span_singleton, rank_submodule_le_one_iff, simp_rw, span_le, subset_def, vectorSpan
-/
theorem collinear_iff_of_mem {s : Set P} {p₀ : P} (h : p₀ in s) :
    Collinear k s ↔ exists v : V, forall p in s, exists r : k, p = r • v +ᵥ p₀ := by
  simp_rw [collinear_iff_rank_le_one, rank_submodule_le_one_iff', Submodule.le_span_singleton_iff]
  constructor
  · rintro ⟨v₀, hv⟩
    use v₀
    intro p hp
    obtain ⟨r, hr⟩ := hv (p -ᵥ p₀) (vsub_mem_vectorSpan k hp h)
    use r
    rw [eq_vadd_iff_vsub_eq]
    exact hr.symm
  · rintro ⟨v, hp₀v⟩
    use v
    intro w hw
    have hs : vectorSpan k s <= k ∙ v := by
      rw [vectorSpan_eq_span_vsub_set_right k h]; rw [Submodule.span_le]; rw [Set.subset_def]
      intro x hx
      rw [SetLike.mem_coe]; rw [Submodule.mem_span_singleton]
      rw [Set.mem_image] at hx
      rcases hx with ⟨p, hp, rfl⟩
      rcases hp₀v p hp with ⟨r, rfl⟩
      use r
      simp
    have hw' := SetLike.le_def.1 hs hw
    rwa [Submodule.mem_span_singleton] at hw'

/--
theorem `collinear_iff_exists_forall_eq_smul_vadd` / 定理 `collinear_iff_exists_forall_eq_smul_vadd`

English:
theorem collinear_iff_exists_forall_eq_smul_vadd
  given: (s : Set P)
  proof: by
  rcases Set.eq_empty_or_nonempty s with (rfl | ⟨⟨p₁, hp₁⟩⟩)
  · simp [collinear_empty]
  · rw [collinear_iff_of_mem hp₁]
    constructor
    · exact fun h => ⟨p₁, h⟩
    · rintro ⟨p, v, hv⟩
      use v
      intro p₂ hp₂
      rcases hv p₂ hp₂ with ⟨r, rfl⟩
      rcases hv p₁ hp₁ with ⟨r₁, rfl⟩


中文:
定理 collinear_iff_exists_forall_eq_smul_vadd
  条件: (s : Set P)
  证明: by
  rcases Set.eq_empty_or_nonempty s with (rfl | ⟨⟨p₁, hp₁⟩⟩)
  · simp [collinear_empty]
  · rw [collinear_iff_of_mem hp₁]
    constructor
    · exact fun h => ⟨p₁, h⟩
    · rintro ⟨p, v, hv⟩
      use v
      intro p₂ hp₂
      rcases hv p₂ hp₂ with ⟨r, rfl⟩
      rcases hv p₁ hp₁ with ⟨r₁, rfl⟩


Depends on / 依赖: Set.eq_empty_or_nonempty, add_smul, collinear_empty, collinear_iff_of_mem, eq_empty_or_nonempty, vadd_vadd
-/
theorem collinear_iff_exists_forall_eq_smul_vadd (s : Set P) :
    Collinear k s ↔ exists (p₀ : P) (v : V), forall p in s, exists r : k, p = r • v +ᵥ p₀ := by
  rcases Set.eq_empty_or_nonempty s with (rfl | ⟨⟨p₁, hp₁⟩⟩)
  · simp [collinear_empty]
  · rw [collinear_iff_of_mem hp₁]
    constructor
    · exact fun h => ⟨p₁, h⟩
    · rintro ⟨p, v, hv⟩
      use v
      intro p₂ hp₂
      rcases hv p₂ hp₂ with ⟨r, rfl⟩
      rcases hv p₁ hp₁ with ⟨r₁, rfl⟩
      use r - r₁
      simp [vadd_vadd, ← add_smul]

variable (k) in
/--
theorem `collinear_pair` / 定理 `collinear_pair`

English:
theorem collinear_pair
  given: (p₁ p₂ : P)
  statement: Collinear k ({p₁, p₂} : Set P)
  proof: by
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  use p₁, p₂ -ᵥ p₁
  intro p hp
  rw [Set.mem_insert_iff]; rw [Set.mem_singleton_iff] at hp
  rcases hp with hp | hp
  · use 0
    simp [hp]
  · use 1
    simp [hp]

中文:
定理 collinear_pair
  条件: (p₁ p₂ : P)
  结论: Collinear k ({p₁, p₂} : Set P)
  证明: by
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  use p₁, p₂ -ᵥ p₁
  intro p hp
  rw [Set.mem_insert_iff]; rw [Set.mem_singleton_iff] at hp
  rcases hp with hp | hp
  · use 0
    simp [hp]
  · use 1
    simp [hp]

Depends on / 依赖: Set.mem_insert_iff, Set.mem_singleton_iff, collinear_iff_exists_forall_eq_smul_vadd, mem_insert_iff, mem_singleton_iff
-/
theorem collinear_pair (p₁ p₂ : P) : Collinear k ({p₁, p₂} : Set P) := by
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  use p₁, p₂ -ᵥ p₁
  intro p hp
  rw [Set.mem_insert_iff]; rw [Set.mem_singleton_iff] at hp
  rcases hp with hp | hp
  · use 0
    simp [hp]
  · use 1
    simp [hp]

/--
theorem `affineIndependent_iff_not_collinear` / 定理 `affineIndependent_iff_not_collinear`

English:
theorem affineIndependent_iff_not_collinear
  given: {p : Fin 3 -> P}
  proof: by
  rw [collinear_iff_finrank_le_one]; rw [affineIndependent_iff_not_finrank_vectorSpan_le k p (Fintype.card_fin 3)]

中文:
定理 affineIndependent_iff_not_collinear
  条件: {p : Fin 3 -> P}
  证明: by
  rw [collinear_iff_finrank_le_one]; rw [affineIndependent_iff_not_finrank_vectorSpan_le k p (Fintype.card_fin 3)]

Depends on / 依赖: Fintype, Fintype.card_fin, affineIndependent_iff_not_finrank_vectorSpan_le, card_fin, collinear_iff_finrank_le_one
-/
theorem affineIndependent_iff_not_collinear {p : Fin 3 -> P} :
    AffineIndependent k p ↔ ¬Collinear k (Set.range p) := by
  rw [collinear_iff_finrank_le_one]; rw [affineIndependent_iff_not_finrank_vectorSpan_le k p (Fintype.card_fin 3)]

/--
theorem `collinear_iff_not_affineIndependent` / 定理 `collinear_iff_not_affineIndependent`

English:
theorem collinear_iff_not_affineIndependent
  given: {p : Fin 3 -> P}
  proof: by
  rw [collinear_iff_finrank_le_one]; rw [finrank_vectorSpan_le_iff_not_affineIndependent k p (Fintype.card_fin 3)]

中文:
定理 collinear_iff_not_affineIndependent
  条件: {p : Fin 3 -> P}
  证明: by
  rw [collinear_iff_finrank_le_one]; rw [finrank_vectorSpan_le_iff_not_affineIndependent k p (Fintype.card_fin 3)]

Depends on / 依赖: Fintype, Fintype.card_fin, card_fin, collinear_iff_finrank_le_one, finrank_vectorSpan_le_iff_not_affineIndependent
-/
theorem collinear_iff_not_affineIndependent {p : Fin 3 -> P} :
    Collinear k (Set.range p) ↔ ¬AffineIndependent k p := by
  rw [collinear_iff_finrank_le_one]; rw [finrank_vectorSpan_le_iff_not_affineIndependent k p (Fintype.card_fin 3)]

/--
theorem `affineIndependent_iff_not_collinear_set` / 定理 `affineIndependent_iff_not_collinear_set`

English:
theorem affineIndependent_iff_not_collinear_set
  given: {p₁ p₂ p₃ : P}
  proof: by
  rw [affineIndependent_iff_not_collinear]
  simp_rw [Matrix.range_cons, Matrix.range_empty, Set.singleton_union, insert_empty_eq]

中文:
定理 affineIndependent_iff_not_collinear_set
  条件: {p₁ p₂ p₃ : P}
  证明: by
  rw [affineIndependent_iff_not_collinear]
  simp_rw [Matrix.range_cons, Matrix.range_empty, Set.singleton_union, insert_empty_eq]

Depends on / 依赖: Matrix, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, affineIndependent_iff_not_collinear, insert_empty_eq, range_cons, range_empty, simp_rw, singleton_union
-/
theorem affineIndependent_iff_not_collinear_set {p₁ p₂ p₃ : P} :
    AffineIndependent k ![p₁, p₂, p₃] ↔ ¬Collinear k ({p₁, p₂, p₃} : Set P) := by
  rw [affineIndependent_iff_not_collinear]
  simp_rw [Matrix.range_cons, Matrix.range_empty, Set.singleton_union, insert_empty_eq]

/--
theorem `collinear_iff_not_affineIndependent_set` / 定理 `collinear_iff_not_affineIndependent_set`

English:
theorem collinear_iff_not_affineIndependent_set
  given: {p₁ p₂ p₃ : P}
  proof: affineIndependent_iff_not_collinear_set.not_left.symm

中文:
定理 collinear_iff_not_affineIndependent_set
  条件: {p₁ p₂ p₃ : P}
  证明: affineIndependent_iff_not_collinear_set.not_left.symm

Depends on / 依赖: affineIndependent_iff_not_collinear_set, affineIndependent_iff_not_collinear_set.not_left.symm, not_left
-/
theorem collinear_iff_not_affineIndependent_set {p₁ p₂ p₃ : P} :
    Collinear k ({p₁, p₂, p₃} : Set P) ↔ ¬AffineIndependent k ![p₁, p₂, p₃] :=
  affineIndependent_iff_not_collinear_set.not_left.symm

/--
theorem `affineIndependent_iff_not_collinear_of_ne` / 定理 `affineIndependent_iff_not_collinear_of_ne`

English:
theorem affineIndependent_iff_not_collinear_of_ne
  statement: {p : Fin 3 -> P} {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ != i₂)
  proof: by
  have hu : (Finset.univ : Finset (Fin 3)) = {i₁, i₂, i₃} := by decide +revert
  rw [affineIndependent_iff_not_collinear]; rw [← Set.image_univ]; rw [← Finset.coe_univ]; rw [hu]; rw [Finset.coe_insert]; rw [Finset.coe_insert]; rw [Finset.coe_singleton]; rw [Set.image_insert_eq]; rw [Set.image_pai

中文:
定理 affineIndependent_iff_not_collinear_of_ne
  结论: {p : Fin 3 -> P} {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ != i₂)
  证明: by
  have hu : (Finset.univ : Finset (Fin 3)) = {i₁, i₂, i₃} := by decide +revert
  rw [affineIndependent_iff_not_collinear]; rw [← Set.image_univ]; rw [← Finset.coe_univ]; rw [hu]; rw [Finset.coe_insert]; rw [Finset.coe_insert]; rw [Finset.coe_singleton]; rw [Set.image_insert_eq]; rw [Set.image_pai

Depends on / 依赖: Finset, Finset.coe_insert, Finset.coe_singleton, Finset.coe_univ, Finset.univ, Set.image_insert_eq, Set.image_pair, Set.image_univ, affineIndependent_iff_not_collinear, coe_insert, coe_singleton, coe_univ, image_insert_eq, image_pair, image_univ, revert
-/
theorem affineIndependent_iff_not_collinear_of_ne {p : Fin 3 -> P} {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ != i₂)
    (h₁₃ : i₁ != i₃) (h₂₃ : i₂ != i₃) :
    AffineIndependent k p ↔ ¬Collinear k ({p i₁, p i₂, p i₃} : Set P) := by
  have hu : (Finset.univ : Finset (Fin 3)) = {i₁, i₂, i₃} := by decide +revert
  rw [affineIndependent_iff_not_collinear]; rw [← Set.image_univ]; rw [← Finset.coe_univ]; rw [hu]; rw [Finset.coe_insert]; rw [Finset.coe_insert]; rw [Finset.coe_singleton]; rw [Set.image_insert_eq]; rw [Set.image_pair]

/--
theorem `collinear_iff_not_affineIndependent_of_ne` / 定理 `collinear_iff_not_affineIndependent_of_ne`

English:
theorem collinear_iff_not_affineIndependent_of_ne
  statement: {p : Fin 3 -> P} {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ != i₂)
  proof: (affineIndependent_iff_not_collinear_of_ne h₁₂ h₁₃ h₂₃).not_left.symm

中文:
定理 collinear_iff_not_affineIndependent_of_ne
  结论: {p : Fin 3 -> P} {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ != i₂)
  证明: (affineIndependent_iff_not_collinear_of_ne h₁₂ h₁₃ h₂₃).not_left.symm

Depends on / 依赖: affineIndependent_iff_not_collinear_of_ne, not_left, not_left.symm
-/
theorem collinear_iff_not_affineIndependent_of_ne {p : Fin 3 -> P} {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ != i₂)
    (h₁₃ : i₁ != i₃) (h₂₃ : i₂ != i₃) :
    Collinear k ({p i₁, p i₂, p i₃} : Set P) ↔ ¬AffineIndependent k p :=
  (affineIndependent_iff_not_collinear_of_ne h₁₂ h₁₃ h₂₃).not_left.symm

/--
theorem `ne₁₂_of_not_collinear` / 定理 `ne₁₂_of_not_collinear`

English:
theorem ne₁₂_of_not_collinear
  given: {p₁ p₂ p₃ : P} (h : ¬Collinear k ({p₁, p₂, p₃} : Set P))
  proof: by
  rintro rfl
  simp [collinear_pair] at h

中文:
定理 ne₁₂_of_not_collinear
  条件: {p₁ p₂ p₃ : P} (h : ¬Collinear k ({p₁, p₂, p₃} : Set P))
  证明: by
  rintro rfl
  simp [collinear_pair] at h

Depends on / 依赖: collinear_pair
-/
theorem ne₁₂_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collinear k ({p₁, p₂, p₃} : Set P)) :
    p₁ != p₂ := by
  rintro rfl
  simp [collinear_pair] at h

/--
theorem `ne₁₃_of_not_collinear` / 定理 `ne₁₃_of_not_collinear`

English:
theorem ne₁₃_of_not_collinear
  given: {p₁ p₂ p₃ : P} (h : ¬Collinear k ({p₁, p₂, p₃} : Set P))
  proof: by
  rintro rfl
  simp [collinear_pair] at h

中文:
定理 ne₁₃_of_not_collinear
  条件: {p₁ p₂ p₃ : P} (h : ¬Collinear k ({p₁, p₂, p₃} : Set P))
  证明: by
  rintro rfl
  simp [collinear_pair] at h

Depends on / 依赖: collinear_pair
-/
theorem ne₁₃_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collinear k ({p₁, p₂, p₃} : Set P)) :
    p₁ != p₃ := by
  rintro rfl
  simp [collinear_pair] at h

/--
theorem `ne₂₃_of_not_collinear` / 定理 `ne₂₃_of_not_collinear`

English:
theorem ne₂₃_of_not_collinear
  given: {p₁ p₂ p₃ : P} (h : ¬Collinear k ({p₁, p₂, p₃} : Set P))
  proof: by
  rintro rfl
  simp [collinear_pair] at h

中文:
定理 ne₂₃_of_not_collinear
  条件: {p₁ p₂ p₃ : P} (h : ¬Collinear k ({p₁, p₂, p₃} : Set P))
  证明: by
  rintro rfl
  simp [collinear_pair] at h

Depends on / 依赖: collinear_pair
-/
theorem ne₂₃_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collinear k ({p₁, p₂, p₃} : Set P)) :
    p₂ != p₃ := by
  rintro rfl
  simp [collinear_pair] at h

/--
theorem `Collinear.mem_affineSpan_of_mem_of_ne` / 定理 `Collinear.mem_affineSpan_of_mem_of_ne`

English:
theorem Collinear.mem_affineSpan_of_mem_of_ne
  statement: {s : Set P} (h : Collinear k s) {p₁ p₂ p₃ : P}
  proof: by
  rw [collinear_iff_of_mem hp₁] at h
  rcases h with ⟨v, h⟩
  rcases h p₂ hp₂ with ⟨r₂, rfl⟩
  rcases h p₃ hp₃ with ⟨r₃, rfl⟩
  rw [vadd_left_mem_affineSpan_pair]
  refine ⟨r₃ / r₂, ?_⟩
  have h₂ : r₂ != 0 := by
    rintro rfl
    simp at hp₁p₂
  simp [smul_smul, h₂]

中文:
定理 Collinear.mem_affineSpan_of_mem_of_ne
  结论: {s : Set P} (h : Collinear k s) {p₁ p₂ p₃ : P}
  证明: by
  rw [collinear_iff_of_mem hp₁] at h
  rcases h with ⟨v, h⟩
  rcases h p₂ hp₂ with ⟨r₂, rfl⟩
  rcases h p₃ hp₃ with ⟨r₃, rfl⟩
  rw [vadd_left_mem_affineSpan_pair]
  refine ⟨r₃ / r₂, ?_⟩
  have h₂ : r₂ != 0 := by
    rintro rfl
    simp at hp₁p₂
  simp [smul_smul, h₂]

Depends on / 依赖: collinear_iff_of_mem, smul_smul, vadd_left_mem_affineSpan_pair
-/
theorem Collinear.mem_affineSpan_of_mem_of_ne {s : Set P} (h : Collinear k s) {p₁ p₂ p₃ : P}
    (hp₁ : p₁ in s) (hp₂ : p₂ in s) (hp₃ : p₃ in s) (hp₁p₂ : p₁ != p₂) : p₃ in line[k, p₁, p₂] := by
  rw [collinear_iff_of_mem hp₁] at h
  rcases h with ⟨v, h⟩
  rcases h p₂ hp₂ with ⟨r₂, rfl⟩
  rcases h p₃ hp₃ with ⟨r₃, rfl⟩
  rw [vadd_left_mem_affineSpan_pair]
  refine ⟨r₃ / r₂, ?_⟩
  have h₂ : r₂ != 0 := by
    rintro rfl
    simp at hp₁p₂
  simp [smul_smul, h₂]

/--
theorem `Collinear.affineSpan_eq_of_ne` / 定理 `Collinear.affineSpan_eq_of_ne`

English:
theorem Collinear.affineSpan_eq_of_ne
  statement: {s : Set P} (h : Collinear k s) {p₁ p₂ : P} (hp₁ : p₁ in s)
  proof: le_antisymm (affineSpan_mono _ (Set.insert_subset_iff.2 ⟨hp₁, Set.singleton_subset_iff.2 hp₂⟩))
    (affineSpan_le.2 fun _ hp => h.mem_affineSpan_of_mem_of_ne hp₁ hp₂ hp hp₁p₂)

中文:
定理 Collinear.affineSpan_eq_of_ne
  结论: {s : Set P} (h : Collinear k s) {p₁ p₂ : P} (hp₁ : p₁ in s)
  证明: le_antisymm (affineSpan_mono _ (Set.insert_subset_iff.2 ⟨hp₁, Set.singleton_subset_iff.2 hp₂⟩))
    (affineSpan_le.2 fun _ hp => h.mem_affineSpan_of_mem_of_ne hp₁ hp₂ hp hp₁p₂)

Depends on / 依赖: Set.insert_subset_iff, Set.singleton_subset_iff, affineSpan_le, affineSpan_mono, h.mem_affineSpan_of_mem_of_ne, insert_subset_iff, le_antisymm, mem_affineSpan_of_mem_of_ne, singleton_subset_iff
-/
theorem Collinear.affineSpan_eq_of_ne {s : Set P} (h : Collinear k s) {p₁ p₂ : P} (hp₁ : p₁ in s)
    (hp₂ : p₂ in s) (hp₁p₂ : p₁ != p₂) : line[k, p₁, p₂] = affineSpan k s :=
  le_antisymm (affineSpan_mono _ (Set.insert_subset_iff.2 ⟨hp₁, Set.singleton_subset_iff.2 hp₂⟩))
    (affineSpan_le.2 fun _ hp => h.mem_affineSpan_of_mem_of_ne hp₁ hp₂ hp hp₁p₂)

/--
theorem `Collinear.collinear_insert_iff_of_ne` / 定理 `Collinear.collinear_insert_iff_of_ne`

English:
theorem Collinear.collinear_insert_iff_of_ne
  statement: {s : Set P} (h : Collinear k s) {p₁ p₂ p₃ : P}
  proof: by
  have hv : vectorSpan k (insert p₁ s) = vectorSpan k ({p₁, p₂, p₃} : Set P) := by
    conv_rhs => rw [← direction_affineSpan, ← affineSpan_insert_affineSpan]
    rw [← direction_affineSpan]; rw [← affineSpan_insert_affineSpan]; rw [h.affineSpan_eq_of_ne hp₂ hp₃ hp₂p₃]
  rw [Collinear]; rw [Colli

中文:
定理 Collinear.collinear_insert_iff_of_ne
  结论: {s : Set P} (h : Collinear k s) {p₁ p₂ p₃ : P}
  证明: by
  have hv : vectorSpan k (insert p₁ s) = vectorSpan k ({p₁, p₂, p₃} : Set P) := by
    conv_rhs => rw [← direction_affineSpan, ← affineSpan_insert_affineSpan]
    rw [← direction_affineSpan]; rw [← affineSpan_insert_affineSpan]; rw [h.affineSpan_eq_of_ne hp₂ hp₃ hp₂p₃]
  rw [Collinear]; rw [Colli

Depends on / 依赖: Collinear, affineSpan_eq_of_ne, affineSpan_insert_affineSpan, conv_rhs, direction_affineSpan, h.affineSpan_eq_of_ne, insert, vectorSpan
-/
theorem Collinear.collinear_insert_iff_of_ne {s : Set P} (h : Collinear k s) {p₁ p₂ p₃ : P}
    (hp₂ : p₂ in s) (hp₃ : p₃ in s) (hp₂p₃ : p₂ != p₃) :
    Collinear k (insert p₁ s) ↔ Collinear k ({p₁, p₂, p₃} : Set P) := by
  have hv : vectorSpan k (insert p₁ s) = vectorSpan k ({p₁, p₂, p₃} : Set P) := by
    conv_rhs => rw [← direction_affineSpan, ← affineSpan_insert_affineSpan]
    rw [← direction_affineSpan]; rw [← affineSpan_insert_affineSpan]; rw [h.affineSpan_eq_of_ne hp₂ hp₃ hp₂p₃]
  rw [Collinear]; rw [Collinear]; rw [hv]

/--
theorem `collinear_insert_iff_of_mem_affineSpan` / 定理 `collinear_insert_iff_of_mem_affineSpan`

English:
theorem collinear_insert_iff_of_mem_affineSpan
  given: {s : Set P} {p : P} (h : p in affineSpan k s)
  proof: by
  rw [Collinear]; rw [Collinear]; rw [vectorSpan_insert_eq_vectorSpan h]

中文:
定理 collinear_insert_iff_of_mem_affineSpan
  条件: {s : Set P} {p : P} (h : p in affineSpan k s)
  证明: by
  rw [Collinear]; rw [Collinear]; rw [vectorSpan_insert_eq_vectorSpan h]

Depends on / 依赖: Collinear, vectorSpan_insert_eq_vectorSpan
-/
theorem collinear_insert_iff_of_mem_affineSpan {s : Set P} {p : P} (h : p in affineSpan k s) :
    Collinear k (insert p s) ↔ Collinear k s := by
  rw [Collinear]; rw [Collinear]; rw [vectorSpan_insert_eq_vectorSpan h]

/--
theorem `collinear_insert_of_mem_affineSpan_pair` / 定理 `collinear_insert_of_mem_affineSpan_pair`

English:
theorem collinear_insert_of_mem_affineSpan_pair
  given: {p₁ p₂ p₃ : P} (h : p₁ in line[k, p₂, p₃])
  proof: by
  rw [collinear_insert_iff_of_mem_affineSpan h]
  exact collinear_pair _ _ _

中文:
定理 collinear_insert_of_mem_affineSpan_pair
  条件: {p₁ p₂ p₃ : P} (h : p₁ in line[k, p₂, p₃])
  证明: by
  rw [collinear_insert_iff_of_mem_affineSpan h]
  exact collinear_pair _ _ _

Depends on / 依赖: collinear_insert_iff_of_mem_affineSpan, collinear_pair
-/
theorem collinear_insert_of_mem_affineSpan_pair {p₁ p₂ p₃ : P} (h : p₁ in line[k, p₂, p₃]) :
    Collinear k ({p₁, p₂, p₃} : Set P) := by
  rw [collinear_insert_iff_of_mem_affineSpan h]
  exact collinear_pair _ _ _

/--
theorem `collinear_insert_insert_of_mem_affineSpan_pair` / 定理 `collinear_insert_insert_of_mem_affineSpan_pair`

English:
theorem collinear_insert_insert_of_mem_affineSpan_pair
  statement: {p₁ p₂ p₃ p₄ : P} (h₁ : p₁ in line[k, p₃, p₄])
  proof: by
  rw [collinear_insert_iff_of_mem_affineSpan
      ((AffineSubspace.le_def' _ _).1 (affineSpan_mono k (Set.subset_insert _ _)) _ h₁)]; rw [collinear_insert_iff_of_mem_affineSpan h₂]
  exact collinear_pair _ _ _

中文:
定理 collinear_insert_insert_of_mem_affineSpan_pair
  结论: {p₁ p₂ p₃ p₄ : P} (h₁ : p₁ in line[k, p₃, p₄])
  证明: by
  rw [collinear_insert_iff_of_mem_affineSpan
      ((AffineSubspace.le_def' _ _).1 (affineSpan_mono k (Set.subset_insert _ _)) _ h₁)]; rw [collinear_insert_iff_of_mem_affineSpan h₂]
  exact collinear_pair _ _ _

Depends on / 依赖: AffineSubspace, AffineSubspace.le_def, Set.subset_insert, affineSpan_mono, collinear_insert_iff_of_mem_affineSpan, collinear_pair, le_def, subset_insert
-/
theorem collinear_insert_insert_of_mem_affineSpan_pair {p₁ p₂ p₃ p₄ : P} (h₁ : p₁ in line[k, p₃, p₄])
    (h₂ : p₂ in line[k, p₃, p₄]) : Collinear k ({p₁, p₂, p₃, p₄} : Set P) := by
  rw [collinear_insert_iff_of_mem_affineSpan
      ((AffineSubspace.le_def' _ _).1 (affineSpan_mono k (Set.subset_insert _ _)) _ h₁)]; rw [collinear_insert_iff_of_mem_affineSpan h₂]
  exact collinear_pair _ _ _

/--
theorem `collinear_insert_insert_insert_of_mem_affineSpan_pair` / 定理 `collinear_insert_insert_insert_of_mem_affineSpan_pair`

English:
theorem collinear_insert_insert_insert_of_mem_affineSpan_pair
  statement: {p₁ p₂ p₃ p₄ p₅ : P}
  proof: by
  rw [collinear_insert_iff_of_mem_affineSpan
      ((AffineSubspace.le_def' _ _).1
        (affineSpan_mono k ((Set.subset_insert _ _).trans (Set.subset_insert _ _))) _ h₁)]; rw [collinear_insert_iff_of_mem_affineSpan
      ((AffineSubspace.le_def' _ _).1 (affineSpan_mono k (Set.subset_insert _ _

中文:
定理 collinear_insert_insert_insert_of_mem_affineSpan_pair
  结论: {p₁ p₂ p₃ p₄ p₅ : P}
  证明: by
  rw [collinear_insert_iff_of_mem_affineSpan
      ((AffineSubspace.le_def' _ _).1
        (affineSpan_mono k ((Set.subset_insert _ _).trans (Set.subset_insert _ _))) _ h₁)]; rw [collinear_insert_iff_of_mem_affineSpan
      ((AffineSubspace.le_def' _ _).1 (affineSpan_mono k (Set.subset_insert _ _

Depends on / 依赖: AffineSubspace, AffineSubspace.le_def, Set.subset_insert, affineSpan_mono, collinear_insert_iff_of_mem_affineSpan, collinear_pair, le_def, subset_insert
-/
theorem collinear_insert_insert_insert_of_mem_affineSpan_pair {p₁ p₂ p₃ p₄ p₅ : P}
    (h₁ : p₁ in line[k, p₄, p₅]) (h₂ : p₂ in line[k, p₄, p₅]) (h₃ : p₃ in line[k, p₄, p₅]) :
    Collinear k ({p₁, p₂, p₃, p₄, p₅} : Set P) := by
  rw [collinear_insert_iff_of_mem_affineSpan
      ((AffineSubspace.le_def' _ _).1
        (affineSpan_mono k ((Set.subset_insert _ _).trans (Set.subset_insert _ _))) _ h₁)]; rw [collinear_insert_iff_of_mem_affineSpan
      ((AffineSubspace.le_def' _ _).1 (affineSpan_mono k (Set.subset_insert _ _)) _ h₂)]; rw [collinear_insert_iff_of_mem_affineSpan h₃]
  exact collinear_pair _ _ _

/--
theorem `collinear_insert_insert_insert_left_of_mem_affineSpan_pair` / 定理 `collinear_insert_insert_insert_left_of_mem_affineSpan_pair`

English:
theorem collinear_insert_insert_insert_left_of_mem_affineSpan_pair
  statement: {p₁ p₂ p₃ p₄ p₅ : P}
  proof: by
  refine (collinear_insert_insert_insert_of_mem_affineSpan_pair h₁ h₂ h₃).subset ?_
  gcongr; simp

中文:
定理 collinear_insert_insert_insert_left_of_mem_affineSpan_pair
  结论: {p₁ p₂ p₃ p₄ p₅ : P}
  证明: by
  refine (collinear_insert_insert_insert_of_mem_affineSpan_pair h₁ h₂ h₃).subset ?_
  gcongr; simp

Depends on / 依赖: collinear_insert_insert_insert_of_mem_affineSpan_pair, subset
-/
theorem collinear_insert_insert_insert_left_of_mem_affineSpan_pair {p₁ p₂ p₃ p₄ p₅ : P}
    (h₁ : p₁ in line[k, p₄, p₅]) (h₂ : p₂ in line[k, p₄, p₅]) (h₃ : p₃ in line[k, p₄, p₅]) :
    Collinear k ({p₁, p₂, p₃, p₄} : Set P) := by
  refine (collinear_insert_insert_insert_of_mem_affineSpan_pair h₁ h₂ h₃).subset ?_
  gcongr; simp

/--
theorem `collinear_triple_of_mem_affineSpan_pair` / 定理 `collinear_triple_of_mem_affineSpan_pair`

English:
theorem collinear_triple_of_mem_affineSpan_pair
  statement: {p₁ p₂ p₃ p₄ p₅ : P} (h₁ : p₁ in line[k, p₄, p₅])
  proof: by
  refine (collinear_insert_insert_insert_left_of_mem_affineSpan_pair h₁ h₂ h₃).subset ?_
  gcongr; simp

中文:
定理 collinear_triple_of_mem_affineSpan_pair
  结论: {p₁ p₂ p₃ p₄ p₅ : P} (h₁ : p₁ in line[k, p₄, p₅])
  证明: by
  refine (collinear_insert_insert_insert_left_of_mem_affineSpan_pair h₁ h₂ h₃).subset ?_
  gcongr; simp

Depends on / 依赖: collinear_insert_insert_insert_left_of_mem_affineSpan_pair, subset
-/
theorem collinear_triple_of_mem_affineSpan_pair {p₁ p₂ p₃ p₄ p₅ : P} (h₁ : p₁ in line[k, p₄, p₅])
    (h₂ : p₂ in line[k, p₄, p₅]) (h₃ : p₃ in line[k, p₄, p₅]) :
    Collinear k ({p₁, p₂, p₃} : Set P) := by
  refine (collinear_insert_insert_insert_left_of_mem_affineSpan_pair h₁ h₂ h₃).subset ?_
  gcongr; simp

/--
theorem `affineIndependent_of_affineIndependent_collinear_ne` / 定理 `affineIndependent_of_affineIndependent_collinear_ne`

English:
theorem affineIndependent_of_affineIndependent_collinear_ne
  statement: {p₁ p₂ p₃ p : P}
  proof: by
  rw [affineIndependent_iff_not_collinear_set]
  by_contra h
  have h1 : Collinear k {p₁, p₃, p₂, p} := by
    apply collinear_insert_insert_of_mem_affineSpan_pair
    · apply Collinear.mem_affineSpan_of_mem_of_ne h (by simp) (by simp) (by simp) hne
    · apply Collinear.mem_affineSpan_of_mem_of_

中文:
定理 affineIndependent_of_affineIndependent_collinear_ne
  结论: {p₁ p₂ p₃ p : P}
  证明: by
  rw [affineIndependent_iff_not_collinear_set]
  by_contra h
  have h1 : Collinear k {p₁, p₃, p₂, p} := by
    apply collinear_insert_insert_of_mem_affineSpan_pair
    · apply Collinear.mem_affineSpan_of_mem_of_ne h (by simp) (by simp) (by simp) hne
    · apply Collinear.mem_affineSpan_of_mem_of_

Depends on / 依赖: Collinear, Collinear.mem_affineSpan_of_mem_of_ne, affineIndependent_iff_not_collinear_set, collinear_insert_insert_of_mem_affineSpan_pair, h1.subset, mem_affineSpan_of_mem_of_ne, subset
-/
theorem affineIndependent_of_affineIndependent_collinear_ne {p₁ p₂ p₃ p : P}
    (ha : AffineIndependent k ![p₁, p₂, p₃]) (hcol : Collinear k {p₂, p₃, p}) (hne : p₂ != p) :
    AffineIndependent k ![p₁, p₂, p] := by
  rw [affineIndependent_iff_not_collinear_set]
  by_contra h
  have h1 : Collinear k {p₁, p₃, p₂, p} := by
    apply collinear_insert_insert_of_mem_affineSpan_pair
    · apply Collinear.mem_affineSpan_of_mem_of_ne h (by simp) (by simp) (by simp) hne
    · apply Collinear.mem_affineSpan_of_mem_of_ne hcol (by simp) (by simp) (by simp) hne
  have h2 : Collinear k {p₁, p₂, p₃} := h1.subset (by grind)
  rw [affineIndependent_iff_not_collinear_set] at ha
  exact ha h2

/--
theorem `affineIndependent_iff_affineIndependent_collinear_ne` / 定理 `affineIndependent_iff_affineIndependent_collinear_ne`

English:
theorem affineIndependent_iff_affineIndependent_collinear_ne
  statement: {p₁ p₂ p₃ p : P}
  proof: by
  refine ⟨fun h => affineIndependent_of_affineIndependent_collinear_ne h hcol hne2,
    fun h => affineIndependent_of_affineIndependent_collinear_ne h ?_ hne1⟩
  convert! hcol using 1
  aesop

中文:
定理 affineIndependent_iff_affineIndependent_collinear_ne
  结论: {p₁ p₂ p₃ p : P}
  证明: by
  refine ⟨fun h => affineIndependent_of_affineIndependent_collinear_ne h hcol hne2,
    fun h => affineIndependent_of_affineIndependent_collinear_ne h ?_ hne1⟩
  convert! hcol using 1
  aesop

Depends on / 依赖: affineIndependent_of_affineIndependent_collinear_ne, convert
-/
theorem affineIndependent_iff_affineIndependent_collinear_ne {p₁ p₂ p₃ p : P}
    (hcol : Collinear k {p₂, p, p₃}) (hne1 : p₂ != p) (hne2 : p₂ != p₃) :
    AffineIndependent k ![p₁, p₂, p] ↔ AffineIndependent k ![p₁, p₂, p₃] := by
  refine ⟨fun h => affineIndependent_of_affineIndependent_collinear_ne h hcol hne2,
    fun h => affineIndependent_of_affineIndependent_collinear_ne h ?_ hne1⟩
  convert! hcol using 1
  aesop

variable (k) in
/--
Definition of `Coplanar` / `Coplanar` 的定义

English:
definition Coplanar
  signature: (s : Set P)
  body: Module.rank k (vectorSpan k s) <= 2

中文:
定义 Coplanar
  签名: (s : Set P)
  定义体: Module.rank k (vectorSpan k s) <= 2

Depends on / 依赖: Module, Module.rank, vectorSpan
-/
def Coplanar (s : Set P) : Prop :=
  Module.rank k (vectorSpan k s) <= 2

/--
theorem `Coplanar.finiteDimensional_vectorSpan` / 定理 `Coplanar.finiteDimensional_vectorSpan`

English:
theorem Coplanar.finiteDimensional_vectorSpan
  given: {s : Set P} (h : Coplanar k s)
  proof: by
  refine IsNoetherian.iff_fg.1 (IsNoetherian.iff_rank_lt_aleph0.2 (lt_of_le_of_lt h ?_))
  exact Cardinal.lt_aleph0.2 ⟨2, rfl⟩

中文:
定理 Coplanar.finiteDimensional_vectorSpan
  条件: {s : Set P} (h : Coplanar k s)
  证明: by
  refine IsNoetherian.iff_fg.1 (IsNoetherian.iff_rank_lt_aleph0.2 (lt_of_le_of_lt h ?_))
  exact Cardinal.lt_aleph0.2 ⟨2, rfl⟩

Depends on / 依赖: Cardinal, Cardinal.lt_aleph0, IsNoetherian, IsNoetherian.iff_fg, IsNoetherian.iff_rank_lt_aleph0, iff_fg, iff_rank_lt_aleph0, lt_aleph0, lt_of_le_of_lt
-/
theorem Coplanar.finiteDimensional_vectorSpan {s : Set P} (h : Coplanar k s) :
    FiniteDimensional k (vectorSpan k s) := by
  refine IsNoetherian.iff_fg.1 (IsNoetherian.iff_rank_lt_aleph0.2 (lt_of_le_of_lt h ?_))
  exact Cardinal.lt_aleph0.2 ⟨2, rfl⟩

/--
theorem `Coplanar.finiteDimensional_direction_affineSpan` / 定理 `Coplanar.finiteDimensional_direction_affineSpan`

English:
theorem Coplanar.finiteDimensional_direction_affineSpan
  given: {s : Set P} (h : Coplanar k s)
  proof: (direction_affineSpan k s).symm ▸ h.finiteDimensional_vectorSpan

中文:
定理 Coplanar.finiteDimensional_direction_affineSpan
  条件: {s : Set P} (h : Coplanar k s)
  证明: (direction_affineSpan k s).symm ▸ h.finiteDimensional_vectorSpan

Depends on / 依赖: direction_affineSpan, finiteDimensional_vectorSpan, h.finiteDimensional_vectorSpan
-/
theorem Coplanar.finiteDimensional_direction_affineSpan {s : Set P} (h : Coplanar k s) :
    FiniteDimensional k (affineSpan k s).direction :=
  (direction_affineSpan k s).symm ▸ h.finiteDimensional_vectorSpan

/--
theorem `coplanar_iff_finrank_le_two` / 定理 `coplanar_iff_finrank_le_two`

English:
theorem coplanar_iff_finrank_le_two
  given: {s : Set P} [FiniteDimensional k (vectorSpan k s)]
  proof: by
  have h : Coplanar k s ↔ Module.rank k (vectorSpan k s) <= 2 := Iff.rfl
  rw [← finrank_eq_rank] at h
  exact mod_cast h

alias ⟨Coplanar.finrank_le_two, _⟩ := coplanar_iff_finrank_le_two

中文:
定理 coplanar_iff_finrank_le_two
  条件: {s : Set P} [FiniteDimensional k (vectorSpan k s)]
  证明: by
  have h : Coplanar k s ↔ Module.rank k (vectorSpan k s) <= 2 := Iff.rfl
  rw [← finrank_eq_rank] at h
  exact mod_cast h

alias ⟨Coplanar.finrank_le_two, _⟩ := coplanar_iff_finrank_le_two

Depends on / 依赖: Coplanar, Iff.rfl, Module, Module.rank, finiteSpanningSetsIn_volumeIoiPow_range_Iio, finrank_eq_rank, mod_cast, sigmaFinite, vectorSpan
-/
theorem coplanar_iff_finrank_le_two {s : Set P} [FiniteDimensional k (vectorSpan k s)] :
    Coplanar k s ↔ finrank k (vectorSpan k s) <= 2 := by
  have h : Coplanar k s ↔ Module.rank k (vectorSpan k s) <= 2 := Iff.rfl
  rw [← finrank_eq_rank] at h
  exact mod_cast h

alias ⟨Coplanar.finrank_le_two, _⟩ := coplanar_iff_finrank_le_two

/--
theorem `Coplanar.subset` / 定理 `Coplanar.subset`

English:
theorem Coplanar.subset
  given: {s₁ s₂ : Set P} (hs : s₁ subseteq s₂) (h : Coplanar k s₂)
  statement: Coplanar k s₁
  proof: (Submodule.rank_mono (vectorSpan_mono k hs)).trans h

中文:
定理 Coplanar.subset
  条件: {s₁ s₂ : Set P} (hs : s₁ subseteq s₂) (h : Coplanar k s₂)
  结论: Coplanar k s₁
  证明: (Submodule.rank_mono (vectorSpan_mono k hs)).trans h

Depends on / 依赖: Submodule, Submodule.rank_mono, rank_mono, vectorSpan_mono
-/
theorem Coplanar.subset {s₁ s₂ : Set P} (hs : s₁ subseteq s₂) (h : Coplanar k s₂) : Coplanar k s₁ :=
  (Submodule.rank_mono (vectorSpan_mono k hs)).trans h

/--
theorem `Collinear.coplanar` / 定理 `Collinear.coplanar`

English:
theorem Collinear.coplanar
  given: {s : Set P} (h : Collinear k s)
  statement: Coplanar k s
  proof: le_trans h one_le_two

中文:
定理 Collinear.coplanar
  条件: {s : Set P} (h : Collinear k s)
  结论: Coplanar k s
  证明: le_trans h one_le_two

Depends on / 依赖: le_trans, one_le_two
-/
theorem Collinear.coplanar {s : Set P} (h : Collinear k s) : Coplanar k s :=
  le_trans h one_le_two

variable (k) (P)

/--
theorem `coplanar_empty` / 定理 `coplanar_empty`

English:
theorem coplanar_empty
  statement: Coplanar k (∅ : Set P)
  proof: (collinear_empty k P).coplanar

中文:
定理 coplanar_empty
  结论: Coplanar k (∅ : Set P)
  证明: (collinear_empty k P).coplanar

Depends on / 依赖: collinear_empty, coplanar
-/
theorem coplanar_empty : Coplanar k (∅ : Set P) :=
  (collinear_empty k P).coplanar

variable {P}

/--
theorem `coplanar_singleton` / 定理 `coplanar_singleton`

English:
theorem coplanar_singleton
  given: (p : P)
  statement: Coplanar k ({p} : Set P)
  proof: (collinear_singleton k p).coplanar

中文:
定理 coplanar_singleton
  条件: (p : P)
  结论: Coplanar k ({p} : Set P)
  证明: (collinear_singleton k p).coplanar

Depends on / 依赖: collinear_singleton, coplanar
-/
theorem coplanar_singleton (p : P) : Coplanar k ({p} : Set P) :=
  (collinear_singleton k p).coplanar

/--
theorem `coplanar_pair` / 定理 `coplanar_pair`

English:
theorem coplanar_pair
  given: (p₁ p₂ : P)
  statement: Coplanar k ({p₁, p₂} : Set P)
  proof: (collinear_pair k p₁ p₂).coplanar

中文:
定理 coplanar_pair
  条件: (p₁ p₂ : P)
  结论: Coplanar k ({p₁, p₂} : Set P)
  证明: (collinear_pair k p₁ p₂).coplanar

Depends on / 依赖: collinear_pair, coplanar
-/
theorem coplanar_pair (p₁ p₂ : P) : Coplanar k ({p₁, p₂} : Set P) :=
  (collinear_pair k p₁ p₂).coplanar

variable {k}

/--
theorem `coplanar_insert_iff_of_mem_affineSpan` / 定理 `coplanar_insert_iff_of_mem_affineSpan`

English:
theorem coplanar_insert_iff_of_mem_affineSpan
  given: {s : Set P} {p : P} (h : p in affineSpan k s)
  proof: by
  rw [Coplanar]; rw [Coplanar]; rw [vectorSpan_insert_eq_vectorSpan h]

中文:
定理 coplanar_insert_iff_of_mem_affineSpan
  条件: {s : Set P} {p : P} (h : p in affineSpan k s)
  证明: by
  rw [Coplanar]; rw [Coplanar]; rw [vectorSpan_insert_eq_vectorSpan h]

Depends on / 依赖: Coplanar, vectorSpan_insert_eq_vectorSpan
-/
theorem coplanar_insert_iff_of_mem_affineSpan {s : Set P} {p : P} (h : p in affineSpan k s) :
    Coplanar k (insert p s) ↔ Coplanar k s := by
  rw [Coplanar]; rw [Coplanar]; rw [vectorSpan_insert_eq_vectorSpan h]

end AffineSpace'

section DivisionRing

variable {k : Type*} {V : Type*} {P : Type*}

open AffineSubspace Module Module

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AffineSpace V P]

/--
theorem `finrank_vectorSpan_insert_le` / 定理 `finrank_vectorSpan_insert_le`

English:
theorem finrank_vectorSpan_insert_le
  given: (s : AffineSubspace k P) (p : P)
  proof: by
  by_cases hf : FiniteDimensional k s.direction; swap
  · have hf' : ¬FiniteDimensional k (vectorSpan k (insert p (s : Set P))) := by
      intro h
      have h' : s.direction <= vectorSpan k (insert p (s : Set P)) := by
        conv_lhs => rw [← affineSpan_coe s, direction_affineSpan]
        ex

中文:
定理 finrank_vectorSpan_insert_le
  条件: (s : AffineSubspace k P) (p : P)
  证明: by
  by_cases hf : FiniteDimensional k s.direction; swap
  · have hf' : ¬FiniteDimensional k (vectorSpan k (insert p (s : Set P))) := by
      intro h
      have h' : s.direction <= vectorSpan k (insert p (s : Set P)) := by
        conv_lhs => rw [← affineSpan_coe s, direction_affineSpan]
        ex

Depends on / 依赖: FiniteDimensional, Set.subset_insert, Submodule, Submodule.finiteDimensional_of_le, affineSpan_coe, conv_lhs, direction, direction_affineS, direction_affineSpan, finiteDimensional_of_le, finrank_of_infinite_dimensional, insert, s.direction, subset_insert, vectorSpan, vectorSpan_mono, zero_add, zero_le_one
-/
theorem finrank_vectorSpan_insert_le (s : AffineSubspace k P) (p : P) :
    finrank k (vectorSpan k (insert p (s : Set P))) <= finrank k s.direction + 1 := by
  by_cases hf : FiniteDimensional k s.direction; swap
  · have hf' : ¬FiniteDimensional k (vectorSpan k (insert p (s : Set P))) := by
      intro h
      have h' : s.direction <= vectorSpan k (insert p (s : Set P)) := by
        conv_lhs => rw [← affineSpan_coe s, direction_affineSpan]
        exact vectorSpan_mono k (Set.subset_insert _ _)
      exact hf (Submodule.finiteDimensional_of_le h')
    rw [finrank_of_infinite_dimensional hf]; rw [finrank_of_infinite_dimensional hf']; rw [zero_add]
    exact zero_le_one
  rw [← direction_affineSpan]; rw [← affineSpan_insert_affineSpan]
  rcases (s : Set P).eq_empty_or_nonempty with (hs | ⟨p₀, hp₀⟩)
  · rw [coe_eq_bot_iff] at hs
    rw [hs]; rw [bot_coe]; rw [span_empty]; rw [bot_coe]; rw [direction_affineSpan]; rw [direction_bot]; rw [finrank_bot]; rw [zero_add]
    convert! zero_le_one' Nat
    rw [← finrank_bot k V]
    convert! rfl <;> simp
  · rw [affineSpan_coe, direction_affineSpan_insert hp₀, add_comm]
    refine (Submodule.finrank_add_le_finrank_add_finrank _ _).trans ?_
    gcongr
    refine finrank_le_one ⟨p -ᵥ p₀, Submodule.mem_span_singleton_self _⟩ fun v => ?_
    have h := v.property
    rw [Submodule.mem_span_singleton] at h
    rcases h with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    ext
    exact hc

variable (k) in
/--
theorem `finrank_vectorSpan_insert_le_set` / 定理 `finrank_vectorSpan_insert_le_set`

English:
theorem finrank_vectorSpan_insert_le_set
  given: (s : Set P) (p : P)
  proof: by
  rw [← direction_affineSpan]; rw [← affineSpan_insert_affineSpan]; rw [direction_affineSpan]; rw [← direction_affineSpan _ s]
  exact finrank_vectorSpan_insert_le ..

中文:
定理 finrank_vectorSpan_insert_le_set
  条件: (s : Set P) (p : P)
  证明: by
  rw [← direction_affineSpan]; rw [← affineSpan_insert_affineSpan]; rw [direction_affineSpan]; rw [← direction_affineSpan _ s]
  exact finrank_vectorSpan_insert_le ..

Depends on / 依赖: affineSpan_insert_affineSpan, direction_affineSpan, finrank_vectorSpan_insert_le
-/
theorem finrank_vectorSpan_insert_le_set (s : Set P) (p : P) :
    finrank k (vectorSpan k (insert p s)) <= finrank k (vectorSpan k s) + 1 := by
  rw [← direction_affineSpan]; rw [← affineSpan_insert_affineSpan]; rw [direction_affineSpan]; rw [← direction_affineSpan _ s]
  exact finrank_vectorSpan_insert_le ..

/--
theorem `Collinear.coplanar_insert` / 定理 `Collinear.coplanar_insert`

English:
theorem Collinear.coplanar_insert
  given: {s : Set P} (h : Collinear k s) (p : P)
  proof: by
  have : FiniteDimensional k { x // x in vectorSpan k s } := h.finiteDimensional_vectorSpan
  grw [coplanar_iff_finrank_le_two, finrank_vectorSpan_insert_le_set, h.finrank_le_one]

中文:
定理 Collinear.coplanar_insert
  条件: {s : Set P} (h : Collinear k s) (p : P)
  证明: by
  have : FiniteDimensional k { x // x in vectorSpan k s } := h.finiteDimensional_vectorSpan
  grw [coplanar_iff_finrank_le_two, finrank_vectorSpan_insert_le_set, h.finrank_le_one]

Depends on / 依赖: FiniteDimensional, coplanar_iff_finrank_le_two, finiteDimensional_vectorSpan, finrank_le_one, finrank_vectorSpan_insert_le_set, h.finiteDimensional_vectorSpan, h.finrank_le_one, vectorSpan
-/
theorem Collinear.coplanar_insert {s : Set P} (h : Collinear k s) (p : P) :
    Coplanar k (insert p s) := by
  have : FiniteDimensional k { x // x in vectorSpan k s } := h.finiteDimensional_vectorSpan
  grw [coplanar_iff_finrank_le_two, finrank_vectorSpan_insert_le_set, h.finrank_le_one]

/--
theorem `coplanar_of_finrank_eq_two` / 定理 `coplanar_of_finrank_eq_two`

English:
theorem coplanar_of_finrank_eq_two
  given: (s : Set P) (h : finrank k V = 2)
  statement: Coplanar k s
  proof: by
  have : FiniteDimensional k V := .of_finrank_eq_succ h
  rw [coplanar_iff_finrank_le_two]; rw [← h]
  exact Submodule.finrank_le _

中文:
定理 coplanar_of_finrank_eq_two
  条件: (s : Set P) (h : finrank k V = 2)
  结论: Coplanar k s
  证明: by
  have : FiniteDimensional k V := .of_finrank_eq_succ h
  rw [coplanar_iff_finrank_le_two]; rw [← h]
  exact Submodule.finrank_le _

Depends on / 依赖: FiniteDimensional, Submodule, Submodule.finrank_le, coplanar_iff_finrank_le_two, finrank_le, of_finrank_eq_succ
-/
theorem coplanar_of_finrank_eq_two (s : Set P) (h : finrank k V = 2) : Coplanar k s := by
  have : FiniteDimensional k V := .of_finrank_eq_succ h
  rw [coplanar_iff_finrank_le_two]; rw [← h]
  exact Submodule.finrank_le _

/--
theorem `coplanar_of_fact_finrank_eq_two` / 定理 `coplanar_of_fact_finrank_eq_two`

English:
theorem coplanar_of_fact_finrank_eq_two
  given: (s : Set P) [h : Fact (finrank k V = 2)]
  statement: Coplanar k s
  proof: coplanar_of_finrank_eq_two s h.out

中文:
定理 coplanar_of_fact_finrank_eq_two
  条件: (s : Set P) [h : Fact (finrank k V = 2)]
  结论: Coplanar k s
  证明: coplanar_of_finrank_eq_two s h.out

Depends on / 依赖: coplanar_of_finrank_eq_two, h.out
-/
theorem coplanar_of_fact_finrank_eq_two (s : Set P) [h : Fact (finrank k V = 2)] : Coplanar k s :=
  coplanar_of_finrank_eq_two s h.out

variable (k)

/--
theorem `coplanar_triple` / 定理 `coplanar_triple`

English:
theorem coplanar_triple
  given: (p₁ p₂ p₃ : P)
  statement: Coplanar k ({p₁, p₂, p₃} : Set P)
  proof: (collinear_pair k p₂ p₃).coplanar_insert p₁

中文:
定理 coplanar_triple
  条件: (p₁ p₂ p₃ : P)
  结论: Coplanar k ({p₁, p₂, p₃} : Set P)
  证明: (collinear_pair k p₂ p₃).coplanar_insert p₁

Depends on / 依赖: collinear_pair, coplanar_insert
-/
theorem coplanar_triple (p₁ p₂ p₃ : P) : Coplanar k ({p₁, p₂, p₃} : Set P) :=
  (collinear_pair k p₂ p₃).coplanar_insert p₁

/--
theorem `Affine.Simplex.collinear_point_centroid_faceOppositeCentroid` / 定理 `Affine.Simplex.collinear_point_centroid_faceOppositeCentroid`

English:
theorem Affine.Simplex.collinear_point_centroid_faceOppositeCentroid
  statement: [CharZero k] {n : Nat} [NeZero n]
  proof: by
  apply collinear_insert_of_mem_affineSpan_pair
  have h : s.points i = (-n : k) • (s.faceOppositeCentroid i -ᵥ s.centroid) +ᵥ s.centroid := by
    rw [← neg_vsub_eq_vsub_rev]; rw [neg_smul_neg]; rw [← point_vsub_centroid_eq_smul_vsub]; rw [vsub_vadd]
  rw [h]
  exact smul_vsub_vadd_mem_affineSpa

中文:
定理 Affine.Simplex.collinear_point_centroid_faceOppositeCentroid
  结论: [CharZero k] {n : 自然数} [NeZero n]
  证明: by
  apply collinear_insert_of_mem_affineSpan_pair
  have h : s.points i = (-n : k) • (s.faceOppositeCentroid i -ᵥ s.centroid) +ᵥ s.centroid := by
    rw [← neg_vsub_eq_vsub_rev]; rw [neg_smul_neg]; rw [← point_vsub_centroid_eq_smul_vsub]; rw [vsub_vadd]
  rw [h]
  exact smul_vsub_vadd_mem_affineSpa

Depends on / 依赖: centroid, collinear_insert_of_mem_affineSpan_pair, faceOppositeCentroid, neg_smul_neg, neg_vsub_eq_vsub_rev, point_vsub_centroid_eq_smul_vsub, points, s.centroid, s.faceOppositeCentroid, s.points, smul_vsub_vadd_mem_affineSpan_pair, vsub_vadd
-/
theorem Affine.Simplex.collinear_point_centroid_faceOppositeCentroid [CharZero k] {n : Nat} [NeZero n]
    (s : Simplex k P n) (i : Fin (n + 1)) :
    Collinear k {s.points i, s.centroid, s.faceOppositeCentroid i} := by
  apply collinear_insert_of_mem_affineSpan_pair
  have h : s.points i = (-n : k) • (s.faceOppositeCentroid i -ᵥ s.centroid) +ᵥ s.centroid := by
    rw [← neg_vsub_eq_vsub_rev]; rw [neg_smul_neg]; rw [← point_vsub_centroid_eq_smul_vsub]; rw [vsub_vadd]
  rw [h]
  exact smul_vsub_vadd_mem_affineSpan_pair _ _ _

end DivisionRing

namespace AffineBasis

universe u₁ u₂ u₃ u₄

variable {ι : Type u₁} {k : Type u₂} {V : Type u₃} {P : Type u₄}
variable [AddCommGroup V] [AffineSpace V P]

section DivisionRing

variable [DivisionRing k] [Module k V]

/--
theorem `finiteDimensional` / 定理 `finiteDimensional`

English:
theorem finiteDimensional
  given: [Finite ι] (b : AffineBasis ι k P)
  statement: FiniteDimensional k V
  proof: let ⟨i⟩ := b.nonempty
  (b.basisOf i).finiteDimensional_of_finite

中文:
定理 finiteDimensional
  条件: [Finite ι] (b : AffineBasis ι k P)
  结论: FiniteDimensional k V
  证明: let ⟨i⟩ := b.nonempty
  (b.basisOf i).finiteDimensional_of_finite
-/
protected theorem finiteDimensional [Finite ι] (b : AffineBasis ι k P) : FiniteDimensional k V :=
  let ⟨i⟩ := b.nonempty
  (b.basisOf i).finiteDimensional_of_finite

/--
theorem `finite` / 定理 `finite`

English:
theorem finite
  given: [FiniteDimensional k V] (b : AffineBasis ι k P)
  statement: Finite ι
  proof: finite_of_fin_dim_affineIndependent k b.ind

中文:
定理 finite
  条件: [FiniteDimensional k V] (b : AffineBasis ι k P)
  结论: Finite ι
  证明: finite_of_fin_dim_affineIndependent k b.ind
-/
protected theorem finite [FiniteDimensional k V] (b : AffineBasis ι k P) : Finite ι :=
  finite_of_fin_dim_affineIndependent k b.ind

/--
theorem `finite_set` / 定理 `finite_set`

English:
theorem finite_set
  given: [FiniteDimensional k V] {s : Set ι} (b : AffineBasis s k P)
  proof: finite_set_of_fin_dim_affineIndependent k b.ind

中文:
定理 finite_set
  条件: [FiniteDimensional k V] {s : Set ι} (b : AffineBasis s k P)
  证明: finite_set_of_fin_dim_affineIndependent k b.ind
-/
protected theorem finite_set [FiniteDimensional k V] {s : Set ι} (b : AffineBasis s k P) :
    s.Finite :=
  finite_set_of_fin_dim_affineIndependent k b.ind

/--
theorem `card_eq_finrank_add_one` / 定理 `card_eq_finrank_add_one`

English:
theorem card_eq_finrank_add_one
  given: [Fintype ι] (b : AffineBasis ι k P)
  proof: have : FiniteDimensional k V := b.finiteDimensional
  b.ind.affineSpan_eq_top_iff_card_eq_finrank_add_one.mp b.tot

中文:
定理 card_eq_finrank_add_one
  条件: [Fintype ι] (b : AffineBasis ι k P)
  证明: have : FiniteDimensional k V := b.finiteDimensional
  b.ind.affineSpan_eq_top_iff_card_eq_finrank_add_one.mp b.tot

Depends on / 依赖: FiniteDimensional, affineSpan_eq_top_iff_card_eq_finrank_add_one, b.finiteDimensional, b.ind.affineSpan_eq_top_iff_card_eq_finrank_add_one.mp, b.tot, finiteDimensional
-/
theorem card_eq_finrank_add_one [Fintype ι] (b : AffineBasis ι k P) :
    Fintype.card ι = Module.finrank k V + 1 :=
  have : FiniteDimensional k V := b.finiteDimensional
  b.ind.affineSpan_eq_top_iff_card_eq_finrank_add_one.mp b.tot

/--
theorem `exists_affineBasis_of_finiteDimensional` / 定理 `exists_affineBasis_of_finiteDimensional`

English:
theorem exists_affineBasis_of_finiteDimensional
  statement: [Fintype ι] [FiniteDimensional k V]
  proof: by
  obtain ⟨s, b, hb⟩ := AffineBasis.exists_affineBasis k V P
  lift s to Finset P using b.finite_set
refine ⟨b.reindex Fintype.equivOfCardEq ?_⟩
  rw [h]; rw [← b.card_eq_finrank_add_one]

中文:
定理 exists_affineBasis_of_finiteDimensional
  结论: [Fintype ι] [FiniteDimensional k V]
  证明: by
  obtain ⟨s, b, hb⟩ := AffineBasis.exists_affineBasis k V P
  lift s to Finset P using b.finite_set
refine ⟨b.reindex Fintype.equivOfCardEq ?_⟩
  rw [h]; rw [← b.card_eq_finrank_add_one]

Depends on / 依赖: AffineBasis, AffineBasis.exists_affineBasis, Finset, Fintype, Fintype.equivOfCardEq, b.card_eq_finrank_add_one, b.finite_set, b.reindex, card_eq_finrank_add_one, equivOfCardEq, exists_affineBasis, finite_set, reindex
-/
theorem exists_affineBasis_of_finiteDimensional [Fintype ι] [FiniteDimensional k V]
    (h : Fintype.card ι = Module.finrank k V + 1) : Nonempty (AffineBasis ι k P) := by
  obtain ⟨s, b, hb⟩ := AffineBasis.exists_affineBasis k V P
  lift s to Finset P using b.finite_set
refine ⟨b.reindex Fintype.equivOfCardEq ?_⟩
  rw [h]; rw [← b.card_eq_finrank_add_one]

end DivisionRing

end AffineBasis

namespace AffineMap

variable {R S V W P : Type*} [Ring R] [Ring S]
  [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V] [AddTorsor V P]
  [AddCommGroup W] [Module R W] [Module S W] [Module.Finite S W] [SMulCommClass R S W]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module.Finite S (P ->ᵃ[R] W)
  body: have ⟨p⟩ : Nonempty P := inferInstance
.equiv (AffineMap.toConstProdLinearMap S).symm ≪≫ₗ (AffineEquiv.vaddConst R p).congrLeftₗ S W

中文:
实例 :
  签名: Module.Finite S (P ->ᵃ[R] W)
  定义体: have ⟨p⟩ : Nonempty P := inferInstance
.equiv (AffineMap.toConstProdLinearMap S).symm ≪≫ₗ (AffineEquiv.vaddConst R p).congrLeftₗ S W

Depends on / 依赖: AffineEquiv, AffineEquiv.vaddConst, AffineMap, AffineMap.toConstProdLinearMap, Nonempty, toConstProdLinearMap, vaddConst
-/
instance : Module.Finite S (P ->ᵃ[R] W) :=
  have ⟨p⟩ : Nonempty P := inferInstance
.equiv (AffineMap.toConstProdLinearMap S).symm ≪≫ₗ (AffineEquiv.vaddConst R p).congrLeftₗ S W

/--
theorem `finrank_eq` / 定理 `finrank_eq`

English:
theorem finrank_eq
  given: [Module.Free S W] [StrongRankCondition R] [StrongRankCondition S]
  proof: calc
    _ = Module.finrank S (V ->ᵃ[R] W) :=
      have ⟨p⟩ : Nonempty P := inferInstance
.finrank_eq .symm.congrLeftₗ S W AffineEquiv.vaddConst R p
    _ = Module.finrank S (W × (V ->ₗ[R] W)) := (AffineMap.toConstProdLinearMap S).finrank_eq
    _ = (Module.finrank R V + 1) * Module.finrank S W := 

中文:
定理 finrank_eq
  条件: [Module.Free S W] [StrongRankCondition R] [StrongRankCondition S]
  证明: calc
    _ = Module.finrank S (V ->ᵃ[R] W) :=
      have ⟨p⟩ : Nonempty P := inferInstance
.finrank_eq .symm.congrLeftₗ S W AffineEquiv.vaddConst R p
    _ = Module.finrank S (W × (V ->ₗ[R] W)) := (AffineMap.toConstProdLinearMap S).finrank_eq
    _ = (Module.finrank R V + 1) * Module.finrank S W := 

Depends on / 依赖: AffineEquiv, AffineEquiv.vaddConst, AffineMap, AffineMap.toConstProdLinearMap, Module, Module.finrank, Module.finrank_linearMap, Module.finrank_prod, Nonempty, finrank, finrank_eq, finrank_linearMap, finrank_prod, symm.congrLeft, toConstProdLinearMap, vaddConst
-/
theorem finrank_eq [Module.Free S W] [StrongRankCondition R] [StrongRankCondition S] :
    Module.finrank S (P ->ᵃ[R] W) = (Module.finrank R V + 1) * Module.finrank S W :=
  calc
    _ = Module.finrank S (V ->ᵃ[R] W) :=
      have ⟨p⟩ : Nonempty P := inferInstance
.finrank_eq .symm.congrLeftₗ S W AffineEquiv.vaddConst R p
    _ = Module.finrank S (W × (V ->ₗ[R] W)) := (AffineMap.toConstProdLinearMap S).finrank_eq
    _ = (Module.finrank R V + 1) * Module.finrank S W := by
      rw [Module.finrank_prod]; rw [Module.finrank_linearMap]
      ring

end AffineMap
