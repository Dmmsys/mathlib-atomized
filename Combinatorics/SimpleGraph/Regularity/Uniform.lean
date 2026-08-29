/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Combinatorics.SimpleGraph.Density
public import Mathlib.Data.Nat.Cast.Order.Field
public import Mathlib.Order.Partition.Equipartition
public import Mathlib.SetTheory.Cardinal.Order

/-!
# Graph uniformity and uniform partitions

In this file we define uniformity of a pair of vertices in a graph and uniformity of a partition of
vertices of a graph. Both are also known as ε-regularity.

Finsets of vertices `s` and `t` are `ε`-uniform in a graph `G` if their edge density is at most
`ε`-far from the density of any big enough `s'` and `t'` where `s' ⊆ s`, `t' ⊆ t`.
The definition is pretty technical, but it amounts to the edges between `s` and `t` being "random"
The literature contains several definitions which are equivalent up to scaling `ε` by some constant
when the partition is equitable.

A partition `P` of the vertices is `ε`-uniform if the proportion of `ε`-uniform pairs of parts is
greater than `(1 - ε)`.

## Main declarations

* `SimpleGraph.IsUniform`: Graph uniformity of a pair of finsets of vertices.
* `SimpleGraph.nonuniformWitness`: `G.nonuniformWitness ε s t` and `G.nonuniformWitness ε t s`
  together witness the non-uniformity of `s` and `t`.
* `Finpartition.nonUniforms`: Nonuniform pairs of parts of a partition.
* `Finpartition.IsUniform`: Uniformity of a partition.
* `Finpartition.nonuniformWitnesses`: For each non-uniform pair of parts of a partition, pick
  witnesses of non-uniformity and dump them all together.

## References

[Yaël Dillies, Bhavik Mehta, *Formalising Szemerédi’s Regularity Lemma in Lean*][srl_itp]
-/

@[expose] public section


open Finset

variable {α 𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-! ### Graph uniformity -/


namespace SimpleGraph

variable (G : SimpleGraph α) [DecidableRel G.Adj] (ε : 𝕜) {s t : Finset α} {a b : α}

/--
Definition of `IsUniform` / `IsUniform` 的定义

English:
definition IsUniform
  signature: (s t : Finset α)
  body: forall ⦃s'⦄, s' subseteq s -> forall ⦃t'⦄, t' subseteq t -> (#s : 𝕜) * ε <= #s' ->
    (#t : 𝕜) * ε <= #t' -> |(G.edgeDensity s' t' : 𝕜) - (G.edgeDensity s t : 𝕜)| < ε
deriving Decidable

中文:
定义 是一致
  签名: (s t : 有限集 α)
  定义体: forall ⦃s'⦄, s' subseteq s -> forall ⦃t'⦄, t' subseteq t -> (#s : 𝕜) * ε <= #s' ->
    (#t : 𝕜) * ε <= #t' -> |(G.edgeDensity s' t' : 𝕜) - (G.edgeDensity s t : 𝕜)| < ε
deriving Decidable

Depends on / 依赖: G.edgeDensity, edgeDensity, subseteq
-/
def IsUniform (s t : Finset α) : Prop :=
  forall ⦃s'⦄, s' subseteq s -> forall ⦃t'⦄, t' subseteq t -> (#s : 𝕜) * ε <= #s' ->
    (#t : 𝕜) * ε <= #t' -> |(G.edgeDensity s' t' : 𝕜) - (G.edgeDensity s t : 𝕜)| < ε
deriving Decidable

variable {G ε}

/--
theorem `IsUniform.mono` / 定理 `IsUniform.mono`

English:
theorem IsUniform.mono
  given: {ε' : 𝕜} (h : ε <= ε') (hε : IsUniform G ε s t)
  statement: IsUniform G ε' s t
  proof: fun s' hs' t' ht' hs ht => by
  refine (hε hs' ht' (le_trans ?_ hs) (le_trans ?_ ht)).trans_le h <;> gcongr

omit [IsStrictOrderedRing 𝕜] in

中文:
定理 是一致.mono
  条件: {ε' : 𝕜} (h : ε <= ε') (hε : 是一致 G ε s t)
  结论: 是一致 G ε' s t
  证明: fun s' hs' t' ht' hs ht => by
  refine (hε hs' ht' (le_trans ?_ hs) (le_trans ?_ ht)).trans_le h <;> gcongr

omit [IsStrictOrderedRing 𝕜] in

Depends on / 依赖: le_trans, trans_le
-/
theorem IsUniform.mono {ε' : 𝕜} (h : ε <= ε') (hε : IsUniform G ε s t) : IsUniform G ε' s t :=
  fun s' hs' t' ht' hs ht => by
  refine (hε hs' ht' (le_trans ?_ hs) (le_trans ?_ ht)).trans_le h <;> gcongr

omit [IsStrictOrderedRing 𝕜] in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Std.Symm (IsUniform G ε)
  body: by
    rw [edgeDensity_comm _ t']; rw [edgeDensity_comm _ t]
    exact h hs' ht' hs ht

omit [IsStrictOrderedRing 𝕜] in

中文:
实例 :
  签名: Std.Symm (是一致 G ε)
  定义体: by
    rw [edgeDensity_comm _ t']; rw [edgeDensity_comm _ t]
    exact h hs' ht' hs ht

omit [IsStrictOrderedRing 𝕜] in

Depends on / 依赖: edgeDensity_comm
-/
instance : Std.Symm (IsUniform G ε) where
  symm s t h t' ht' s' hs' ht hs := by
    rw [edgeDensity_comm _ t']; rw [edgeDensity_comm _ t]
    exact h hs' ht' hs ht

omit [IsStrictOrderedRing 𝕜] in
/--
theorem `IsUniform.symm` / 定理 `IsUniform.symm`

English:
theorem IsUniform.symm
  statement: IsUniform G ε s t -> IsUniform G ε t s
  proof: symm_of _

中文:
定理 是一致.symm
  结论: 是一致 G ε s t -> 是一致 G ε t s
  证明: symm_of _

Depends on / 依赖: symm_of
-/
theorem IsUniform.symm : IsUniform G ε s t -> IsUniform G ε t s :=
  symm_of _

variable (G)

omit [IsStrictOrderedRing 𝕜] in
/--
theorem `isUniform_comm` / 定理 `isUniform_comm`

English:
theorem isUniform_comm
  statement: IsUniform G ε s t ↔ IsUniform G ε t s
  proof: ⟨symm_of _, symm_of _⟩

中文:
定理 isUniform_comm
  结论: 是一致 G ε s t ↔ 是一致 G ε t s
  证明: ⟨symm_of _, symm_of _⟩

Depends on / 依赖: mem_singleton_self, symm_of
-/
theorem isUniform_comm : IsUniform G ε s t ↔ IsUniform G ε t s :=
  ⟨symm_of _, symm_of _⟩

/--
lemma `isUniform_one` / 引理 `isUniform_one`

English:
lemma isUniform_one
  statement: G.IsUniform (1 : 𝕜) s t
  proof: by
  intro s' hs' t' ht' hs ht
  rw [mul_one] at hs ht
  rw [eq_of_subset_of_card_le hs' (Nat.cast_le.1 hs)]; rw [eq_of_subset_of_card_le ht' (Nat.cast_le.1 ht)]; rw [sub_self]; rw [abs_zero]
  exact zero_lt_one

中文:
引理 isUniform_one
  结论: G.是一致 (1 : 𝕜) s t
  证明: by
  intro s' hs' t' ht' hs ht
  rw [mul_one] at hs ht
  rw [eq_of_subset_of_card_le hs' (Nat.cast_le.1 hs)]; rw [eq_of_subset_of_card_le ht' (Nat.cast_le.1 ht)]; rw [sub_self]; rw [abs_zero]
  exact zero_lt_one

Depends on / 依赖: Nat.cast_le, abs_zero, cast_le, eq_of_subset_of_card_le, mul_one, sub_self, zero_lt_one
-/
lemma isUniform_one : G.IsUniform (1 : 𝕜) s t := by
  intro s' hs' t' ht' hs ht
  rw [mul_one] at hs ht
  rw [eq_of_subset_of_card_le hs' (Nat.cast_le.1 hs)]; rw [eq_of_subset_of_card_le ht' (Nat.cast_le.1 ht)]; rw [sub_self]; rw [abs_zero]
  exact zero_lt_one

variable {G}

/--
lemma `IsUniform.pos` / 引理 `IsUniform.pos`

English:
lemma IsUniform.pos
  given: (hG : G.IsUniform ε s t)
  statement: 0 < ε
  proof: not_le.1 fun hε => (hε.trans <| abs_nonneg _).not_gt hG (empty_subset _) (empty_subset _)
    (by simpa using mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hε)
    (by simpa using mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hε)

中文:
引理 是一致.pos
  条件: (hG : G.是一致 ε s t)
  结论: 0 < ε
  证明: not_le.1 fun hε => (hε.trans <| abs_nonneg _).not_gt hG (empty_subset _) (empty_subset _)
    (by simpa using mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hε)
    (by simpa using mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hε)

Depends on / 依赖: Nat.cast_nonneg, abs_nonneg, cast_nonneg, empty_subset, mul_nonpos_of_nonneg_of_nonpos, not_gt, not_le
-/
lemma IsUniform.pos (hG : G.IsUniform ε s t) : 0 < ε :=
not_le.1 fun hε => (hε.trans <| abs_nonneg _).not_gt hG (empty_subset _) (empty_subset _)
    (by simpa using mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hε)
    (by simpa using mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hε)

/--
lemma `isUniform_singleton` / 引理 `isUniform_singleton`

English:
lemma isUniform_singleton
  statement: G.IsUniform ε {a} {b} ↔ 0 < ε
  proof: by
  refine ⟨IsUniform.pos, fun hε s' hs' t' ht' hs ht => ?_⟩
  rw [card_singleton]; rw [Nat.cast_one]; rw [one_mul] at hs ht
  obtain rfl | rfl := Finset.subset_singleton_iff.1 hs'
  · replace hs : ε <= 0 := by simpa using hs
    exact (hε.not_ge hs).elim
  obtain rfl | rfl := Finset.subset_singleton_iff.1 ht'
  · replace ht : ε <= 0 := by simpa using ht
    exact (hε.not_ge ht).elim
  · rwa [sub_self, abs_zero]

中文:
引理 isUniform_singleton
  结论: G.是一致 ε {a} {b} ↔ 0 < ε
  证明: by
  refine ⟨IsUniform.pos, fun hε s' hs' t' ht' hs ht => ?_⟩
  rw [card_singleton]; rw [Nat.cast_one]; rw [one_mul] at hs ht
  obtain rfl | rfl := Finset.subset_singleton_iff.1 hs'
  · replace hs : ε <= 0 := by simpa using hs
    exact (hε.not_ge hs).elim
  obtain rfl | rfl := Finset.subset_singleton_iff.1 ht'
  · replace ht : ε <= 0 := by simpa using ht
    exact (hε.not_ge ht).elim
  · rwa [sub_self, abs_zero]
-/
@[simp] lemma isUniform_singleton : G.IsUniform ε {a} {b} ↔ 0 < ε := by
  refine ⟨IsUniform.pos, fun hε s' hs' t' ht' hs ht => ?_⟩
  rw [card_singleton]; rw [Nat.cast_one]; rw [one_mul] at hs ht
  obtain rfl | rfl := Finset.subset_singleton_iff.1 hs'
  · replace hs : ε <= 0 := by simpa using hs
    exact (hε.not_ge hs).elim
  obtain rfl | rfl := Finset.subset_singleton_iff.1 ht'
  · replace ht : ε <= 0 := by simpa using ht
    exact (hε.not_ge ht).elim
  · rwa [sub_self, abs_zero]

/--
theorem `not_isUniform_zero` / 定理 `not_isUniform_zero`

English:
theorem not_isUniform_zero
  statement: ¬G.IsUniform (0 : 𝕜) s t
  proof: fun h =>
(abs_nonneg _).not_gt h (empty_subset _) (empty_subset _) (by simp) (by simp)

中文:
定理 not_isUniform_zero
  结论: ¬G.是一致 (0 : 𝕜) s t
  证明: fun h =>
(abs_nonneg _).not_gt h (empty_subset _) (empty_subset _) (by simp) (by simp)
-/
theorem not_isUniform_zero : ¬G.IsUniform (0 : 𝕜) s t := fun h =>
(abs_nonneg _).not_gt h (empty_subset _) (empty_subset _) (by simp) (by simp)

/--
theorem `not_isUniform_iff` / 定理 `not_isUniform_iff`

English:
theorem not_isUniform_iff
  proof: by
  unfold IsUniform
  simp only [not_forall, not_lt, exists_prop, Rat.cast_abs, Rat.cast_sub]

中文:
定理 not_isUniform_iff
  证明: by
  unfold IsUniform
  simp only [not_forall, not_lt, exists_prop, Rat.cast_abs, Rat.cast_sub]

Depends on / 依赖: IsUniform, Rat.cast_abs, Rat.cast_sub, cast_abs, cast_sub, exists_prop, not_forall, not_lt
-/
theorem not_isUniform_iff :
    ¬G.IsUniform ε s t ↔ exists s', s' subseteq s ∧ exists t', t' subseteq t ∧ #s * ε <= #s' ∧
      #t * ε <= #t' ∧ ε <= |G.edgeDensity s' t' - G.edgeDensity s t| := by
  unfold IsUniform
  simp only [not_forall, not_lt, exists_prop, Rat.cast_abs, Rat.cast_sub]

variable (G)

/--
Definition of `nonuniformWitnesses` / `nonuniformWitnesses` 的定义

English:
definition nonuniformWitnesses
  signature: (ε : 𝕜) (s t : Finset α)
  body: if h : ¬G.IsUniform ε s t then
    ((not_isUniform_iff.1 h).choose, (not_isUniform_iff.1 h).choose_spec.2.choose)
  else (s, t)

中文:
定义 nonuniformWitnesses
  签名: (ε : 𝕜) (s t : 有限集 α)
  定义体: if h : ¬G.IsUniform ε s t then
    ((not_isUniform_iff.1 h).choose, (not_isUniform_iff.1 h).choose_spec.2.choose)
  else (s, t)

Depends on / 依赖: G.IsUniform, IsUniform, choose_spec, not_isUniform_iff
-/
noncomputable def nonuniformWitnesses (ε : 𝕜) (s t : Finset α) : Finset α × Finset α :=
  if h : ¬G.IsUniform ε s t then
    ((not_isUniform_iff.1 h).choose, (not_isUniform_iff.1 h).choose_spec.2.choose)
  else (s, t)

/--
theorem `left_nonuniformWitnesses_subset` / 定理 `left_nonuniformWitnesses_subset`

English:
theorem left_nonuniformWitnesses_subset
  given: (h : ¬G.IsUniform ε s t)
  proof: by
  rw [nonuniformWitnesses]; rw [dif_pos h]
  exact (not_isUniform_iff.1 h).choose_spec.1

中文:
定理 left_nonuniformWitnesses_subset
  条件: (h : ¬G.是一致 ε s t)
  证明: by
  rw [nonuniformWitnesses]; rw [dif_pos h]
  exact (not_isUniform_iff.1 h).choose_spec.1

Depends on / 依赖: choose_spec, dif_pos, nonuniformWitnesses, not_isUniform_iff
-/
theorem left_nonuniformWitnesses_subset (h : ¬G.IsUniform ε s t) :
    (G.nonuniformWitnesses ε s t).1 subseteq s := by
  rw [nonuniformWitnesses]; rw [dif_pos h]
  exact (not_isUniform_iff.1 h).choose_spec.1

/--
theorem `left_nonuniformWitnesses_card` / 定理 `left_nonuniformWitnesses_card`

English:
theorem left_nonuniformWitnesses_card
  given: (h : ¬G.IsUniform ε s t)
  proof: by
  rw [nonuniformWitnesses]; rw [dif_pos h]
  exact (not_isUniform_iff.1 h).choose_spec.2.choose_spec.2.1

中文:
定理 left_nonuniformWitnesses_card
  条件: (h : ¬G.是一致 ε s t)
  证明: by
  rw [nonuniformWitnesses]; rw [dif_pos h]
  exact (not_isUniform_iff.1 h).choose_spec.2.choose_spec.2.1

Depends on / 依赖: choose_spec, dif_pos, nonuniformWitnesses, not_isUniform_iff
-/
theorem left_nonuniformWitnesses_card (h : ¬G.IsUniform ε s t) :
    #s * ε <= #(G.nonuniformWitnesses ε s t).1 := by
  rw [nonuniformWitnesses]; rw [dif_pos h]
  exact (not_isUniform_iff.1 h).choose_spec.2.choose_spec.2.1

/--
theorem `right_nonuniformWitnesses_subset` / 定理 `right_nonuniformWitnesses_subset`

English:
theorem right_nonuniformWitnesses_subset
  given: (h : ¬G.IsUniform ε s t)
  proof: by
  rw [nonuniformWitnesses]; rw [dif_pos h]
  exact (not_isUniform_iff.1 h).choose_spec.2.choose_spec.1

中文:
定理 right_nonuniformWitnesses_subset
  条件: (h : ¬G.是一致 ε s t)
  证明: by
  rw [nonuniformWitnesses]; rw [dif_pos h]
  exact (not_isUniform_iff.1 h).choose_spec.2.choose_spec.1

Depends on / 依赖: choose_spec, dif_pos, nonuniformWitnesses, not_isUniform_iff
-/
theorem right_nonuniformWitnesses_subset (h : ¬G.IsUniform ε s t) :
    (G.nonuniformWitnesses ε s t).2 subseteq t := by
  rw [nonuniformWitnesses]; rw [dif_pos h]
  exact (not_isUniform_iff.1 h).choose_spec.2.choose_spec.1

/--
theorem `right_nonuniformWitnesses_card` / 定理 `right_nonuniformWitnesses_card`

English:
theorem right_nonuniformWitnesses_card
  given: (h : ¬G.IsUniform ε s t)
  proof: by
  rw [nonuniformWitnesses]; rw [dif_pos h]
  exact (not_isUniform_iff.1 h).choose_spec.2.choose_spec.2.2.1

中文:
定理 right_nonuniformWitnesses_card
  条件: (h : ¬G.是一致 ε s t)
  证明: by
  rw [nonuniformWitnesses]; rw [dif_pos h]
  exact (not_isUniform_iff.1 h).choose_spec.2.choose_spec.2.2.1

Depends on / 依赖: choose_spec, dif_pos, nonuniformWitnesses, not_isUniform_iff
-/
theorem right_nonuniformWitnesses_card (h : ¬G.IsUniform ε s t) :
    #t * ε <= #(G.nonuniformWitnesses ε s t).2 := by
  rw [nonuniformWitnesses]; rw [dif_pos h]
  exact (not_isUniform_iff.1 h).choose_spec.2.choose_spec.2.2.1

/--
theorem `nonuniformWitnesses_spec` / 定理 `nonuniformWitnesses_spec`

English:
theorem nonuniformWitnesses_spec
  given: (h : ¬G.IsUniform ε s t)
  proof: by
  rw [nonuniformWitnesses]; rw [dif_pos h]
  exact (not_isUniform_iff.1 h).choose_spec.2.choose_spec.2.2.2

中文:
定理 nonuniformWitnesses_spec
  条件: (h : ¬G.是一致 ε s t)
  证明: by
  rw [nonuniformWitnesses]; rw [dif_pos h]
  exact (not_isUniform_iff.1 h).choose_spec.2.choose_spec.2.2.2

Depends on / 依赖: choose_spec, dif_pos, nonuniformWitnesses, not_isUniform_iff
-/
theorem nonuniformWitnesses_spec (h : ¬G.IsUniform ε s t) :
    ε <=
      |G.edgeDensity (G.nonuniformWitnesses ε s t).1 (G.nonuniformWitnesses ε s t).2 -
          G.edgeDensity s t| := by
  rw [nonuniformWitnesses]; rw [dif_pos h]
  exact (not_isUniform_iff.1 h).choose_spec.2.choose_spec.2.2.2

open scoped Classical in
/--
Definition of `nonuniformWitness` / `nonuniformWitness` 的定义

English:
definition nonuniformWitness
  signature: (ε : 𝕜) (s t : Finset α)
  body: if WellOrderingRel s t then (G.nonuniformWitnesses ε s t).1 else (G.nonuniformWitnesses ε t s).2

中文:
定义 nonuniformWitness
  签名: (ε : 𝕜) (s t : 有限集 α)
  定义体: if WellOrderingRel s t then (G.nonuniformWitnesses ε s t).1 else (G.nonuniformWitnesses ε t s).2

Depends on / 依赖: G.nonuniformWitnesses, WellOrderingRel, nonuniformWitnesses
-/
noncomputable def nonuniformWitness (ε : 𝕜) (s t : Finset α) : Finset α :=
  if WellOrderingRel s t then (G.nonuniformWitnesses ε s t).1 else (G.nonuniformWitnesses ε t s).2

/--
theorem `nonuniformWitness_subset` / 定理 `nonuniformWitness_subset`

English:
theorem nonuniformWitness_subset
  given: (h : ¬G.IsUniform ε s t)
  statement: G.nonuniformWitness ε s t subseteq s
  proof: by
  unfold nonuniformWitness
  split_ifs
  · exact G.left_nonuniformWitnesses_subset h
  · exact G.right_nonuniformWitnesses_subset fun i => h i.symm

中文:
定理 nonuniformWitness_subset
  条件: (h : ¬G.是一致 ε s t)
  结论: G.nonuniformWitness ε s t subseteq s
  证明: by
  unfold nonuniformWitness
  split_ifs
  · exact G.left_nonuniformWitnesses_subset h
  · exact G.right_nonuniformWitnesses_subset fun i => h i.symm

Depends on / 依赖: G.left_nonuniformWitnesses_subset, G.right_nonuniformWitnesses_subset, i.symm, left_nonuniformWitnesses_subset, nonuniformWitness, right_nonuniformWitnesses_subset, split_ifs
-/
theorem nonuniformWitness_subset (h : ¬G.IsUniform ε s t) : G.nonuniformWitness ε s t subseteq s := by
  unfold nonuniformWitness
  split_ifs
  · exact G.left_nonuniformWitnesses_subset h
  · exact G.right_nonuniformWitnesses_subset fun i => h i.symm

/--
theorem `le_card_nonuniformWitness` / 定理 `le_card_nonuniformWitness`

English:
theorem le_card_nonuniformWitness
  given: (h : ¬G.IsUniform ε s t)
  proof: by
  unfold nonuniformWitness
  split_ifs
  · exact G.left_nonuniformWitnesses_card h
  · exact G.right_nonuniformWitnesses_card fun i => h i.symm

中文:
定理 le_card_nonuniformWitness
  条件: (h : ¬G.是一致 ε s t)
  证明: by
  unfold nonuniformWitness
  split_ifs
  · exact G.left_nonuniformWitnesses_card h
  · exact G.right_nonuniformWitnesses_card fun i => h i.symm

Depends on / 依赖: G.left_nonuniformWitnesses_card, G.right_nonuniformWitnesses_card, i.symm, left_nonuniformWitnesses_card, nonuniformWitness, right_nonuniformWitnesses_card, split_ifs
-/
theorem le_card_nonuniformWitness (h : ¬G.IsUniform ε s t) :
    #s * ε <= #(G.nonuniformWitness ε s t) := by
  unfold nonuniformWitness
  split_ifs
  · exact G.left_nonuniformWitnesses_card h
  · exact G.right_nonuniformWitnesses_card fun i => h i.symm

/--
theorem `nonuniformWitness_spec` / 定理 `nonuniformWitness_spec`

English:
theorem nonuniformWitness_spec
  given: (h₁ : s != t) (h₂ : ¬G.IsUniform ε s t)
  statement: ε <= |G.edgeDensity
  proof: by
  unfold nonuniformWitness
  rcases trichotomous_of WellOrderingRel s t with (lt | rfl | gt)
  · rw [if_pos lt, if_neg (asymm lt)]
    exact G.nonuniformWitnesses_spec h₂
  · cases h₁ rfl
  · rw [if_neg (asymm gt), if_pos gt, edgeDensity_comm, edgeDensity_comm _ s]
    apply G.nonuniformWitnesses_spec fun i => h₂ i.symm

中文:
定理 nonuniformWitness_spec
  条件: (h₁ : s != t) (h₂ : ¬G.是一致 ε s t)
  结论: ε <= |G.edgeDensity
  证明: by
  unfold nonuniformWitness
  rcases trichotomous_of WellOrderingRel s t with (lt | rfl | gt)
  · rw [if_pos lt, if_neg (asymm lt)]
    exact G.nonuniformWitnesses_spec h₂
  · cases h₁ rfl
  · rw [if_neg (asymm gt), if_pos gt, edgeDensity_comm, edgeDensity_comm _ s]
    apply G.nonuniformWitnesses_spec fun i => h₂ i.symm

Depends on / 依赖: G.nonuniformWitnesses_spec, WellOrderingRel, edgeDensity_comm, i.symm, if_neg, if_pos, nonuniformWitness, nonuniformWitnesses_spec, trichotomous_of
-/
theorem nonuniformWitness_spec (h₁ : s != t) (h₂ : ¬G.IsUniform ε s t) : ε <= |G.edgeDensity
    (G.nonuniformWitness ε s t) (G.nonuniformWitness ε t s) - G.edgeDensity s t| := by
  unfold nonuniformWitness
  rcases trichotomous_of WellOrderingRel s t with (lt | rfl | gt)
  · rw [if_pos lt, if_neg (asymm lt)]
    exact G.nonuniformWitnesses_spec h₂
  · cases h₁ rfl
  · rw [if_neg (asymm gt), if_pos gt, edgeDensity_comm, edgeDensity_comm _ s]
    apply G.nonuniformWitnesses_spec fun i => h₂ i.symm

end SimpleGraph

/-! ### Uniform partitions -/


variable [DecidableEq α] {A : Finset α} (P : Finpartition A) (G : SimpleGraph α)
  [DecidableRel G.Adj] {ε δ : 𝕜} {u v : Finset α}

namespace Finpartition

/--
Definition of `sparsePairs` / `sparsePairs` 的定义

English:
definition sparsePairs
  signature: (ε : 𝕜)
  body: P.parts.offDiag.filter fun (u, v) => G.edgeDensity u v < ε

omit [IsStrictOrderedRing 𝕜] in
@[simp]

中文:
定义 sparsePairs
  签名: (ε : 𝕜)
  定义体: P.parts.offDiag.filter fun (u, v) => G.edgeDensity u v < ε

omit [IsStrictOrderedRing 𝕜] in
@[simp]

Depends on / 依赖: G.edgeDensity, P.parts.offDiag.filter, edgeDensity, filter, offDiag
-/
def sparsePairs (ε : 𝕜) : Finset (Finset α × Finset α) :=
  P.parts.offDiag.filter fun (u, v) => G.edgeDensity u v < ε

omit [IsStrictOrderedRing 𝕜] in
@[simp]
/--
lemma `mk_mem_sparsePairs` / 引理 `mk_mem_sparsePairs`

English:
lemma mk_mem_sparsePairs
  given: (u v : Finset α) (ε : 𝕜)
  proof: by
  rw [sparsePairs]; rw [mem_filter]; rw [mem_offDiag]; rw [and_assoc]; rw [and_assoc]

omit [IsStrictOrderedRing 𝕜] in

中文:
引理 mk_mem_sparsePairs
  条件: (u v : 有限集 α) (ε : 𝕜)
  证明: by
  rw [sparsePairs]; rw [mem_filter]; rw [mem_offDiag]; rw [and_assoc]; rw [and_assoc]

omit [IsStrictOrderedRing 𝕜] in

Depends on / 依赖: and_assoc, mem_filter, mem_offDiag, sparsePairs
-/
lemma mk_mem_sparsePairs (u v : Finset α) (ε : 𝕜) :
    (u, v) in P.sparsePairs G ε ↔ u in P.parts ∧ v in P.parts ∧ u != v ∧ G.edgeDensity u v < ε := by
  rw [sparsePairs]; rw [mem_filter]; rw [mem_offDiag]; rw [and_assoc]; rw [and_assoc]

omit [IsStrictOrderedRing 𝕜] in
/--
lemma `sparsePairs_mono` / 引理 `sparsePairs_mono`

English:
lemma sparsePairs_mono
  given: {ε ε' : 𝕜} (h : ε <= ε')
  statement: P.sparsePairs G ε subseteq P.sparsePairs G ε'
  proof: monotone_filter_right _ fun _ _ => h.trans_lt'

中文:
引理 sparsePairs_mono
  条件: {ε ε' : 𝕜} (h : ε <= ε')
  结论: P.sparsePairs G ε subseteq P.sparsePairs G ε'
  证明: monotone_filter_right _ fun _ _ => h.trans_lt'

Depends on / 依赖: h.trans_lt, monotone_filter_right, trans_lt
-/
lemma sparsePairs_mono {ε ε' : 𝕜} (h : ε <= ε') : P.sparsePairs G ε subseteq P.sparsePairs G ε' :=
  monotone_filter_right _ fun _ _ => h.trans_lt'

/--
Definition of `nonUniforms` / `nonUniforms` 的定义

English:
definition nonUniforms
  signature: (ε : 𝕜)
  body: P.parts.offDiag.filter fun (u, v) => ¬G.IsUniform ε u v

omit [IsStrictOrderedRing 𝕜] in

中文:
定义 nonUniforms
  签名: (ε : 𝕜)
  定义体: P.parts.offDiag.filter fun (u, v) => ¬G.IsUniform ε u v

omit [IsStrictOrderedRing 𝕜] in

Depends on / 依赖: G.IsUniform, IsUniform, P.parts.offDiag.filter, filter, offDiag
-/
def nonUniforms (ε : 𝕜) : Finset (Finset α × Finset α) :=
  P.parts.offDiag.filter fun (u, v) => ¬G.IsUniform ε u v

omit [IsStrictOrderedRing 𝕜] in
/--
lemma `mk_mem_nonUniforms` / 引理 `mk_mem_nonUniforms`

English:
lemma mk_mem_nonUniforms
  proof: by
  rw [nonUniforms]; rw [mem_filter]; rw [mem_offDiag]; rw [and_assoc]; rw [and_assoc]

中文:
引理 mk_mem_nonUniforms
  证明: by
  rw [nonUniforms]; rw [mem_filter]; rw [mem_offDiag]; rw [and_assoc]; rw [and_assoc]
-/
@[simp] lemma mk_mem_nonUniforms :
    (u, v) in P.nonUniforms G ε ↔ u in P.parts ∧ v in P.parts ∧ u != v ∧ ¬G.IsUniform ε u v := by
  rw [nonUniforms]; rw [mem_filter]; rw [mem_offDiag]; rw [and_assoc]; rw [and_assoc]

/--
theorem `nonUniforms_mono` / 定理 `nonUniforms_mono`

English:
theorem nonUniforms_mono
  given: {ε ε' : 𝕜} (h : ε <= ε')
  statement: P.nonUniforms G ε' subseteq P.nonUniforms G ε
  proof: monotone_filter_right _ fun _ _ => mt SimpleGraph.IsUniform.mono h

中文:
定理 nonUniforms_mono
  条件: {ε ε' : 𝕜} (h : ε <= ε')
  结论: P.nonUniforms G ε' subseteq P.nonUniforms G ε
  证明: monotone_filter_right _ fun _ _ => mt SimpleGraph.IsUniform.mono h

Depends on / 依赖: IsUniform, SimpleGraph, SimpleGraph.IsUniform.mono, monotone_filter_right
-/
theorem nonUniforms_mono {ε ε' : 𝕜} (h : ε <= ε') : P.nonUniforms G ε' subseteq P.nonUniforms G ε :=
monotone_filter_right _ fun _ _ => mt SimpleGraph.IsUniform.mono h

/--
theorem `nonUniforms_bot` / 定理 `nonUniforms_bot`

English:
theorem nonUniforms_bot
  given: (hε : 0 < ε)
  statement: (⊥ : Finpartition A).nonUniforms G ε = ∅
  proof: by
  rw [eq_empty_iff_forall_notMem]
  rintro ⟨u, v⟩
  simp only [mk_mem_nonUniforms, parts_bot, mem_map, not_and,
    Classical.not_not, exists_imp]; dsimp
  rintro x ⟨_, rfl⟩ y ⟨_, rfl⟩ _
  rwa [SimpleGraph.isUniform_singleton]

中文:
定理 nonUniforms_bot
  条件: (hε : 0 < ε)
  结论: (⊥ : 有限分拆 A).nonUniforms G ε = ∅
  证明: by
  rw [eq_empty_iff_forall_notMem]
  rintro ⟨u, v⟩
  simp only [mk_mem_nonUniforms, parts_bot, mem_map, not_and,
    Classical.not_not, exists_imp]; dsimp
  rintro x ⟨_, rfl⟩ y ⟨_, rfl⟩ _
  rwa [SimpleGraph.isUniform_singleton]

Depends on / 依赖: Classical, Classical.not_not, SimpleGraph, SimpleGraph.isUniform_singleton, eq_empty_iff_forall_notMem, exists_imp, isUniform_singleton, mem_map, mk_mem_nonUniforms, not_and, not_not, parts_bot
-/
theorem nonUniforms_bot (hε : 0 < ε) : (⊥ : Finpartition A).nonUniforms G ε = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  rintro ⟨u, v⟩
  simp only [mk_mem_nonUniforms, parts_bot, mem_map, not_and,
    Classical.not_not, exists_imp]; dsimp
  rintro x ⟨_, rfl⟩ y ⟨_, rfl⟩ _
  rwa [SimpleGraph.isUniform_singleton]

/--
Definition of `IsUniform` / `IsUniform` 的定义

English:
definition IsUniform
  signature: (ε : 𝕜)
  body: (#(P.nonUniforms G ε) : 𝕜) <= (#P.parts * (#P.parts - 1) : Nat) * ε

中文:
定义 是一致
  签名: (ε : 𝕜)
  定义体: (#(P.nonUniforms G ε) : 𝕜) <= (#P.parts * (#P.parts - 1) : Nat) * ε

Depends on / 依赖: P.nonUniforms, P.parts, nonUniforms
-/
def IsUniform (ε : 𝕜) : Prop :=
  (#(P.nonUniforms G ε) : 𝕜) <= (#P.parts * (#P.parts - 1) : Nat) * ε

/--
lemma `bot_isUniform` / 引理 `bot_isUniform`

English:
lemma bot_isUniform
  given: (hε : 0 < ε)
  statement: (⊥ : Finpartition A).IsUniform G ε
  proof: by
  rw [Finpartition.IsUniform]; rw [Finpartition.card_bot]; rw [nonUniforms_bot _ hε]; rw [Finset.card_empty]; rw [Nat.cast_zero]
  positivity

中文:
引理 bot_isUniform
  条件: (hε : 0 < ε)
  结论: (⊥ : 有限分拆 A).是一致 G ε
  证明: by
  rw [Finpartition.IsUniform]; rw [Finpartition.card_bot]; rw [nonUniforms_bot _ hε]; rw [Finset.card_empty]; rw [Nat.cast_zero]
  positivity

Depends on / 依赖: Finpartition, Finpartition.IsUniform, Finpartition.card_bot, Finset, Finset.card_empty, IsUniform, Nat.cast_zero, card_bot, card_empty, cast_zero, nonUniforms_bot
-/
lemma bot_isUniform (hε : 0 < ε) : (⊥ : Finpartition A).IsUniform G ε := by
  rw [Finpartition.IsUniform]; rw [Finpartition.card_bot]; rw [nonUniforms_bot _ hε]; rw [Finset.card_empty]; rw [Nat.cast_zero]
  positivity

/--
lemma `isUniform_one` / 引理 `isUniform_one`

English:
lemma isUniform_one
  statement: P.IsUniform G (1 : 𝕜)
  proof: by
  rw [IsUniform]; rw [mul_one]; rw [Nat.cast_le]
  refine (card_filter_le _
    (fun uv => ¬SimpleGraph.IsUniform G 1 (Prod.fst uv) (Prod.snd uv))).trans ?_
  rw [offDiag_card]; rw [Nat.mul_sub_left_distrib]; rw [mul_one]

中文:
引理 isUniform_one
  结论: P.是一致 G (1 : 𝕜)
  证明: by
  rw [IsUniform]; rw [mul_one]; rw [Nat.cast_le]
  refine (card_filter_le _
    (fun uv => ¬SimpleGraph.IsUniform G 1 (Prod.fst uv) (Prod.snd uv))).trans ?_
  rw [offDiag_card]; rw [Nat.mul_sub_left_distrib]; rw [mul_one]

Depends on / 依赖: IsUniform, Nat.cast_le, Nat.mul_sub_left_distrib, Prod.fst, Prod.snd, SimpleGraph, SimpleGraph.IsUniform, card_filter_le, cast_le, mul_one, mul_sub_left_distrib, offDiag_card
-/
lemma isUniform_one : P.IsUniform G (1 : 𝕜) := by
  rw [IsUniform]; rw [mul_one]; rw [Nat.cast_le]
  refine (card_filter_le _
    (fun uv => ¬SimpleGraph.IsUniform G 1 (Prod.fst uv) (Prod.snd uv))).trans ?_
  rw [offDiag_card]; rw [Nat.mul_sub_left_distrib]; rw [mul_one]

variable {P G}

/--
theorem `IsUniform.mono` / 定理 `IsUniform.mono`

English:
theorem IsUniform.mono
  given: {ε ε' : 𝕜} (hP : P.IsUniform G ε) (h : ε <= ε')
  statement: P.IsUniform G ε'
  proof: ((Nat.cast_le.2 <| card_le_card <| P.nonUniforms_mono G h).trans hP).trans by gcongr

omit [IsStrictOrderedRing 𝕜] in

中文:
定理 是一致.mono
  条件: {ε ε' : 𝕜} (hP : P.是一致 G ε) (h : ε <= ε')
  结论: P.是一致 G ε'
  证明: ((Nat.cast_le.2 <| card_le_card <| P.nonUniforms_mono G h).trans hP).trans by gcongr

omit [IsStrictOrderedRing 𝕜] in
-/
theorem IsUniform.mono {ε ε' : 𝕜} (hP : P.IsUniform G ε) (h : ε <= ε') : P.IsUniform G ε' :=
((Nat.cast_le.2 <| card_le_card <| P.nonUniforms_mono G h).trans hP).trans by gcongr

omit [IsStrictOrderedRing 𝕜] in
/--
theorem `isUniformOfEmpty` / 定理 `isUniformOfEmpty`

English:
theorem isUniformOfEmpty
  given: (hP : P.parts = ∅)
  statement: P.IsUniform G ε
  proof: by
  simp [IsUniform, hP, nonUniforms]

omit [IsStrictOrderedRing 𝕜] in

中文:
定理 isUniformOfEmpty
  条件: (hP : P.parts = ∅)
  结论: P.是一致 G ε
  证明: by
  simp [IsUniform, hP, nonUniforms]

omit [IsStrictOrderedRing 𝕜] in

Depends on / 依赖: IsUniform, nonUniforms
-/
theorem isUniformOfEmpty (hP : P.parts = ∅) : P.IsUniform G ε := by
  simp [IsUniform, hP, nonUniforms]

omit [IsStrictOrderedRing 𝕜] in
/--
theorem `nonempty_of_not_uniform` / 定理 `nonempty_of_not_uniform`

English:
theorem nonempty_of_not_uniform
  given: (h : ¬P.IsUniform G ε)
  statement: P.parts.Nonempty
  proof: nonempty_of_ne_empty fun h₁ => h isUniformOfEmpty h₁

中文:
定理 nonempty_of_not_uniform
  条件: (h : ¬P.是一致 G ε)
  结论: P.parts.非空
  证明: nonempty_of_ne_empty fun h₁ => h isUniformOfEmpty h₁

Depends on / 依赖: isUniformOfEmpty, nonempty_of_ne_empty
-/
theorem nonempty_of_not_uniform (h : ¬P.IsUniform G ε) : P.parts.Nonempty :=
nonempty_of_ne_empty fun h₁ => h isUniformOfEmpty h₁

variable (P G ε) (s : Finset α)

/--
Definition of `nonuniformWitnesses` / `nonuniformWitnesses` 的定义

English:
definition nonuniformWitnesses
  signature: : Finset (Finset α)
  body: {t in P.parts | s != t ∧ ¬G.IsUniform ε s t}.image (G.nonuniformWitness ε s)

中文:
定义 nonuniformWitnesses
  签名: : 有限集 (有限集 α)
  定义体: {t in P.parts | s != t ∧ ¬G.IsUniform ε s t}.image (G.nonuniformWitness ε s)

Depends on / 依赖: G.IsUniform, G.nonuniformWitness, IsUniform, P.parts, nonuniformWitness
-/
noncomputable def nonuniformWitnesses : Finset (Finset α) :=
  {t in P.parts | s != t ∧ ¬G.IsUniform ε s t}.image (G.nonuniformWitness ε s)

variable {P G ε s} {t : Finset α}

/--
lemma `card_nonuniformWitnesses_le` / 引理 `card_nonuniformWitnesses_le`

English:
lemma card_nonuniformWitnesses_le
  proof: card_image_le

中文:
引理 card_nonuniformWitnesses_le
  证明: card_image_le

Depends on / 依赖: card_image_le
-/
lemma card_nonuniformWitnesses_le :
    #(P.nonuniformWitnesses G ε s) <= #{t in P.parts | s != t ∧ ¬G.IsUniform ε s t} := card_image_le

/--
theorem `nonuniformWitness_mem_nonuniformWitnesses` / 定理 `nonuniformWitness_mem_nonuniformWitnesses`

English:
theorem nonuniformWitness_mem_nonuniformWitnesses
  statement: (h : ¬G.IsUniform ε s t) (ht : t in P.parts)
  proof: mem_image_of_mem _ mem_filter.2 ⟨ht, hst, h⟩

中文:
定理 nonuniformWitness_mem_nonuniformWitnesses
  结论: (h : ¬G.是一致 ε s t) (ht : t in P.parts)
  证明: mem_image_of_mem _ mem_filter.2 ⟨ht, hst, h⟩

Depends on / 依赖: mem_filter, mem_image_of_mem
-/
theorem nonuniformWitness_mem_nonuniformWitnesses (h : ¬G.IsUniform ε s t) (ht : t in P.parts)
    (hst : s != t) : G.nonuniformWitness ε s t in P.nonuniformWitnesses G ε s :=
mem_image_of_mem _ mem_filter.2 ⟨ht, hst, h⟩

/-! ### Equipartitions -/

open SimpleGraph in
/--
lemma `IsEquipartition.card_interedges_sparsePairs_le'` / 引理 `IsEquipartition.card_interedges_sparsePairs_le'`

English:
lemma IsEquipartition.card_interedges_sparsePairs_le'
  statement: (hP : P.IsEquipartition)
  proof: by
  calc
    _ <= ∑ UV in P.sparsePairs G ε, (#(G.interedges UV.1 UV.2) : 𝕜) := mod_cast card_biUnion_le
    _ <= ∑ UV in P.sparsePairs G ε, ε * (#UV.1 * #UV.2) := ?_
    _ <= ∑ UV in P.parts.offDiag, ε * (#UV.1 * #UV.2) := by gcongr; apply filter_subset
    _ = ε * ∑ UV in P.parts.offDiag, (#UV.1 * #UV.2 : 𝕜) := (mul_sum _ _ _).symm
    _ <= _ := ?_
  · gcongr with ⟨U, V⟩ hUV
    simp only [mk_mem_sparsePairs, ne_eq, ← card_interedges_div_card, Rat.cast_div,
      Rat.cast_natCast, Rat.cast_mul] at hUV
    refine ((div_lt_iff₀ ?_).1 hUV.2.2.2).le
    exact mul_pos (Nat.cast_pos.2 (P.nonempty_of_mem_parts hUV.1).card_pos)
      (Nat.cast_pos.2 (P.nonempty_of_mem_parts hUV.2.1).card_pos)
  norm_cast
  gcongr
  calc
    (_ : Nat) <= _ := sum_le_card_nsmul P.parts.offDiag (fun i => #i.1 * #i.2)
            ((#A / #P.parts + 1) ^ 2 : Nat) ?_
    _ <= (#P.parts * (#A / #P.parts) + #P.parts) ^ 2 := ?_
    _ <= _ := by gcongr; apply Nat.mul_div_le
  · simp only [Prod.forall, and_imp, mem_offDiag, sq]
    rintro U V hU hV -
    exact_mod_cast Nat.mul_le_mul (hP.card_part_le_average_add_one hU)
      (hP.card_part_le_average_add_one hV)
  · rw [smul_eq_mul, offDiag_card, Nat.mul_sub_right_distrib, ← sq, ← mul_pow, mul_add_one (α := Nat)]
    exact Nat.sub_le _ _

中文:
引理 IsEquipartition.card_interedges_sparsePairs_le'
  结论: (hP : P.IsEquipartition)
  证明: by
  calc
    _ <= ∑ UV in P.sparsePairs G ε, (#(G.interedges UV.1 UV.2) : 𝕜) := mod_cast card_biUnion_le
    _ <= ∑ UV in P.sparsePairs G ε, ε * (#UV.1 * #UV.2) := ?_
    _ <= ∑ UV in P.parts.offDiag, ε * (#UV.1 * #UV.2) := by gcongr; apply filter_subset
    _ = ε * ∑ UV in P.parts.offDiag, (#UV.1 * #UV.2 : 𝕜) := (mul_sum _ _ _).symm
    _ <= _ := ?_
  · gcongr with ⟨U, V⟩ hUV
    simp only [mk_mem_sparsePairs, ne_eq, ← card_interedges_div_card, Rat.cast_div,
      Rat.cast_natCast, Rat.cast_mul] at hUV
    refine ((div_lt_iff₀ ?_).1 hUV.2.2.2).le
    exact mul_pos (Nat.cast_pos.2 (P.nonempty_of_mem_parts hUV.1).card_pos)
      (Nat.cast_pos.2 (P.nonempty_of_mem_parts hUV.2.1).card_pos)
  norm_cast
  gcongr
  calc
    (_ : Nat) <= _ := sum_le_card_nsmul P.parts.offDiag (fun i => #i.1 * #i.2)
            ((#A / #P.parts + 1) ^ 2 : Nat) ?_
    _ <= (#P.parts * (#A / #P.parts) + #P.parts) ^ 2 := ?_
    _ <= _ := by gcongr; apply Nat.mul_div_le
  · simp only [Prod.forall, and_imp, mem_offDiag, sq]
    rintro U V hU hV -
    exact_mod_cast Nat.mul_le_mul (hP.card_part_le_average_add_one hU)
      (hP.card_part_le_average_add_one hV)
  · rw [smul_eq_mul, offDiag_card, Nat.mul_sub_right_distrib, ← sq, ← mul_pow, mul_add_one (α := Nat)]
    exact Nat.sub_le _ _

Depends on / 依赖: G.interedges, P.parts.offDiag, P.sparsePairs, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, card_biUnion_le, card_interedges_div_card, cast_div, cast_mul, cast_natCast, filter_subset, interedges, mk_mem_sparsePairs, mod_cast, mul_sum, ne_eq, offDiag, sparsePairs
-/
lemma IsEquipartition.card_interedges_sparsePairs_le' (hP : P.IsEquipartition)
    (hε : 0 <= ε) :
    #((P.sparsePairs G ε).biUnion fun (U, V) => G.interedges U V) <= ε * (#A + #P.parts) ^ 2 := by
  calc
    _ <= ∑ UV in P.sparsePairs G ε, (#(G.interedges UV.1 UV.2) : 𝕜) := mod_cast card_biUnion_le
    _ <= ∑ UV in P.sparsePairs G ε, ε * (#UV.1 * #UV.2) := ?_
    _ <= ∑ UV in P.parts.offDiag, ε * (#UV.1 * #UV.2) := by gcongr; apply filter_subset
    _ = ε * ∑ UV in P.parts.offDiag, (#UV.1 * #UV.2 : 𝕜) := (mul_sum _ _ _).symm
    _ <= _ := ?_
  · gcongr with ⟨U, V⟩ hUV
    simp only [mk_mem_sparsePairs, ne_eq, ← card_interedges_div_card, Rat.cast_div,
      Rat.cast_natCast, Rat.cast_mul] at hUV
    refine ((div_lt_iff₀ ?_).1 hUV.2.2.2).le
    exact mul_pos (Nat.cast_pos.2 (P.nonempty_of_mem_parts hUV.1).card_pos)
      (Nat.cast_pos.2 (P.nonempty_of_mem_parts hUV.2.1).card_pos)
  norm_cast
  gcongr
  calc
    (_ : Nat) <= _ := sum_le_card_nsmul P.parts.offDiag (fun i => #i.1 * #i.2)
            ((#A / #P.parts + 1) ^ 2 : Nat) ?_
    _ <= (#P.parts * (#A / #P.parts) + #P.parts) ^ 2 := ?_
    _ <= _ := by gcongr; apply Nat.mul_div_le
  · simp only [Prod.forall, and_imp, mem_offDiag, sq]
    rintro U V hU hV -
    exact_mod_cast Nat.mul_le_mul (hP.card_part_le_average_add_one hU)
      (hP.card_part_le_average_add_one hV)
  · rw [smul_eq_mul, offDiag_card, Nat.mul_sub_right_distrib, ← sq, ← mul_pow, mul_add_one (α := Nat)]
    exact Nat.sub_le _ _

/--
lemma `IsEquipartition.card_interedges_sparsePairs_le` / 引理 `IsEquipartition.card_interedges_sparsePairs_le`

English:
lemma IsEquipartition.card_interedges_sparsePairs_le
  given: (hP : P.IsEquipartition) (hε : 0 <= ε)
  proof: by
  calc
    _ <= _ := hP.card_interedges_sparsePairs_le' hε
    _ <= ε * (#A + #A) ^ 2 := by gcongr; exact P.card_parts_le_card
    _ = _ := by ring

中文:
引理 IsEquipartition.card_interedges_sparsePairs_le
  条件: (hP : P.IsEquipartition) (hε : 0 <= ε)
  证明: by
  calc
    _ <= _ := hP.card_interedges_sparsePairs_le' hε
    _ <= ε * (#A + #A) ^ 2 := by gcongr; exact P.card_parts_le_card
    _ = _ := by ring

Depends on / 依赖: P.card_parts_le_card, card_interedges_sparsePairs_le, card_parts_le_card, hP.card_interedges_sparsePairs_le
-/
lemma IsEquipartition.card_interedges_sparsePairs_le (hP : P.IsEquipartition) (hε : 0 <= ε) :
    #((P.sparsePairs G ε).biUnion fun (U, V) => G.interedges U V) <= 4 * ε * #A ^ 2 := by
  calc
    _ <= _ := hP.card_interedges_sparsePairs_le' hε
    _ <= ε * (#A + #A) ^ 2 := by gcongr; exact P.card_parts_le_card
    _ = _ := by ring

/--
lemma `aux` / 引理 `aux`

English:
lemma aux
  given: {i j : Nat} (hj : 0 < j)
  statement: j * (j - 1) * (i / j + 1) ^ 2 < (i + j) ^ 2
  proof: by
  have : j * (j - 1) < j ^ 2 := by
    rw [sq]; exact Nat.mul_lt_mul_of_pos_left (Nat.sub_lt hj zero_lt_one) hj
  apply (Nat.mul_lt_mul_of_pos_right this <| pow_pos Nat.succ_pos' _).trans_le
  rw [← mul_pow]; rw [Nat.mul_succ]
  gcongr
  apply Nat.mul_div_le

中文:
引理 aux
  条件: {i j : 自然数} (hj : 0 < j)
  结论: j * (j - 1) * (i / j + 1) ^ 2 < (i + j) ^ 2
  证明: by
  have : j * (j - 1) < j ^ 2 := by
    rw [sq]; exact Nat.mul_lt_mul_of_pos_left (Nat.sub_lt hj zero_lt_one) hj
  apply (Nat.mul_lt_mul_of_pos_right this <| pow_pos Nat.succ_pos' _).trans_le
  rw [← mul_pow]; rw [Nat.mul_succ]
  gcongr
  apply Nat.mul_div_le
-/
private lemma aux {i j : Nat} (hj : 0 < j) : j * (j - 1) * (i / j + 1) ^ 2 < (i + j) ^ 2 := by
  have : j * (j - 1) < j ^ 2 := by
    rw [sq]; exact Nat.mul_lt_mul_of_pos_left (Nat.sub_lt hj zero_lt_one) hj
  apply (Nat.mul_lt_mul_of_pos_right this <| pow_pos Nat.succ_pos' _).trans_le
  rw [← mul_pow]; rw [Nat.mul_succ]
  gcongr
  apply Nat.mul_div_le

/--
lemma `IsEquipartition.card_biUnion_offDiag_le'` / 引理 `IsEquipartition.card_biUnion_offDiag_le'`

English:
lemma IsEquipartition.card_biUnion_offDiag_le'
  given: (hP : P.IsEquipartition)
  proof: by
  obtain h | h := P.parts.eq_empty_or_nonempty
  · simp [h]
  calc
    _ <= (#P.parts : 𝕜) * (↑(#A / #P.parts) * ↑(#A / #P.parts + 1)) :=
        mod_cast card_biUnion_le_card_mul _ _ _ fun U hU => ?_
    _ = #P.parts * ↑(#A / #P.parts) * ↑(#A / #P.parts + 1) := by rw [mul_assoc]
    _ <= #A * (#A / #P.parts + 1) :=
        mul_le_mul (mod_cast Nat.mul_div_le _ _) ?_ (by positivity) (by positivity)
    _ = _ := by rw [← div_add_same (mod_cast h.card_pos.ne'), mul_div_assoc]
  · simpa using Nat.cast_div_le
  suffices (#U - 1) * #U <= #A / #P.parts * (#A / #P.parts + 1) by
    rwa [Nat.mul_sub_right_distrib, one_mul, ← offDiag_card] at this
  have := hP.card_part_le_average_add_one hU
  refine Nat.mul_le_mul ((Nat.sub_le_sub_right this 1).trans ?_) this
  simp only [Nat.add_succ_sub_one, add_zero, le_rfl]

中文:
引理 IsEquipartition.card_biUnion_offDiag_le'
  条件: (hP : P.IsEquipartition)
  证明: by
  obtain h | h := P.parts.eq_empty_or_nonempty
  · simp [h]
  calc
    _ <= (#P.parts : 𝕜) * (↑(#A / #P.parts) * ↑(#A / #P.parts + 1)) :=
        mod_cast card_biUnion_le_card_mul _ _ _ fun U hU => ?_
    _ = #P.parts * ↑(#A / #P.parts) * ↑(#A / #P.parts + 1) := by rw [mul_assoc]
    _ <= #A * (#A / #P.parts + 1) :=
        mul_le_mul (mod_cast Nat.mul_div_le _ _) ?_ (by positivity) (by positivity)
    _ = _ := by rw [← div_add_same (mod_cast h.card_pos.ne'), mul_div_assoc]
  · simpa using Nat.cast_div_le
  suffices (#U - 1) * #U <= #A / #P.parts * (#A / #P.parts + 1) by
    rwa [Nat.mul_sub_right_distrib, one_mul, ← offDiag_card] at this
  have := hP.card_part_le_average_add_one hU
  refine Nat.mul_le_mul ((Nat.sub_le_sub_right this 1).trans ?_) this
  simp only [Nat.add_succ_sub_one, add_zero, le_rfl]

Depends on / 依赖: Nat.cast_div_le, Nat.mul_div_le, P.parts, P.parts.eq_empty_or_nonempty, card_biUnion_le_card_mul, card_pos, cast_div_le, div_add_same, eq_empty_or_nonempty, h.card_pos.ne, mod_cast, mul_assoc, mul_div_assoc, mul_div_le, mul_le_mul
-/
lemma IsEquipartition.card_biUnion_offDiag_le' (hP : P.IsEquipartition) :
    (#(P.parts.biUnion offDiag) : 𝕜) <= #A * (#A + #P.parts) / #P.parts := by
  obtain h | h := P.parts.eq_empty_or_nonempty
  · simp [h]
  calc
    _ <= (#P.parts : 𝕜) * (↑(#A / #P.parts) * ↑(#A / #P.parts + 1)) :=
        mod_cast card_biUnion_le_card_mul _ _ _ fun U hU => ?_
    _ = #P.parts * ↑(#A / #P.parts) * ↑(#A / #P.parts + 1) := by rw [mul_assoc]
    _ <= #A * (#A / #P.parts + 1) :=
        mul_le_mul (mod_cast Nat.mul_div_le _ _) ?_ (by positivity) (by positivity)
    _ = _ := by rw [← div_add_same (mod_cast h.card_pos.ne'), mul_div_assoc]
  · simpa using Nat.cast_div_le
  suffices (#U - 1) * #U <= #A / #P.parts * (#A / #P.parts + 1) by
    rwa [Nat.mul_sub_right_distrib, one_mul, ← offDiag_card] at this
  have := hP.card_part_le_average_add_one hU
  refine Nat.mul_le_mul ((Nat.sub_le_sub_right this 1).trans ?_) this
  simp only [Nat.add_succ_sub_one, add_zero, le_rfl]

/--
lemma `IsEquipartition.card_biUnion_offDiag_le` / 引理 `IsEquipartition.card_biUnion_offDiag_le`

English:
lemma IsEquipartition.card_biUnion_offDiag_le
  statement: (hε : 0 < ε) (hP : P.IsEquipartition)
  proof: by
  obtain rfl | hA : A = ⊥ ∨ _ := A.eq_empty_or_nonempty
  · simp [Subsingleton.elim P ⊥]
  apply hP.card_biUnion_offDiag_le'.trans
  rw [div_le_iff₀ (Nat.cast_pos.2 (P.parts_nonempty hA.ne_empty).card_pos)]
  have : (#A : 𝕜) + #P.parts <= 2 * #A := by
    rw [two_mul]; gcongr; exact P.card_parts_le_card
  refine (mul_le_mul_of_nonneg_left this <| by positivity).trans ?_
  suffices 1 <= ε / 4 * #P.parts by
    rw [mul_left_comm]; rw [← sq]
    convert! mul_le_mul_of_nonneg_left this (mul_nonneg zero_le_two <| sq_nonneg (#A : 𝕜)) using 1
      <;> ring
  rwa [← div_le_iff₀', one_div_div]
  positivity

中文:
引理 IsEquipartition.card_biUnion_offDiag_le
  结论: (hε : 0 < ε) (hP : P.IsEquipartition)
  证明: by
  obtain rfl | hA : A = ⊥ ∨ _ := A.eq_empty_or_nonempty
  · simp [Subsingleton.elim P ⊥]
  apply hP.card_biUnion_offDiag_le'.trans
  rw [div_le_iff₀ (Nat.cast_pos.2 (P.parts_nonempty hA.ne_empty).card_pos)]
  have : (#A : 𝕜) + #P.parts <= 2 * #A := by
    rw [two_mul]; gcongr; exact P.card_parts_le_card
  refine (mul_le_mul_of_nonneg_left this <| by positivity).trans ?_
  suffices 1 <= ε / 4 * #P.parts by
    rw [mul_left_comm]; rw [← sq]
    convert! mul_le_mul_of_nonneg_left this (mul_nonneg zero_le_two <| sq_nonneg (#A : 𝕜)) using 1
      <;> ring
  rwa [← div_le_iff₀', one_div_div]
  positivity

Depends on / 依赖: A.eq_empty_or_nonempty, Nat.cast_pos, P.card_parts_le_card, P.parts, P.parts_nonempty, Subsingleton, Subsingleton.elim, card_biUnion_offDiag_le, card_parts_le_card, card_pos, cast_pos, convert, eq_empty_or_nonempty, hA.ne_empty, hP.card_biUnion_offDiag_le, mul_le_mul_of_nonneg_left, mul_left_comm, mul_nonneg, ne_empty, parts_nonempty
-/
lemma IsEquipartition.card_biUnion_offDiag_le (hε : 0 < ε) (hP : P.IsEquipartition)
    (hP' : 4 / ε <= #P.parts) : #(P.parts.biUnion offDiag) <= ε / 2 * #A ^ 2 := by
  obtain rfl | hA : A = ⊥ ∨ _ := A.eq_empty_or_nonempty
  · simp [Subsingleton.elim P ⊥]
  apply hP.card_biUnion_offDiag_le'.trans
  rw [div_le_iff₀ (Nat.cast_pos.2 (P.parts_nonempty hA.ne_empty).card_pos)]
  have : (#A : 𝕜) + #P.parts <= 2 * #A := by
    rw [two_mul]; gcongr; exact P.card_parts_le_card
  refine (mul_le_mul_of_nonneg_left this <| by positivity).trans ?_
  suffices 1 <= ε / 4 * #P.parts by
    rw [mul_left_comm]; rw [← sq]
    convert! mul_le_mul_of_nonneg_left this (mul_nonneg zero_le_two <| sq_nonneg (#A : 𝕜)) using 1
      <;> ring
  rwa [← div_le_iff₀', one_div_div]
  positivity

/--
lemma `IsEquipartition.sum_nonUniforms_lt'` / 引理 `IsEquipartition.sum_nonUniforms_lt'`

English:
lemma IsEquipartition.sum_nonUniforms_lt'
  statement: (hA : A.Nonempty) (hε : 0 < ε) (hP : P.IsEquipartition)
  proof: by
  calc
    _ <= #(P.nonUniforms G ε) • (↑(#A / #P.parts + 1) : 𝕜) ^ 2 :=
      sum_le_card_nsmul _ _ _ ?_
    _ = _ := nsmul_eq_mul _ _
_ <= _ := mul_le_mul_of_nonneg_right hG by positivity
    _ < _ := ?_
  · simp only [Prod.forall, Finpartition.mk_mem_nonUniforms, and_imp]
    rintro U V hU hV - -
    rw [sq]; rw [← Nat.cast_mul]; rw [← Nat.cast_mul]; rw [Nat.cast_le]
    exact Nat.mul_le_mul (hP.card_part_le_average_add_one hU)
      (hP.card_part_le_average_add_one hV)
  · rw [mul_right_comm _ ε, mul_comm ε]
    gcongr
    norm_cast
    exact aux (P.parts_nonempty hA.ne_empty).card_pos

中文:
引理 IsEquipartition.sum_nonUniforms_lt'
  结论: (hA : A.非空) (hε : 0 < ε) (hP : P.IsEquipartition)
  证明: by
  calc
    _ <= #(P.nonUniforms G ε) • (↑(#A / #P.parts + 1) : 𝕜) ^ 2 :=
      sum_le_card_nsmul _ _ _ ?_
    _ = _ := nsmul_eq_mul _ _
_ <= _ := mul_le_mul_of_nonneg_right hG by positivity
    _ < _ := ?_
  · simp only [Prod.forall, Finpartition.mk_mem_nonUniforms, and_imp]
    rintro U V hU hV - -
    rw [sq]; rw [← Nat.cast_mul]; rw [← Nat.cast_mul]; rw [Nat.cast_le]
    exact Nat.mul_le_mul (hP.card_part_le_average_add_one hU)
      (hP.card_part_le_average_add_one hV)
  · rw [mul_right_comm _ ε, mul_comm ε]
    gcongr
    norm_cast
    exact aux (P.parts_nonempty hA.ne_empty).card_pos

Depends on / 依赖: Finpartition, Finpartition.mk_mem_nonUniforms, Nat.cast_le, Nat.cast_mul, Nat.mul_le_mul, P.nonUniforms, P.parts, Prod.forall, and_imp, card_part_le_average_add_one, cast_le, cast_mul, hP.card_part_le_average_add_one, mk_mem_nonUniforms, mul_comm, mul_le_mul, mul_le_mul_of_nonneg_right, mul_right_comm, nonUniforms, nsmul_eq_mul
-/
lemma IsEquipartition.sum_nonUniforms_lt' (hA : A.Nonempty) (hε : 0 < ε) (hP : P.IsEquipartition)
    (hG : P.IsUniform G ε) :
    ∑ i in P.nonUniforms G ε, (#i.1 * #i.2 : 𝕜) < ε * (#A + #P.parts) ^ 2 := by
  calc
    _ <= #(P.nonUniforms G ε) • (↑(#A / #P.parts + 1) : 𝕜) ^ 2 :=
      sum_le_card_nsmul _ _ _ ?_
    _ = _ := nsmul_eq_mul _ _
_ <= _ := mul_le_mul_of_nonneg_right hG by positivity
    _ < _ := ?_
  · simp only [Prod.forall, Finpartition.mk_mem_nonUniforms, and_imp]
    rintro U V hU hV - -
    rw [sq]; rw [← Nat.cast_mul]; rw [← Nat.cast_mul]; rw [Nat.cast_le]
    exact Nat.mul_le_mul (hP.card_part_le_average_add_one hU)
      (hP.card_part_le_average_add_one hV)
  · rw [mul_right_comm _ ε, mul_comm ε]
    gcongr
    norm_cast
    exact aux (P.parts_nonempty hA.ne_empty).card_pos

/--
lemma `IsEquipartition.sum_nonUniforms_lt` / 引理 `IsEquipartition.sum_nonUniforms_lt`

English:
lemma IsEquipartition.sum_nonUniforms_lt
  statement: (hA : A.Nonempty) (hε : 0 < ε) (hP : P.IsEquipartition)
  proof: by
  calc
    _ <= ∑ i in P.nonUniforms G ε, (#i.1 * #i.2 : 𝕜) := by
        norm_cast; simp_rw [← card_product]; exact card_biUnion_le
    _ < _ := hP.sum_nonUniforms_lt' hA hε hG
    _ <= ε * (#A + #A) ^ 2 := by gcongr; exact P.card_parts_le_card
    _ = _ := by ring

中文:
引理 IsEquipartition.sum_nonUniforms_lt
  结论: (hA : A.非空) (hε : 0 < ε) (hP : P.IsEquipartition)
  证明: by
  calc
    _ <= ∑ i in P.nonUniforms G ε, (#i.1 * #i.2 : 𝕜) := by
        norm_cast; simp_rw [← card_product]; exact card_biUnion_le
    _ < _ := hP.sum_nonUniforms_lt' hA hε hG
    _ <= ε * (#A + #A) ^ 2 := by gcongr; exact P.card_parts_le_card
    _ = _ := by ring

Depends on / 依赖: P.card_parts_le_card, P.nonUniforms, card_biUnion_le, card_parts_le_card, card_product, hP.sum_nonUniforms_lt, nonUniforms, simp_rw, sum_nonUniforms_lt
-/
lemma IsEquipartition.sum_nonUniforms_lt (hA : A.Nonempty) (hε : 0 < ε) (hP : P.IsEquipartition)
    (hG : P.IsUniform G ε) :
    #((P.nonUniforms G ε).biUnion fun (U, V) => U ×ˢ V) < 4 * ε * #A ^ 2 := by
  calc
    _ <= ∑ i in P.nonUniforms G ε, (#i.1 * #i.2 : 𝕜) := by
        norm_cast; simp_rw [← card_product]; exact card_biUnion_le
    _ < _ := hP.sum_nonUniforms_lt' hA hε hG
    _ <= ε * (#A + #A) ^ 2 := by gcongr; exact P.card_parts_le_card
    _ = _ := by ring

end Finpartition

/-! ### Reduced graph -/

namespace SimpleGraph

/--
Definition of `regularityReduced` / `regularityReduced` 的定义

English:
definition regularityReduced
  signature: (ε δ : 𝕜)
  body: G.Adj a b ∧
    exists U in P.parts, exists V in P.parts, a in U ∧ b in V ∧ U != V ∧ G.IsUniform ε U V ∧ δ <= G.edgeDensity U V
  symm.symm a b := by
    rintro ⟨ab, U, UP, V, VP, xU, yV, UV, GUV, εUV⟩
    refine ⟨ab.symm, V, VP, U, UP, yV, xU, UV.symm, GUV.symm, ?_⟩
    rwa [edgeDensity_comm]

中文:
定义 regularityReduced
  签名: (ε δ : 𝕜)
  定义体: G.Adj a b ∧
    exists U in P.parts, exists V in P.parts, a in U ∧ b in V ∧ U != V ∧ G.IsUniform ε U V ∧ δ <= G.edgeDensity U V
  symm.symm a b := by
    rintro ⟨ab, U, UP, V, VP, xU, yV, UV, GUV, εUV⟩
    refine ⟨ab.symm, V, VP, U, UP, yV, xU, UV.symm, GUV.symm, ?_⟩
    rwa [edgeDensity_comm]
-/
@[simps] def regularityReduced (ε δ : 𝕜) : SimpleGraph α where
  Adj a b := G.Adj a b ∧
    exists U in P.parts, exists V in P.parts, a in U ∧ b in V ∧ U != V ∧ G.IsUniform ε U V ∧ δ <= G.edgeDensity U V
  symm.symm a b := by
    rintro ⟨ab, U, UP, V, VP, xU, yV, UV, GUV, εUV⟩
    refine ⟨ab.symm, V, VP, U, UP, yV, xU, UV.symm, GUV.symm, ?_⟩
    rwa [edgeDensity_comm]

/--
Instance `regularityReduced.instDecidableRel_adj` / 实例 `regularityReduced.instDecidableRel_adj`

English:
instance regularityReduced.instDecidableRel_adj
  signature: : DecidableRel (G.regularityReduced P ε δ).Adj
  body: inferInstanceAs DecidableRel (mk _ _).Adj

中文:
实例 regularityReduced.instDecidableRel_adj
  签名: : DecidableRel (G.regularityReduced P ε δ).伴随
  定义体: inferInstanceAs DecidableRel (mk _ _).Adj

Depends on / 依赖: DecidableRel
-/
instance regularityReduced.instDecidableRel_adj : DecidableRel (G.regularityReduced P ε δ).Adj :=
inferInstanceAs DecidableRel (mk _ _).Adj

variable {G P}

omit [IsStrictOrderedRing 𝕜] in
/--
lemma `regularityReduced_le` / 引理 `regularityReduced_le`

English:
lemma regularityReduced_le
  statement: G.regularityReduced P ε δ <= G
  proof: fun _ _ => And.left

中文:
引理 regularityReduced_le
  结论: G.regularityReduced P ε δ <= G
  证明: fun _ _ => And.left

Depends on / 依赖: And.left
-/
lemma regularityReduced_le : G.regularityReduced P ε δ <= G := fun _ _ => And.left

/--
lemma `regularityReduced_mono` / 引理 `regularityReduced_mono`

English:
lemma regularityReduced_mono
  given: {ε₁ ε₂ : 𝕜} (hε : ε₁ <= ε₂)
  proof: fun _a _b ⟨hab, U, hU, V, hV, ha, hb, hUV, hGε, hGδ⟩ =>
    ⟨hab, U, hU, V, hV, ha, hb, hUV, hGε.mono hε, hGδ⟩

omit [IsStrictOrderedRing 𝕜] in

中文:
引理 regularityReduced_mono
  条件: {ε₁ ε₂ : 𝕜} (hε : ε₁ <= ε₂)
  证明: fun _a _b ⟨hab, U, hU, V, hV, ha, hb, hUV, hGε, hGδ⟩ =>
    ⟨hab, U, hU, V, hV, ha, hb, hUV, hGε.mono hε, hGδ⟩

omit [IsStrictOrderedRing 𝕜] in
-/
lemma regularityReduced_mono {ε₁ ε₂ : 𝕜} (hε : ε₁ <= ε₂) :
    G.regularityReduced P ε₁ δ <= G.regularityReduced P ε₂ δ :=
  fun _a _b ⟨hab, U, hU, V, hV, ha, hb, hUV, hGε, hGδ⟩ =>
    ⟨hab, U, hU, V, hV, ha, hb, hUV, hGε.mono hε, hGδ⟩

omit [IsStrictOrderedRing 𝕜] in
/--
lemma `regularityReduced_anti` / 引理 `regularityReduced_anti`

English:
lemma regularityReduced_anti
  given: {δ₁ δ₂ : 𝕜} (hδ : δ₁ <= δ₂)
  proof: fun _a _b ⟨hab, U, hU, V, hV, ha, hb, hUV, hUVε, hUVδ⟩ =>
    ⟨hab, U, hU, V, hV, ha, hb, hUV, hUVε, hδ.trans hUVδ⟩

omit [IsStrictOrderedRing 𝕜] in

中文:
引理 regularityReduced_anti
  条件: {δ₁ δ₂ : 𝕜} (hδ : δ₁ <= δ₂)
  证明: fun _a _b ⟨hab, U, hU, V, hV, ha, hb, hUV, hUVε, hUVδ⟩ =>
    ⟨hab, U, hU, V, hV, ha, hb, hUV, hUVε, hδ.trans hUVδ⟩

omit [IsStrictOrderedRing 𝕜] in
-/
lemma regularityReduced_anti {δ₁ δ₂ : 𝕜} (hδ : δ₁ <= δ₂) :
    G.regularityReduced P ε δ₂ <= G.regularityReduced P ε δ₁ :=
  fun _a _b ⟨hab, U, hU, V, hV, ha, hb, hUV, hUVε, hUVδ⟩ =>
    ⟨hab, U, hU, V, hV, ha, hb, hUV, hUVε, hδ.trans hUVδ⟩

omit [IsStrictOrderedRing 𝕜] in
/--
lemma `unreduced_edges_subset` / 引理 `unreduced_edges_subset`

English:
lemma unreduced_edges_subset
  proof: by
  rintro ⟨x, y⟩
  simp only [mem_filter, regularityReduced_adj, not_and, not_exists,
    not_le, mem_biUnion, mem_union, mem_product, Prod.exists, mem_offDiag, and_imp,
    or_assoc, and_assoc, P.mk_mem_nonUniforms, Finpartition.mk_mem_sparsePairs, mem_interedges_iff]
  intro hx hy h h'
  replace h' := h' h
  obtain ⟨U, hU, hx⟩ := P.exists_mem hx
  obtain ⟨V, hV, hy⟩ := P.exists_mem hy
  obtain rfl | hUV := eq_or_ne U V
  · exact Or.inr (Or.inl ⟨U, hU, hx, hy, G.ne_of_adj h⟩)
  by_cases h₂ : G.IsUniform (ε / 8) U V
· exact Or.inr Or.inr ⟨U, V, hU, hV, hUV, h' _ hU _ hV hx hy hUV h₂, hx, hy, h⟩
  · exact Or.inl ⟨U, V, hU, hV, hUV, h₂, hx, hy⟩

中文:
引理 unreduced_edges_subset
  证明: by
  rintro ⟨x, y⟩
  simp only [mem_filter, regularityReduced_adj, not_and, not_exists,
    not_le, mem_biUnion, mem_union, mem_product, Prod.exists, mem_offDiag, and_imp,
    or_assoc, and_assoc, P.mk_mem_nonUniforms, Finpartition.mk_mem_sparsePairs, mem_interedges_iff]
  intro hx hy h h'
  replace h' := h' h
  obtain ⟨U, hU, hx⟩ := P.exists_mem hx
  obtain ⟨V, hV, hy⟩ := P.exists_mem hy
  obtain rfl | hUV := eq_or_ne U V
  · exact Or.inr (Or.inl ⟨U, hU, hx, hy, G.ne_of_adj h⟩)
  by_cases h₂ : G.IsUniform (ε / 8) U V
· exact Or.inr Or.inr ⟨U, V, hU, hV, hUV, h' _ hU _ hV hx hy hUV h₂, hx, hy, h⟩
  · exact Or.inl ⟨U, V, hU, hV, hUV, h₂, hx, hy⟩

Depends on / 依赖: Finpartition, Finpartition.mk_mem_sparsePairs, G.IsUniform, G.ne_of_adj, IsUniform, Or.inl, Or.inr, P.exists_mem, P.mk_mem_nonUniforms, Prod.exists, and_assoc, and_imp, eq_or_ne, exists_mem, mem_biUnion, mem_filter, mem_interedges_iff, mem_offDiag, mem_product, mem_union
-/
lemma unreduced_edges_subset :
    (A ×ˢ A).filter (fun (x, y) => G.Adj x y ∧ ¬ (G.regularityReduced P (ε / 8) (ε / 4)).Adj x y) subseteq
      (P.nonUniforms G (ε / 8)).biUnion (fun (U, V) => U ×ˢ V) union P.parts.biUnion offDiag union
        (P.sparsePairs G (ε / 4)).biUnion fun (U, V) => G.interedges U V := by
  rintro ⟨x, y⟩
  simp only [mem_filter, regularityReduced_adj, not_and, not_exists,
    not_le, mem_biUnion, mem_union, mem_product, Prod.exists, mem_offDiag, and_imp,
    or_assoc, and_assoc, P.mk_mem_nonUniforms, Finpartition.mk_mem_sparsePairs, mem_interedges_iff]
  intro hx hy h h'
  replace h' := h' h
  obtain ⟨U, hU, hx⟩ := P.exists_mem hx
  obtain ⟨V, hV, hy⟩ := P.exists_mem hy
  obtain rfl | hUV := eq_or_ne U V
  · exact Or.inr (Or.inl ⟨U, hU, hx, hy, G.ne_of_adj h⟩)
  by_cases h₂ : G.IsUniform (ε / 8) U V
· exact Or.inr Or.inr ⟨U, V, hU, hV, hUV, h' _ hU _ hV hx hy hUV h₂, hx, hy, h⟩
  · exact Or.inl ⟨U, V, hU, hV, hUV, h₂, hx, hy⟩

end SimpleGraph
