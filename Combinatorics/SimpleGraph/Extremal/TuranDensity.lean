/-
Copyright (c) 2025 Mitchell Horner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Horner
-/
module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
public import Mathlib.Data.Nat.Choose.Cast

import Mathlib.Tactic.Bound
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Turán density

This file defines the **Turán density** of a simple graph.

## Main definitions

* `SimpleGraph.turanDensity H` is the **Turán density** of the simple graph `H`, defined as the
  limit of `extremalNumber n H / n.choose 2` as `n` approaches `∞`.

* `SimpleGraph.tendsto_turanDensity` is the proof that `SimpleGraph.turanDensity` is well-defined.

* `SimpleGraph.isEquivalent_extremalNumber` is the proof that `extremalNumber n H` is
  asymptotically equivalent to `turanDensity H * n.choose 2` as `n` approaches `∞`.

* `SimpleGraph.isContained_of_card_edgeFinset`: simple graphs on `n` vertices with at least
  `(turanDensity H + o(1)) * n ^ 2` edges contain `H`, for all sufficiently large `n`.
-/

@[expose] public section


open Asymptotics Filter Finset Fintype Topology

namespace SimpleGraph

variable {W : Type*}

/--
lemma `antitoneOn_extremalNumber_div_choose_two` / 引理 `antitoneOn_extremalNumber_div_choose_two`

English:
lemma antitoneOn_extremalNumber_div_choose_two
  given: (H : SimpleGraph W)
  proof: by
  apply antitoneOn_nat_Ici_of_succ_le
  intro n hn
  conv_lhs =>
    enter [1, 1]
    rw [← Fintype.card_fin (n + 1)]
  rw [div_le_iff₀ (mod_cast Nat.choose_pos (by linarith))]; rw [extremalNumber_le_iff_of_nonneg H (by positivity)]
  intro G _ h
  rw [mul_comm]; rw [← mul_div_assoc]; rw [le_div_

中文:
引理 antitoneOn_extremalNumber_div_choose_two
  条件: (H : SimpleGraph W)
  证明: by
  apply antitoneOn_nat_Ici_of_succ_le
  intro n hn
  conv_lhs =>
    enter [1, 1]
    rw [← Fintype.card_fin (n + 1)]
  rw [div_le_iff₀ (mod_cast Nat.choose_pos (by linarith))]; rw [extremalNumber_le_iff_of_nonneg H (by positivity)]
  intro G _ h
  rw [mul_comm]; rw [← mul_div_assoc]; rw [le_div_

Depends on / 依赖: Fintype, Fintype.card_fin, Nat.cast_add_one, Nat.cast_choose_two, Nat.choose_pos, add_sub_cancel_right, antitoneOn_nat_Ici_of_succ_le, card_fin, cast_add_one, cast_choose_two, choose_pos, conv_lhs, extremalNumber_le_iff_of_nonneg, mod_cast, mul_comm, mul_div, mul_div_assoc
-/
lemma antitoneOn_extremalNumber_div_choose_two (H : SimpleGraph W) :
    AntitoneOn (fun n => (extremalNumber n H / n.choose 2 : Real)) (Set.Ici 2) := by
  apply antitoneOn_nat_Ici_of_succ_le
  intro n hn
  conv_lhs =>
    enter [1, 1]
    rw [← Fintype.card_fin (n + 1)]
  rw [div_le_iff₀ (mod_cast Nat.choose_pos (by linarith))]; rw [extremalNumber_le_iff_of_nonneg H (by positivity)]
  intro G _ h
  rw [mul_comm]; rw [← mul_div_assoc]; rw [le_div_iff₀' (mod_cast Nat.choose_pos hn)]; rw [Nat.cast_choose_two]; rw [Nat.cast_choose_two]; rw [Nat.cast_add_one]; rw [add_sub_cancel_right (n : Real) 1]; rw [mul_comm _ (n - 1 : Real)]; rw [← mul_div (n - 1 : Real)]; rw [mul_comm _ (n / 2 : Real)]; rw [mul_assoc]; rw [mul_comm (n - 1 : Real)]; rw [← mul_div (n + 1 : Real)]; rw [mul_comm _ (n / 2 : Real)]; rw [mul_assoc]; rw [mul_le_mul_iff_right₀ (by positivity)]; rw [← Nat.cast_pred (by positivity)]; rw [← Nat.cast_mul]; rw [← Nat.cast_add_one]; rw [← Nat.cast_mul]; rw [Nat.cast_le]
  conv_rhs =>
    rw [← Fintype.card_fin (n + 1)]; rw [← card_univ]
  -- double counting `(v, e) ↦ v ∉ e`
  apply card_nsmul_le_card_nsmul' (r := fun v e => v ∉ e)
  -- counting `e`
  · intro e he
    simp_rw [← Sym2.mem_toFinset, bipartiteBelow, filter_not, filter_mem_eq_inter, univ_inter,
      ← compl_eq_univ_sdiff, card_compl, Fintype.card_fin, card_toFinset_mem_edgeFinset ⟨e, he⟩,
      Nat.cast_id, Nat.reduceSubDiff, le_refl]
  -- counting `v`
  · intro v hv
    simpa [edgeFinset_deleteIncidenceSet_eq_filter]
      using! card_edgeFinset_deleteIncidenceSet_le_extremalNumber h v

/--
Definition of `turanDensity` / `turanDensity` 的定义

English:
definition turanDensity
  signature: (H : SimpleGraph W)
  body: limUnder atTop fun n => (extremalNumber n H / n.choose 2 : Real)

中文:
定义 turanDensity
  签名: (H : SimpleGraph W)
  定义体: limUnder atTop fun n => (extremalNumber n H / n.choose 2 : Real)

Depends on / 依赖: extremalNumber, limUnder, n.choose
-/
noncomputable def turanDensity (H : SimpleGraph W) :=
  limUnder atTop fun n => (extremalNumber n H / n.choose 2 : Real)

/--
theorem `isGLB_turanDensity` / 定理 `isGLB_turanDensity`

English:
theorem isGLB_turanDensity
  given: (H : SimpleGraph W)
  proof: by
  have h_bdd : BddBelow { (extremalNumber n H / n.choose 2 : Real) | n in Set.Ici 2 } := by
    refine ⟨0, fun x ⟨_, _, hx⟩ => ?_⟩
    rw [← hx]
    positivity
  refine Real.isGLB_of_tendsto_antitoneOn_bddBelow_nat_Ici ?_
    (antitoneOn_extremalNumber_div_choose_two H) h_bdd
  have h_tto := Real

中文:
定理 isGLB_turanDensity
  条件: (H : SimpleGraph W)
  证明: by
  have h_bdd : BddBelow { (extremalNumber n H / n.choose 2 : Real) | n in Set.Ici 2 } := by
    refine ⟨0, fun x ⟨_, _, hx⟩ => ?_⟩
    rw [← hx]
    positivity
  refine Real.isGLB_of_tendsto_antitoneOn_bddBelow_nat_Ici ?_
    (antitoneOn_extremalNumber_div_choose_two H) h_bdd
  have h_tto := Real

Depends on / 依赖: BddBelow, Real.isGLB_of_tendsto_antitoneOn_bddBelow_nat_Ici, Real.tendsto_atTop_csInf_of_antitoneOn_bddBelow_nat_Ici, Set.Ici, antitoneOn_extremalNumber_div_choose_two, extremalNumber, h_bdd, h_tto, h_tto.limUnder_eq, isGLB_of_tendsto_antitoneOn_bddBelow_nat_Ici, limUnder_eq, n.choose, tendsto_atTop_csInf_of_antitoneOn_bddBelow_nat_Ici
-/
theorem isGLB_turanDensity (H : SimpleGraph W) :
    IsGLB { (extremalNumber n H / n.choose 2 : Real) | n in Set.Ici 2 } (turanDensity H) := by
  have h_bdd : BddBelow { (extremalNumber n H / n.choose 2 : Real) | n in Set.Ici 2 } := by
    refine ⟨0, fun x ⟨_, _, hx⟩ => ?_⟩
    rw [← hx]
    positivity
  refine Real.isGLB_of_tendsto_antitoneOn_bddBelow_nat_Ici ?_
    (antitoneOn_extremalNumber_div_choose_two H) h_bdd
  have h_tto := Real.tendsto_atTop_csInf_of_antitoneOn_bddBelow_nat_Ici
    (antitoneOn_extremalNumber_div_choose_two H) h_bdd
  rwa [← h_tto.limUnder_eq] at h_tto

/--
theorem `turanDensity_eq_csInf` / 定理 `turanDensity_eq_csInf`

English:
theorem turanDensity_eq_csInf
  given: (H : SimpleGraph W)
  proof: have h := isGLB_turanDensity H
  (h.csInf_eq h.nonempty).symm

中文:
定理 turanDensity_eq_csInf
  条件: (H : SimpleGraph W)
  证明: have h := isGLB_turanDensity H
  (h.csInf_eq h.nonempty).symm

Depends on / 依赖: csInf_eq, h.csInf_eq, h.nonempty, isGLB_turanDensity, nonempty
-/
theorem turanDensity_eq_csInf (H : SimpleGraph W) :
    turanDensity H = sInf { (extremalNumber n H / n.choose 2 : Real) | n in Set.Ici 2 } :=
  have h := isGLB_turanDensity H
  (h.csInf_eq h.nonempty).symm

/--
theorem `tendsto_turanDensity` / 定理 `tendsto_turanDensity`

English:
theorem tendsto_turanDensity
  given: (H : SimpleGraph W)
  proof: by
  have h_tendsto := Real.tendsto_atTop_csInf_of_antitoneOn_bddBelow_nat_Ici
    (antitoneOn_extremalNumber_div_choose_two H) (isGLB_turanDensity H).bddBelow
  rwa [turanDensity, h_tendsto.limUnder_eq]

中文:
定理 tendsto_turanDensity
  条件: (H : SimpleGraph W)
  证明: by
  have h_tendsto := Real.tendsto_atTop_csInf_of_antitoneOn_bddBelow_nat_Ici
    (antitoneOn_extremalNumber_div_choose_two H) (isGLB_turanDensity H).bddBelow
  rwa [turanDensity, h_tendsto.limUnder_eq]

Depends on / 依赖: Real.tendsto_atTop_csInf_of_antitoneOn_bddBelow_nat_Ici, antitoneOn_extremalNumber_div_choose_two, bddBelow, h_tendsto, h_tendsto.limUnder_eq, isGLB_turanDensity, limUnder_eq, tendsto_atTop_csInf_of_antitoneOn_bddBelow_nat_Ici, turanDensity
-/
theorem tendsto_turanDensity (H : SimpleGraph W) :
    Tendsto (fun n => (extremalNumber n H / n.choose 2 : Real)) atTop (𝓝 (turanDensity H)) := by
  have h_tendsto := Real.tendsto_atTop_csInf_of_antitoneOn_bddBelow_nat_Ici
    (antitoneOn_extremalNumber_div_choose_two H) (isGLB_turanDensity H).bddBelow
  rwa [turanDensity, h_tendsto.limUnder_eq]

/--
theorem `isEquivalent_extremalNumber` / 定理 `isEquivalent_extremalNumber`

English:
theorem isEquivalent_extremalNumber
  given: {H : SimpleGraph W} (h : turanDensity H != 0)
  proof: by
  have hπ := tendsto_turanDensity H
  apply Tendsto.const_mul (1 / turanDensity H : Real) at hπ
  simp_rw [one_div_mul_cancel h, div_mul_div_comm, one_mul] at hπ
  have hz : forallᶠ (x : Nat) in atTop, turanDensity H * x.choose 2 != 0 := by
    rw [eventually_atTop]
    refine ⟨2, fun n hn => ?_⟩

中文:
定理 isEquivalent_extremalNumber
  条件: {H : SimpleGraph W} (h : turanDensity H != 0)
  证明: by
  have hπ := tendsto_turanDensity H
  apply Tendsto.const_mul (1 / turanDensity H : Real) at hπ
  simp_rw [one_div_mul_cancel h, div_mul_div_comm, one_mul] at hπ
  have hz : forallᶠ (x : Nat) in atTop, turanDensity H * x.choose 2 != 0 := by
    rw [eventually_atTop]
    refine ⟨2, fun n hn => ?_⟩

Depends on / 依赖: Nat.choose_eq_zero_iff, Tendsto, Tendsto.const_mul, choose_eq_zero_iff, const_mul, div_mul_div_comm, eventually_atTop, isEquivalent_iff_tendsto_one, one_div_mul_cancel, one_mul, simp_rw, tendsto_turanDensity, turanDensity, x.choose
-/
theorem isEquivalent_extremalNumber {H : SimpleGraph W} (h : turanDensity H != 0) :
    (fun n => (extremalNumber n H : Real)) ~[atTop] (fun n => (turanDensity H * n.choose 2 : Real)) := by
  have hπ := tendsto_turanDensity H
  apply Tendsto.const_mul (1 / turanDensity H : Real) at hπ
  simp_rw [one_div_mul_cancel h, div_mul_div_comm, one_mul] at hπ
  have hz : forallᶠ (x : Nat) in atTop, turanDensity H * x.choose 2 != 0 := by
    rw [eventually_atTop]
    refine ⟨2, fun n hn => ?_⟩
    simpa [h, Nat.choose_eq_zero_iff]
  simpa [isEquivalent_iff_tendsto_one hz] using! hπ

/--
theorem `eventually_isContained_of_card_edgeFinset` / 定理 `eventually_isContained_of_card_edgeFinset`

English:
theorem eventually_isContained_of_card_edgeFinset
  given: (H : SimpleGraph W) {ε : Real} (hε_pos : 0 < ε)
  proof: by
  have hπ := (turanDensity_eq_csInf H).ge
  rw [eventually_atTop]
  contrapose! hπ with h
apply lt_of_lt_of_le lt_add_of_pos_right (turanDensity H) hε_pos
  refine le_csInf ?_ (fun x ⟨m, hm, hx⟩ => ?_)
  · rw [← Set.image, Set.image_nonempty]
    exact Set.nonempty_Ici
  rw [← hx]
  have ⟨n, hn, 

中文:
定理 eventually_isContained_of_card_edgeFinset
  条件: (H : SimpleGraph W) {ε : 实数} (hε_pos : 0 < ε)
  证明: by
  have hπ := (turanDensity_eq_csInf H).ge
  rw [eventually_atTop]
  contrapose! hπ with h
apply lt_of_lt_of_le lt_add_of_pos_right (turanDensity H) hε_pos
  refine le_csInf ?_ (fun x ⟨m, hm, hx⟩ => ?_)
  · rw [← Set.image, Set.image_nonempty]
    exact Set.nonempty_Ici
  rw [← hx]
  have ⟨n, hn, 

Depends on / 依赖: H.Free, Nat.choose_pos, Set.image, Set.image_nonempty, Set.nonempty_Ici, choose_pos, contrapose, eventually_atTop, extremalNumber, h_free, hcard_edges, hm.trans, image_nonempty, le_csInf, lt_add_of_pos_right, lt_of_lt_of_le, mod_cast, n.choose, nonempty_Ici, not_nonempty_iff
-/
theorem eventually_isContained_of_card_edgeFinset (H : SimpleGraph W) {ε : Real} (hε_pos : 0 < ε) :
    forallᶠ n in atTop, forall {G : SimpleGraph (Fin n)} [DecidableRel G.Adj],
      #G.edgeFinset >= (turanDensity H + ε) * n.choose 2 -> H ⊑ G := by
  have hπ := (turanDensity_eq_csInf H).ge
  rw [eventually_atTop]
  contrapose! hπ with h
apply lt_of_lt_of_le lt_add_of_pos_right (turanDensity H) hε_pos
  refine le_csInf ?_ (fun x ⟨m, hm, hx⟩ => ?_)
  · rw [← Set.image, Set.image_nonempty]
    exact Set.nonempty_Ici
  rw [← hx]
  have ⟨n, hn, G, _, hcard_edges, h_free⟩ := h m
  replace h_free : H.Free G := not_nonempty_iff.mpr h_free
  trans (extremalNumber n H / n.choose 2)
  · rw [le_div_iff₀ <| mod_cast Nat.choose_pos (hm.trans hn)]
    conv =>
      enter [2, 1, 1]
      rw [← Fintype.card_fin n]
    exact hcard_edges.trans (mod_cast card_edgeFinset_le_extremalNumber h_free)
  · exact antitoneOn_extremalNumber_div_choose_two H hm (hm.trans hn) hn

open scoped Classical in
/--
Definition of `turanDensityConst` / `turanDensityConst` 的定义

English:
abbreviation turanDensityConst
  signature: (H : SimpleGraph W) (ε : Real)
  body: if h : ε > 0 then
Nat.find eventually_atTop.mp eventually_isContained_of_card_edgeFinset H h
  else 0

中文:
缩写 turanDensityConst
  签名: (H : SimpleGraph W) (ε : 实数)
  定义体: if h : ε > 0 then
Nat.find eventually_atTop.mp eventually_isContained_of_card_edgeFinset H h
  else 0

Depends on / 依赖: Nat.find, eventually_atTop, eventually_atTop.mp, eventually_isContained_of_card_edgeFinset
-/
noncomputable abbrev turanDensityConst (H : SimpleGraph W) (ε : Real) :=
  if h : ε > 0 then
Nat.find eventually_atTop.mp eventually_isContained_of_card_edgeFinset H h
  else 0

/--
theorem `isContained_of_card_edgeFinset` / 定理 `isContained_of_card_edgeFinset`

English:
theorem isContained_of_card_edgeFinset
  statement: (H : SimpleGraph W) {ε : Real} (hε_pos : 0 < ε)
  proof: by
  classical
  rw [(G.overFinIso rfl).card_edgeFinset_eq]; rw [isContained_congr Iso.refl (G.overFinIso rfl)]
apply Nat.find_spec eventually_atTop.mp eventually_isContained_of_card_edgeFinset H hε_pos
  simpa only [turanDensityConst, hε_pos, ↓reduceDIte] using h_verts

中文:
定理 isContained_of_card_edgeFinset
  结论: (H : SimpleGraph W) {ε : 实数} (hε_pos : 0 < ε)
  证明: by
  classical
  rw [(G.overFinIso rfl).card_edgeFinset_eq]; rw [isContained_congr Iso.refl (G.overFinIso rfl)]
apply Nat.find_spec eventually_atTop.mp eventually_isContained_of_card_edgeFinset H hε_pos
  simpa only [turanDensityConst, hε_pos, ↓reduceDIte] using h_verts

Depends on / 依赖: G.overFinIso, Iso.refl, Nat.find_spec, card_edgeFinset_eq, classical, eventually_atTop, eventually_atTop.mp, eventually_isContained_of_card_edgeFinset, find_spec, h_verts, isContained_congr, overFinIso, reduceDIte, turanDensityConst
-/
theorem isContained_of_card_edgeFinset (H : SimpleGraph W) {ε : Real} (hε_pos : 0 < ε)
    {V : Type*} [Fintype V] (h_verts : card V >= turanDensityConst H ε)
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    #G.edgeFinset >= (turanDensity H + ε) * (card V).choose 2 -> H ⊑ G := by
  classical
  rw [(G.overFinIso rfl).card_edgeFinset_eq]; rw [isContained_congr Iso.refl (G.overFinIso rfl)]
apply Nat.find_spec eventually_atTop.mp eventually_isContained_of_card_edgeFinset H hε_pos
  simpa only [turanDensityConst, hε_pos, ↓reduceDIte] using h_verts

end SimpleGraph
