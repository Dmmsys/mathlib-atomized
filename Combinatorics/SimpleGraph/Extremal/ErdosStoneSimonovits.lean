/-
Copyright (c) 2026 Mitchell Horner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Horner
-/
module

public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite
public import Mathlib.Analysis.Real.Sqrt

/-!
# The Erdős-Stone-Simonovits theorem

This file proves the **Erdős-Stone-Simonovits theorem** for simple graphs.

## Main definitions

* `SimpleGraph.eventually_completeEquipartiteGraph_isContained_of_minDegree` is the proof of the
  minimal degree version of the **Erdős-Stone theorem** for simple graphs.
-/

open Filter Finset Fintype Real Topology

namespace SimpleGraph

variable {n : Nat} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
  {W : Type*} [Fintype W] {H : SimpleGraph W}

section ErdosStone

namespace ErdosStone

variable {ε : Real} {r t t' : Nat} (K : G.CompleteEquipartiteSubgraph r t')

/--
Definition of `filter` / `filter` 的定义

English:
definition filter
  signature: (t : Nat)
  body: { v in K.vertsᶜ | forall p in K.parts, exists s in p.powersetCard t, forall w in s, G.Adj v w }

中文:
定义 filter
  签名: (t : 自然数)
  定义体: { v in K.vertsᶜ | forall p in K.parts, exists s in p.powersetCard t, forall w in s, G.Adj v w }

Depends on / 依赖: G.Adj, K.parts, K.verts, p.powersetCard, powersetCard
-/
def filter (t : Nat) : Finset (Fin n) :=
  { v in K.vertsᶜ | forall p in K.parts, exists s in p.powersetCard t, forall w in s, G.Adj v w }

/--
theorem `filter_subset_compl_verts` / 定理 `filter_subset_compl_verts`

English:
theorem filter_subset_compl_verts
  statement: filter K t subseteq K.vertsᶜ
  proof: filter_subset _ K.vertsᶜ

omit [DecidableRel G.Adj] in

中文:
定理 filter_subset_compl_verts
  结论: filter K t subseteq K.vertsᶜ
  证明: filter_subset _ K.vertsᶜ

omit [DecidableRel G.Adj] in

Depends on / 依赖: K.verts, filter_subset
-/
theorem filter_subset_compl_verts : filter K t subseteq K.vertsᶜ :=
  filter_subset _ K.vertsᶜ

omit [DecidableRel G.Adj] in
/--
theorem `between_verts_isBipartiteWith` / 定理 `between_verts_isBipartiteWith`

English:
theorem between_verts_isBipartiteWith
  proof: by
  rw [coe_compl K.verts]
  exact between_isBipartiteWith (disjoint_compl_right)

中文:
定理 between_verts_isBipartiteWith
  证明: by
  rw [coe_compl K.verts]
  exact between_isBipartiteWith (disjoint_compl_right)

Depends on / 依赖: K.verts, between_isBipartiteWith, coe_compl, disjoint_compl_right
-/
theorem between_verts_isBipartiteWith :
    (G.between K.verts K.vertsᶜ).IsBipartiteWith K.verts ↑K.vertsᶜ := by
  rw [coe_compl K.verts]
  exact between_isBipartiteWith (disjoint_compl_right)

/--
lemma `le_card_edgeFinset_between_verts` / 引理 `le_card_edgeFinset_between_verts`

English:
lemma le_card_edgeFinset_between_verts
  proof: by
  rw [← isBipartiteWith_sum_degrees_eq_card_edges (between_verts_isBipartiteWith K)]; rw [← nsmul_eq_mul]; rw [← sum_const]; rw [Nat.cast_sum]
  exact sum_le_sum (fun v hv => sub_le_iff_le_add.mpr <|
    mod_cast (G.minDegree_le_degree v).trans (degree_le_between_add hv))

中文:
引理 le_card_edgeFinset_between_verts
  证明: by
  rw [← isBipartiteWith_sum_degrees_eq_card_edges (between_verts_isBipartiteWith K)]; rw [← nsmul_eq_mul]; rw [← sum_const]; rw [Nat.cast_sum]
  exact sum_le_sum (fun v hv => sub_le_iff_le_add.mpr <|
    mod_cast (G.minDegree_le_degree v).trans (degree_le_between_add hv))

Depends on / 依赖: G.minDegree_le_degree, Nat.cast_sum, between_verts_isBipartiteWith, cast_sum, degree_le_between_add, isBipartiteWith_sum_degrees_eq_card_edges, minDegree_le_degree, mod_cast, nsmul_eq_mul, sub_le_iff_le_add, sub_le_iff_le_add.mpr, sum_const, sum_le_sum
-/
lemma le_card_edgeFinset_between_verts :
    (#K.verts * (G.minDegree - #K.verts) : Real) <= #(G.between K.verts K.vertsᶜ).edgeFinset := by
  rw [← isBipartiteWith_sum_degrees_eq_card_edges (between_verts_isBipartiteWith K)]; rw [← nsmul_eq_mul]; rw [← sum_const]; rw [Nat.cast_sum]
  exact sum_le_sum (fun v hv => sub_le_iff_le_add.mpr <|
    mod_cast (G.minDegree_le_degree v).trans (degree_le_between_add hv))

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `degree_between_verts_lt_of_mem_sdiff` / 引理 `degree_between_verts_lt_of_mem_sdiff`

English:
lemma degree_between_verts_lt_of_mem_sdiff
  proof: by
  simp_rw [Finset.mem_sdiff, ErdosStone.filter, mem_filter, not_and_or, and_or_left,
    and_not_self_iff, false_or, not_forall, not_exists, not_and_or, not_forall, exists_prop] at hv
  obtain ⟨hv, p, hp, hs⟩ := hv
  rw [← card_neighborFinset_eq_degree]; rw [isBipartiteWith_neighborFinset' (between_verts_isBipartiteWith K) hv]
  conv =>
    enter [1, 1, 2]
    unfold CompleteEquipartiteSubgraph.verts
  rw [filter_disjiUnion]; rw [card_disjiUnion]; rw [sum_eq_sum_sdiff_singleton_add hp]
  apply add_lt_add_of_le_of_lt
  · conv_rhs =>
      rw [K.card_verts]; rw [← Nat.sub_one_mul]; rw [← K.card_parts.resolve_right ht'_pos.ne']; rw [← card_singleton p]; rw [← Finset.card_sdiff_of_subset (singleton_subset_iff.mpr hp)]; rw [← smul_eq_mul]; rw [← sum_const]; rw [← Finset.sum_congr rfl fun _ h => K.card_mem_parts (mem_sdiff.mp h).1]
    exact sum_le_sum (fun _ _ => card_filter_le _ _)
  · contrapose! hs
    obtain ⟨s, hs⟩ := powersetCard_nonempty.mpr hs
    have hs' : s in p.powersetCard t := powersetCard_mono (filter_subset _ _) hs
    refine ⟨s, hs', fun w hw => ?_⟩
    obtain ⟨_, hadj, _⟩ := by
      rw [mem_powersetCard] at hs
      apply hs.1 at hw
      rwa [mem_filter, between_adj] at hw
    exact hadj.symm

中文:
引理 degree_between_verts_lt_of_mem_sdiff
  证明: by
  simp_rw [Finset.mem_sdiff, ErdosStone.filter, mem_filter, not_and_or, and_or_left,
    and_not_self_iff, false_or, not_forall, not_exists, not_and_or, not_forall, exists_prop] at hv
  obtain ⟨hv, p, hp, hs⟩ := hv
  rw [← card_neighborFinset_eq_degree]; rw [isBipartiteWith_neighborFinset' (between_verts_isBipartiteWith K) hv]
  conv =>
    enter [1, 1, 2]
    unfold CompleteEquipartiteSubgraph.verts
  rw [filter_disjiUnion]; rw [card_disjiUnion]; rw [sum_eq_sum_sdiff_singleton_add hp]
  apply add_lt_add_of_le_of_lt
  · conv_rhs =>
      rw [K.card_verts]; rw [← Nat.sub_one_mul]; rw [← K.card_parts.resolve_right ht'_pos.ne']; rw [← card_singleton p]; rw [← Finset.card_sdiff_of_subset (singleton_subset_iff.mpr hp)]; rw [← smul_eq_mul]; rw [← sum_const]; rw [← Finset.sum_congr rfl fun _ h => K.card_mem_parts (mem_sdiff.mp h).1]
    exact sum_le_sum (fun _ _ => card_filter_le _ _)
  · contrapose! hs
    obtain ⟨s, hs⟩ := powersetCard_nonempty.mpr hs
    have hs' : s in p.powersetCard t := powersetCard_mono (filter_subset _ _) hs
    refine ⟨s, hs', fun w hw => ?_⟩
    obtain ⟨_, hadj, _⟩ := by
      rw [mem_powersetCard] at hs
      apply hs.1 at hw
      rwa [mem_filter, between_adj] at hw
    exact hadj.symm

Depends on / 依赖: CompleteEquipartiteSubgraph, CompleteEquipartiteSubgraph.verts, ErdosStone, ErdosStone.filter, Finset, Finset.mem_sdiff, add_lt_add_of_le_of_lt, and_not_self_iff, and_or_left, between_verts_isBipartiteWith, card_disjiUnion, card_neighborFinset_eq_degree, exists_prop, false_or, filter, filter_disjiUnion, isBipartiteWith_neighborFinset, mem_filter, mem_sdiff, not_and_or
-/
lemma degree_between_verts_lt_of_mem_sdiff
    {v : Fin n} (hv : v in K.vertsᶜ \ filter K t) (ht'_pos : 0 < t') :
    (G.between K.verts K.vertsᶜ).degree v < #K.verts - t' + t := by
  simp_rw [Finset.mem_sdiff, ErdosStone.filter, mem_filter, not_and_or, and_or_left,
    and_not_self_iff, false_or, not_forall, not_exists, not_and_or, not_forall, exists_prop] at hv
  obtain ⟨hv, p, hp, hs⟩ := hv
  rw [← card_neighborFinset_eq_degree]; rw [isBipartiteWith_neighborFinset' (between_verts_isBipartiteWith K) hv]
  conv =>
    enter [1, 1, 2]
    unfold CompleteEquipartiteSubgraph.verts
  rw [filter_disjiUnion]; rw [card_disjiUnion]; rw [sum_eq_sum_sdiff_singleton_add hp]
  apply add_lt_add_of_le_of_lt
  · conv_rhs =>
      rw [K.card_verts]; rw [← Nat.sub_one_mul]; rw [← K.card_parts.resolve_right ht'_pos.ne']; rw [← card_singleton p]; rw [← Finset.card_sdiff_of_subset (singleton_subset_iff.mpr hp)]; rw [← smul_eq_mul]; rw [← sum_const]; rw [← Finset.sum_congr rfl fun _ h => K.card_mem_parts (mem_sdiff.mp h).1]
    exact sum_le_sum (fun _ _ => card_filter_le _ _)
  · contrapose! hs
    obtain ⟨s, hs⟩ := powersetCard_nonempty.mpr hs
    have hs' : s in p.powersetCard t := powersetCard_mono (filter_subset _ _) hs
    refine ⟨s, hs', fun w hw => ?_⟩
    obtain ⟨_, hadj, _⟩ := by
      rw [mem_powersetCard] at hs
      apply hs.1 at hw
      rwa [mem_filter, between_adj] at hw
    exact hadj.symm

/--
lemma `card_edgeFinset_between_verts_le` / 引理 `card_edgeFinset_between_verts_le`

English:
lemma card_edgeFinset_between_verts_le
  given: (hr_pos : 0 < r) (ht'_pos : 0 < t')
  proof: calc (#(G.between K.verts K.vertsᶜ).edgeFinset : Real)
    _ = ∑ v in K.vertsᶜ \ filter K t, ((G.between K.verts K.vertsᶜ).degree v : Real)
      + ∑ v in filter K t, ((G.between K.verts K.vertsᶜ).degree v : Real) := by
        rw [ErdosStone.filter]; rw [sum_sdiff (filter_subset _ K.vertsᶜ)]; rw [eq_comm]
        exact_mod_cast isBipartiteWith_sum_degrees_eq_card_edges'
          (between_verts_isBipartiteWith K)
    _ <= ∑ _ in K.vertsᶜ \ filter K t, (#K.verts - t' + t : Real)
      + ∑ _ in filter K t, (#K.verts : Real) := by
        apply add_le_add <;> refine sum_le_sum (fun v hv => ?_)
        · rw [← Nat.cast_sub ((Nat.le_mul_of_pos_left t' hr_pos).trans_eq K.card_verts.symm)]
          exact_mod_cast (degree_between_verts_lt_of_mem_sdiff K hv ht'_pos).le
        · exact_mod_cast isBipartiteWith_degree_le'
            (between_verts_isBipartiteWith K) (filter_subset_compl_verts K hv)
    _ = (n - #K.verts) * (#K.verts - (t' - t))
      + #(filter K t) * (t' - t) := by
        rw [sum_const]; rw [nsmul_eq_mul]; rw [card_sdiff_of_subset (filter_subset_compl_verts K)]; rw [Nat.cast_sub (card_le_card (filter_subset_compl_verts K))]; rw [card_compl]; rw [Nat.cast_sub (card_le_univ K.verts)]; rw [Fintype.card_fin]; rw [sum_const]; rw [nsmul_eq_mul]; rw [sub_mul]; rw [sub_add (#K.verts : Real) _ _]; rw [mul_sub (#(filter K t) : Real) _ _]; rw [← sub_add]; rw [sub_add_eq_add_sub]; rw [sub_add_cancel]

中文:
引理 card_edgeFinset_between_verts_le
  条件: (hr_pos : 0 < r) (ht'_pos : 0 < t')
  证明: calc (#(G.between K.verts K.vertsᶜ).edgeFinset : Real)
    _ = ∑ v in K.vertsᶜ \ filter K t, ((G.between K.verts K.vertsᶜ).degree v : Real)
      + ∑ v in filter K t, ((G.between K.verts K.vertsᶜ).degree v : Real) := by
        rw [ErdosStone.filter]; rw [sum_sdiff (filter_subset _ K.vertsᶜ)]; rw [eq_comm]
        exact_mod_cast isBipartiteWith_sum_degrees_eq_card_edges'
          (between_verts_isBipartiteWith K)
    _ <= ∑ _ in K.vertsᶜ \ filter K t, (#K.verts - t' + t : Real)
      + ∑ _ in filter K t, (#K.verts : Real) := by
        apply add_le_add <;> refine sum_le_sum (fun v hv => ?_)
        · rw [← Nat.cast_sub ((Nat.le_mul_of_pos_left t' hr_pos).trans_eq K.card_verts.symm)]
          exact_mod_cast (degree_between_verts_lt_of_mem_sdiff K hv ht'_pos).le
        · exact_mod_cast isBipartiteWith_degree_le'
            (between_verts_isBipartiteWith K) (filter_subset_compl_verts K hv)
    _ = (n - #K.verts) * (#K.verts - (t' - t))
      + #(filter K t) * (t' - t) := by
        rw [sum_const]; rw [nsmul_eq_mul]; rw [card_sdiff_of_subset (filter_subset_compl_verts K)]; rw [Nat.cast_sub (card_le_card (filter_subset_compl_verts K))]; rw [card_compl]; rw [Nat.cast_sub (card_le_univ K.verts)]; rw [Fintype.card_fin]; rw [sum_const]; rw [nsmul_eq_mul]; rw [sub_mul]; rw [sub_add (#K.verts : Real) _ _]; rw [mul_sub (#(filter K t) : Real) _ _]; rw [← sub_add]; rw [sub_add_eq_add_sub]; rw [sub_add_cancel]

Depends on / 依赖: ErdosStone, ErdosStone.filter, G.between, K.verts, add_l, between, between_verts_isBipartiteWith, degree, edgeFinset, eq_comm, filter, filter_subset, isBipartiteWith_sum_degrees_eq_card_edges, sum_sdiff
-/
lemma card_edgeFinset_between_verts_le (hr_pos : 0 < r) (ht'_pos : 0 < t') :
    (#(G.between K.verts K.vertsᶜ).edgeFinset : Real)
      <= (n - #K.verts) * (#K.verts - (t' - t))
        + #(filter K t) * (t' - t) :=
  calc (#(G.between K.verts K.vertsᶜ).edgeFinset : Real)
    _ = ∑ v in K.vertsᶜ \ filter K t, ((G.between K.verts K.vertsᶜ).degree v : Real)
      + ∑ v in filter K t, ((G.between K.verts K.vertsᶜ).degree v : Real) := by
        rw [ErdosStone.filter]; rw [sum_sdiff (filter_subset _ K.vertsᶜ)]; rw [eq_comm]
        exact_mod_cast isBipartiteWith_sum_degrees_eq_card_edges'
          (between_verts_isBipartiteWith K)
    _ <= ∑ _ in K.vertsᶜ \ filter K t, (#K.verts - t' + t : Real)
      + ∑ _ in filter K t, (#K.verts : Real) := by
        apply add_le_add <;> refine sum_le_sum (fun v hv => ?_)
        · rw [← Nat.cast_sub ((Nat.le_mul_of_pos_left t' hr_pos).trans_eq K.card_verts.symm)]
          exact_mod_cast (degree_between_verts_lt_of_mem_sdiff K hv ht'_pos).le
        · exact_mod_cast isBipartiteWith_degree_le'
            (between_verts_isBipartiteWith K) (filter_subset_compl_verts K hv)
    _ = (n - #K.verts) * (#K.verts - (t' - t))
      + #(filter K t) * (t' - t) := by
        rw [sum_const]; rw [nsmul_eq_mul]; rw [card_sdiff_of_subset (filter_subset_compl_verts K)]; rw [Nat.cast_sub (card_le_card (filter_subset_compl_verts K))]; rw [card_compl]; rw [Nat.cast_sub (card_le_univ K.verts)]; rw [Fintype.card_fin]; rw [sum_const]; rw [nsmul_eq_mul]; rw [sub_mul]; rw [sub_add (#K.verts : Real) _ _]; rw [mul_sub (#(filter K t) : Real) _ _]; rw [← sub_add]; rw [sub_add_eq_add_sub]; rw [sub_add_cancel]

/--
lemma `mul_le_card_filter_mul` / 引理 `mul_le_card_filter_mul`

English:
lemma mul_le_card_filter_mul
  statement: (hr_pos : 0 < r) (ht'_pos : 0 < t')
  proof: calc (N * (t' - t) : Real)
    _ <= n * (r * t' * ε - t) - r * t' * (t' - t) := by
        rw [← add_sub_cancel_right (N : Real) (r * t' : Real)]; rw [sub_mul]
        exact sub_le_sub_right hN _
    _ = #K.verts * ((1 - 1 / r + ε) * n - #K.verts)
      - (n - #K.verts) * (#K.verts - (t' - t)) := by
        conv_rhs => rw [sub_eq_add_neg, ← neg_mul, neg_sub, sub_mul, mul_sub, ← add_sub_assoc,
          mul_sub, ← add_sub_assoc, sub_add_cancel, sub_right_comm, ← mul_assoc, ← mul_rotate,
          mul_assoc, ← mul_sub, mul_add, mul_sub (#K.verts : Real) _ _, mul_one,
          sub_add_eq_add_sub, add_sub_assoc, add_sub_sub_cancel, K.card_verts, Nat.cast_mul,
          mul_one_div, mul_div_cancel_left₀ (t' : Real) (mod_cast hr_pos.ne'), sub_add_sub_cancel]
    _ <= #K.verts * (G.minDegree - #K.verts) - (n - #K.verts) * (#K.verts - (t' - t)) :=
        sub_le_sub_right (mul_le_mul_of_nonneg_left
          (sub_le_sub_right hδ _) (#K.verts).cast_nonneg) _
    _ <= #(filter K t) * (t' - t) :=
sub_left_le_of_le_add (le_card_edgeFinset_between_verts K).trans
          (card_edgeFinset_between_verts_le K hr_pos ht'_pos)

中文:
引理 mul_le_card_filter_mul
  结论: (hr_pos : 0 < r) (ht'_pos : 0 < t')
  证明: calc (N * (t' - t) : Real)
    _ <= n * (r * t' * ε - t) - r * t' * (t' - t) := by
        rw [← add_sub_cancel_right (N : Real) (r * t' : Real)]; rw [sub_mul]
        exact sub_le_sub_right hN _
    _ = #K.verts * ((1 - 1 / r + ε) * n - #K.verts)
      - (n - #K.verts) * (#K.verts - (t' - t)) := by
        conv_rhs => rw [sub_eq_add_neg, ← neg_mul, neg_sub, sub_mul, mul_sub, ← add_sub_assoc,
          mul_sub, ← add_sub_assoc, sub_add_cancel, sub_right_comm, ← mul_assoc, ← mul_rotate,
          mul_assoc, ← mul_sub, mul_add, mul_sub (#K.verts : Real) _ _, mul_one,
          sub_add_eq_add_sub, add_sub_assoc, add_sub_sub_cancel, K.card_verts, Nat.cast_mul,
          mul_one_div, mul_div_cancel_left₀ (t' : Real) (mod_cast hr_pos.ne'), sub_add_sub_cancel]
    _ <= #K.verts * (G.minDegree - #K.verts) - (n - #K.verts) * (#K.verts - (t' - t)) :=
        sub_le_sub_right (mul_le_mul_of_nonneg_left
          (sub_le_sub_right hδ _) (#K.verts).cast_nonneg) _
    _ <= #(filter K t) * (t' - t) :=
sub_left_le_of_le_add (le_card_edgeFinset_between_verts K).trans
          (card_edgeFinset_between_verts_le K hr_pos ht'_pos)

Depends on / 依赖: K.verts, add_sub_assoc, add_sub_cancel_right, conv_rhs, mul_add, mul_assoc, mul_rotate, mul_sub, neg_mul, neg_sub, sub_add_cancel, sub_eq_add_neg, sub_le_sub_right, sub_mul, sub_right_comm
-/
lemma mul_le_card_filter_mul (hr_pos : 0 < r) (ht'_pos : 0 < t')
    (hδ : G.minDegree >= (1 - 1 / r + ε) * n)
    {N : Nat} (hN : (N + r * t') * (t' - t) <= n * (r * t' * ε - t)) :
    (N * (t' - t) : Real) <= (#(filter K t) * (t' - t) : Real) :=
  calc (N * (t' - t) : Real)
    _ <= n * (r * t' * ε - t) - r * t' * (t' - t) := by
        rw [← add_sub_cancel_right (N : Real) (r * t' : Real)]; rw [sub_mul]
        exact sub_le_sub_right hN _
    _ = #K.verts * ((1 - 1 / r + ε) * n - #K.verts)
      - (n - #K.verts) * (#K.verts - (t' - t)) := by
        conv_rhs => rw [sub_eq_add_neg, ← neg_mul, neg_sub, sub_mul, mul_sub, ← add_sub_assoc,
          mul_sub, ← add_sub_assoc, sub_add_cancel, sub_right_comm, ← mul_assoc, ← mul_rotate,
          mul_assoc, ← mul_sub, mul_add, mul_sub (#K.verts : Real) _ _, mul_one,
          sub_add_eq_add_sub, add_sub_assoc, add_sub_sub_cancel, K.card_verts, Nat.cast_mul,
          mul_one_div, mul_div_cancel_left₀ (t' : Real) (mod_cast hr_pos.ne'), sub_add_sub_cancel]
    _ <= #K.verts * (G.minDegree - #K.verts) - (n - #K.verts) * (#K.verts - (t' - t)) :=
        sub_le_sub_right (mul_le_mul_of_nonneg_left
          (sub_le_sub_right hδ _) (#K.verts).cast_nonneg) _
    _ <= #(filter K t) * (t' - t) :=
sub_left_le_of_le_add (le_card_edgeFinset_between_verts K).trans
          (card_edgeFinset_between_verts_le K hr_pos ht'_pos)

/--
Definition of `filter.pi` / `filter.pi` 的定义

English:
definition filter.pi
  signature: :
  body: fun ⟨_, h⟩ =>
    let s := Multiset.of_mem_filter h
    ⟨fun p hp => (s p hp).choose, Finset.mem_pi.mpr fun p hp => (s p hp).choose_spec.1⟩

中文:
定义 filter.pi
  签名: :
  定义体: fun ⟨_, h⟩ =>
    let s := Multiset.of_mem_filter h
    ⟨fun p hp => (s p hp).choose, Finset.mem_pi.mpr fun p hp => (s p hp).choose_spec.1⟩

Depends on / 依赖: Finset, Finset.mem_pi.mpr, Multiset, Multiset.of_mem_filter, choose_spec, mem_pi, of_mem_filter
-/
noncomputable def filter.pi :
    filter K t -> K.parts.pi (·.powersetCard t) :=
  fun ⟨_, h⟩ =>
    let s := Multiset.of_mem_filter h
    ⟨fun p hp => (s p hp).choose, Finset.mem_pi.mpr fun p hp => (s p hp).choose_spec.1⟩

/--
theorem `filter.pi.mem_val` / 定理 `filter.pi.mem_val`

English:
theorem filter.pi.mem_val
  given: {p} (hp : p in K.parts) (w : filter K t)
  proof: let s := Multiset.of_mem_filter w.prop p hp
  s.choose_spec.right

中文:
定理 filter.pi.mem_val
  条件: {p} (hp : p in K.parts) (w : filter K t)
  证明: let s := Multiset.of_mem_filter w.prop p hp
  s.choose_spec.right

Depends on / 依赖: Multiset, Multiset.of_mem_filter, choose_spec, of_mem_filter, s.choose_spec.right, w.prop
-/
theorem filter.pi.mem_val {p} (hp : p in K.parts) (w : filter K t) :
    forall v in (filter.pi K w).val p hp, G.Adj w v :=
  let s := Multiset.of_mem_filter w.prop p hp
  s.choose_spec.right

/--
theorem `filter.pi.exists_le_card_fiber` / 定理 `filter.pi.exists_le_card_fiber`

English:
theorem filter.pi.exists_le_card_fiber
  statement: (hr_pos : 0 < r) (ht'_pos : 0 < t')
  proof: by
  have : Nonempty (K.parts.pi (·.powersetCard t)) := by
    simp_rw [nonempty_coe_sort, pi_nonempty, powersetCard_nonempty]
    intro p hp
    rw [K.card_mem_parts hp]
    exact ht_lt_t'.le
  apply exists_le_card_fiber_of_mul_le_card
  simp_rw [card_coe]
  calc #(K.parts.pi (·.powersetCard t)) * t
    _ = (∏ x in K.parts, (#x).choose t) * t := by
        simp_rw [Finset.card_pi, card_powersetCard]
    _ = (∏ p in K.parts, t'.choose t) * t :=
congrArg (· * t) prod_congr rfl
fun p hp => congrArg (Nat.choose · t) K.card_mem_parts hp
    _ <= t'.choose t ^ r * t := by
        rw [prod_const]; rw [K.card_parts.resolve_right ht'_pos.ne']
    _ <= #(filter K t) := by
        refine Nat.le_of_mul_le_mul_right ?_ (Nat.sub_pos_of_lt ht_lt_t')
        rw [← @Nat.cast_le Real]; rw [Nat.cast_mul _ (t' - t)]; rw [Nat.cast_mul _ (t' - t)]; rw [Nat.cast_sub ht_lt_t'.le]
        exact mul_le_card_filter_mul K hr_pos ht'_pos hδ (mod_cast hN)

中文:
定理 filter.pi.存在_le_card_fiber
  结论: (hr_pos : 0 < r) (ht'_pos : 0 < t')
  证明: by
  have : Nonempty (K.parts.pi (·.powersetCard t)) := by
    simp_rw [nonempty_coe_sort, pi_nonempty, powersetCard_nonempty]
    intro p hp
    rw [K.card_mem_parts hp]
    exact ht_lt_t'.le
  apply exists_le_card_fiber_of_mul_le_card
  simp_rw [card_coe]
  calc #(K.parts.pi (·.powersetCard t)) * t
    _ = (∏ x in K.parts, (#x).choose t) * t := by
        simp_rw [Finset.card_pi, card_powersetCard]
    _ = (∏ p in K.parts, t'.choose t) * t :=
congrArg (· * t) prod_congr rfl
fun p hp => congrArg (Nat.choose · t) K.card_mem_parts hp
    _ <= t'.choose t ^ r * t := by
        rw [prod_const]; rw [K.card_parts.resolve_right ht'_pos.ne']
    _ <= #(filter K t) := by
        refine Nat.le_of_mul_le_mul_right ?_ (Nat.sub_pos_of_lt ht_lt_t')
        rw [← @Nat.cast_le Real]; rw [Nat.cast_mul _ (t' - t)]; rw [Nat.cast_mul _ (t' - t)]; rw [Nat.cast_sub ht_lt_t'.le]
        exact mul_le_card_filter_mul K hr_pos ht'_pos hδ (mod_cast hN)

Depends on / 依赖: Finset, Finset.card_pi, K.card_mem_parts, K.parts, K.parts.pi, Nat.choose, Nonempty, card_coe, card_mem_parts, card_pi, card_powersetCard, exists_le_card_fiber_of_mul_le_card, ht_lt_t, nonempty_coe_sort, pi_nonempty, powersetCard, powersetCard_nonempty, prod_congr, simp_rw
-/
theorem filter.pi.exists_le_card_fiber (hr_pos : 0 < r) (ht'_pos : 0 < t')
    (ht_lt_t' : t < t') (hδ : G.minDegree >= (1 - 1 / r + ε) * n)
    (hN : (t'.choose t ^ r * t + r * t') * (t' - t) <= n * (r * t' * ε - t)) :
    exists y : K.parts.pi (·.powersetCard t), t <= #{ w | filter.pi K w = y } := by
  have : Nonempty (K.parts.pi (·.powersetCard t)) := by
    simp_rw [nonempty_coe_sort, pi_nonempty, powersetCard_nonempty]
    intro p hp
    rw [K.card_mem_parts hp]
    exact ht_lt_t'.le
  apply exists_le_card_fiber_of_mul_le_card
  simp_rw [card_coe]
  calc #(K.parts.pi (·.powersetCard t)) * t
    _ = (∏ x in K.parts, (#x).choose t) * t := by
        simp_rw [Finset.card_pi, card_powersetCard]
    _ = (∏ p in K.parts, t'.choose t) * t :=
congrArg (· * t) prod_congr rfl
fun p hp => congrArg (Nat.choose · t) K.card_mem_parts hp
    _ <= t'.choose t ^ r * t := by
        rw [prod_const]; rw [K.card_parts.resolve_right ht'_pos.ne']
    _ <= #(filter K t) := by
        refine Nat.le_of_mul_le_mul_right ?_ (Nat.sub_pos_of_lt ht_lt_t')
        rw [← @Nat.cast_le Real]; rw [Nat.cast_mul _ (t' - t)]; rw [Nat.cast_mul _ (t' - t)]; rw [Nat.cast_sub ht_lt_t'.le]
        exact mul_le_card_filter_mul K hr_pos ht'_pos hδ (mod_cast hN)

end ErdosStone

set_option backward.isDefEq.respectTransparency.types false in
/-- If `G` has a minimal degree of at least `(1 - 1 / r + o(1)) * n`, then `G` contains a
copy of a `completeEquipartiteGraph` in `r + 1` parts each of size `t`.

This is the minimal-degree version of the **Erdős-Stone theorem**. -/
public theorem eventually_completeEquipartiteGraph_isContained_of_minDegree
    {ε : Real} (hε : 0 < ε) (r t : Nat) :
    forallᶠ n in atTop, forall {G : SimpleGraph (Fin n)} [DecidableRel G.Adj],
      G.minDegree >= (1 - 1 / r + ε) * n
        -> completeEquipartiteGraph (r + 1) t ⊑ G := by
  rcases show (r = 0 ∨ t = 0) ∨ r != 0 ∧ t != 0 by tauto with h0 | ⟨hr_pos, ht_pos⟩
  · rw [← Nat.le_zero_eq, ← @Nat.add_le_add_iff_right r 0 1, zero_add] at h0
    rw [eventually_atTop]
    refine ⟨(r + 1) * t, fun n hn {G} _ _ => ?_⟩
    rw [completeEquipartiteGraph_eq_bot_iff.mpr h0]; rw [bot_isContained_iff_card_le]; rw [card_prod]; rw [Fintype.card_fin]; rw [Fintype.card_fin]; rw [Fintype.card_fin]
    exact hn
  · rw [← Nat.pos_iff_ne_zero] at hr_pos ht_pos
    -- choose `ε'` to ensure `G.minDegree` is large enough
    let ε' := 1 / (↑(r - 1) * r) + ε
    have hε' : 0 < ε' := by positivity
    -- choose `t'` larger than `t / (r * ε)`
    let t' := ⌊t / (r * ε)⌋₊ + 1
    have ht_lt_rt'ε : t < r * t' * ε := by
      rw [mul_comm (r : Real) (t' : Real)]; rw [mul_assoc]; rw [← div_lt_iff₀ (by positivity)]; rw [Nat.cast_add_one]
      exact Nat.lt_floor_add_one (t / (r * ε))
    have ht'_pos : 0 < t' := by positivity
have ⟨N', ih⟩ := eventually_atTop.mp
      eventually_completeEquipartiteGraph_isContained_of_minDegree hε' (r - 1) t'
    -- choose `N` at least `(t'.choose t ^ r * t + r * t') * (t '- t) / (r * t' * ε - t)` to
    -- satisfy the pigeonhole principle
    let N := max (max 1 N') ⌈(t'.choose t ^ r * t + r * t') * (t' - t) / (r * t' * ε - t)⌉₊
    refine eventually_atTop.mpr ⟨N, fun n hn {G} _ hδ => ?_⟩
    have : Nonempty (Fin n) := by
      rw [← Fin.pos_iff_nonempty]
      exact hn.trans_lt' (lt_max_of_lt_left (lt_max_of_lt_left zero_lt_one))
    -- `r` is less than `1 / ε` otherwise `G.minDegree = n`
    have hrε_lt_1 : r * ε < 1 := by
      have hδ_lt_card : (G.minDegree : Real) < (n : Real) := by
        conv_rhs =>
          rw [← Fintype.card_fin n]
        exact_mod_cast G.minDegree_lt_card
      contrapose! hδ_lt_card with h1_le_rε
      rw [← div_le_iff₀' (by positivity)]; rw [← sub_nonpos]; rw [← le_sub_self_iff 1]; rw [← sub_add] at h1_le_rε
      exact hδ.trans' (le_mul_of_one_le_left n.cast_nonneg h1_le_rε)
    have ht_lt_t' : t < t' := by
      rw [mul_comm (r : Real) (t' : Real)]; rw [mul_assoc] at ht_lt_rt'ε
      exact_mod_cast ht_lt_rt'ε.trans_le (mul_le_of_le_one_right (mod_cast ht'_pos.le) hrε_lt_1.le)
    -- identify a `completeEquipartiteGraph r t'` in `G` from the inductive hypothesis
    replace ih : completeEquipartiteGraph r t' ⊑ G := by
      rcases eq_or_ne r 1 with hr_eq_1 | hr_ne_1
      -- if `r = 1` then `completeEquipartiteGraph r t' = ⊥`
      · have h0 : r <= 1 ∨ t' = 0 := Or.inl hr_eq_1.le
        rw [completeEquipartiteGraph_eq_bot_iff.mpr h0]; rw [bot_isContained_iff_card_le]; rw [card_prod]; rw [Fintype.card_fin]; rw [Fintype.card_fin]; rw [hr_eq_1]; rw [one_mul]; rw [Fintype.card_fin]
        apply hn.trans'
        exact_mod_cast calc (t' : Real)
          _ <= r * t' := le_mul_of_one_le_left (by positivity) (mod_cast hr_pos)
          _ <= t'.choose t ^ r * t + r * t' := le_add_of_nonneg_left (by positivity)
          _ <= (t'.choose t ^ r * t + r * t') * (t' - t) / (r * t' * ε - t) := by
            rw [mul_div_assoc]; rw [le_mul_iff_one_le_right (by positivity)]; rw [one_le_div (sub_pos.mpr ht_lt_rt'ε)]; rw [sub_le_sub_iff_right]; rw [mul_comm (r : Real) (t' : Real)]; rw [mul_assoc]; rw [mul_le_iff_le_one_right (by positivity)]
            exact hrε_lt_1.le
          _ <= ⌈(t'.choose t ^ r * t + r * t') * (t' - t) / (r * t' * ε - t)⌉₊ := Nat.le_ceil _
          _ <= N := Nat.cast_le.mpr (le_max_right _ _)
      -- if `r > 1` then `G` satisfies the inductive hypothesis
      · have hδ' := calc (G.minDegree : Real)
          _ >= (1 - 1 / (r - 1) + (1 / (r - 1) - 1 / r) + ε) * n := by
              rwa [← sub_add_sub_cancel _ (1 / (r - 1) : Real) _] at hδ
          _ = (1 - 1 / ↑(r - 1) + ε') * n := by
              rw [← one_div_mul_sub_mul_one_div_eq_one_div_add_one_div
                (sub_ne_zero_of_ne (mod_cast hr_ne_1)) (mod_cast hr_pos.ne')]; rw [sub_sub_cancel]; rw [mul_one]; rw [one_div_mul_one_div_rev]; rw [mul_comm (r : Real) _]; rw [← Nat.cast_pred hr_pos]; rw [add_assoc]
        rw [← Nat.succ_pred_eq_of_pos hr_pos]
        exact ih n (hn.trans' (le_max_of_le_left (le_max_right 1 N'))) hδ'
    obtain ⟨K⟩ := completeEquipartiteGraph_isContained_iff.mp ih
    -- find `t` vertices not in `K` adjacent to `t` vertices in each `K.parts` using the
    -- pigeonhole principle
    obtain ⟨⟨y, hy⟩, ht_le_card_filter⟩ := by
      apply ErdosStone.filter.pi.exists_le_card_fiber K hr_pos ht'_pos ht_lt_t' hδ
      rw [← div_le_iff₀ (sub_pos_of_lt ht_lt_rt'ε)]
      trans (N : Real)
      · exact (Nat.le_ceil _).trans (Nat.cast_le.mpr <| le_max_right _ _)
      · exact_mod_cast hn
    rw [Finset.mem_pi] at hy
    have ⟨s, hs_subset, hcards⟩ := exists_subset_card_eq ht_le_card_filter
    -- identify the `t` vertices in each `K.parts` as a `CompleteEquipartiteSubgraph r t` in `K`
    let K' : G.CompleteEquipartiteSubgraph r t := by
      refine ⟨univ.map ⟨fun p : K.parts => y p.val p.prop, fun p₁ p₂ (heq : y p₁ _ = y p₂ _) => ?_⟩,
        ?_, fun {p} hp => ?_, fun p₁ hp₁ p₂ hp₂ hne v₁ hv₁ v₂ hv₂ => ?_⟩
      · have hy₁' := mem_powersetCard.mp (hy p₁.val p₁.prop)
        have hy₂' := mem_powersetCard.mp (hy p₂.val p₂.prop)
        rw [← heq] at hy₂'
        obtain ⟨v, hv⟩ : (y p₁ _).Nonempty := by
          rw [← Finset.card_pos]; rw [hy₁'.right]
          exact ht_pos
        by_contra! hne
        absurd K.isCompleteBetween p₁.prop p₂.prop
          (Subtype.ext_iff.ne.mp hne) (hy₁'.left hv) (hy₂'.left hv)
        exact G.loopless.irrefl v
      · simp_rw [card_map, card_univ, card_coe]
        exact .inl (K.card_parts.resolve_right ht'_pos.ne')
      · simp_rw [univ_eq_attach, Finset.mem_map, mem_attach,
          Function.Embedding.coeFn_mk, true_and, Subtype.exists] at hp
        replace ⟨p, hp, hyp⟩ := hp
        rw [← hyp]
        have hy' := mem_powersetCard.mp (hy p hp)
        exact hy'.right
      · simp_rw [univ_eq_attach, coe_map, Function.Embedding.coeFn_mk,
          Set.mem_image, mem_coe, mem_attach, true_and, Subtype.exists] at hp₁ hp₂
        replace ⟨p₁, hp₁, hyp₁⟩ := hp₁
        rw [← hyp₁] at hv₁ hne
        have hy₁' := mem_powersetCard.mp (hy p₁ hp₁)
        replace ⟨p₂, hp₂, hyp₂⟩ := hp₂
        rw [← hyp₂] at hv₂ hne
        have hy₂' := mem_powersetCard.mp (hy p₂ hp₂)
        refine K.isCompleteBetween hp₁ hp₂ ?_ (hy₁'.left hv₁) (hy₂'.left hv₂)
        by_contra! heq
        simp [← heq] at hne
    -- identify the `t` vertices not in `K` and the `CompleteEquipartiteSubgraph r t` in `K`
    -- as a `CompleteEquipartiteSubgraph (r + 1) t` in `G`
    refine completeEquipartiteGraph_succ_isContained_iff.mpr
      ⟨K', s.map (.subtype _), by rwa [← card_map] at hcards, fun p' hp' v hv w hw => ?_⟩
    obtain ⟨w', hw'_mem, (hw'_eq : ↑w' = w)⟩ := Finset.mem_map.mp hw
    simp_rw [K', univ_eq_attach, Finset.mem_map, mem_attach,
      Function.Embedding.coeFn_mk, true_and, Subtype.exists] at hp'
    obtain ⟨p, hp, hp'_eq⟩ : exists p, exists (h : p in K.parts), y p h = p' := hp'
    apply hs_subset at hw'_mem
    simp_rw [mem_filter, mem_univ, true_and, ErdosStone.filter.pi, Subtype.mk.injEq] at hw'_mem
    rw [← hp'_eq]; rw [mem_coe]; rw [← hw'_mem] at hv
    rw [← hw'_eq]
    exact (ErdosStone.filter.pi.mem_val K hp w' v hv).symm

end ErdosStone

end SimpleGraph
