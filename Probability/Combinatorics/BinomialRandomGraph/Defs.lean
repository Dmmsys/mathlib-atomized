/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Sym.Card
public import Mathlib.MeasureTheory.Constructions.SimpleGraph
public import Mathlib.Probability.Distributions.SetBernoulli

/-!
# Binomial random graphs

This file constructs the binomial distribution with parameter `p` on simple graphs with
vertices `V`. This is the law `G(V, p)` of binomial random graphs with probability `p`.

## TODO

Add the characteristic predicate for a random graph to follow the binomial random distribution.

## Historical note

This is usually called the Erdős–Rényi model, but this name is historically inaccurate as Erdős and
Rényi introduced a closely related but different model. We therefore choose the name
"binomial random graph" to avoid confusion with this other model and because it is a more
descriptive name.

## Tags

Erdős-Rényi graph, Erdős-Renyi graph, Erdös-Rényi graph, Erdös-Renyi graph, Erdos-Rényi graph,
Erdos-Renyi graph
-/

public section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped Finset

namespace SimpleGraph
variable {V : Type*} {p : I}

variable (V p) in
/-- The binomial distribution with parameter `p` on simple graphs with vertices `V`. -/
@[expose]
/--
Definition of `binomialRandom` / `binomialRandom` 的定义

English:
definition binomialRandom
  signature: : Measure (SimpleGraph V)
  body: setBer(Sym2.diagSetᶜ, p).comap edgeSet

@[inherit_doc] scoped notation "G(" V ", " p ")" => binomialRandom V p

中文:
定义 binomialRandom
  签名: : 测度 (简单图 V)
  定义体: setBer(Sym2.diagSetᶜ, p).comap edgeSet

@[inherit_doc] scoped notation "G(" V ", " p ")" => binomialRandom V p

Depends on / 依赖: Sym2.diagSet, edgeSet, setBer
-/
noncomputable def binomialRandom : Measure (SimpleGraph V) :=
  setBer(Sym2.diagSetᶜ, p).comap edgeSet

@[inherit_doc] scoped notation "G(" V ", " p ")" => binomialRandom V p

section Countable
variable [Countable V]

variable (V p) in
/--
lemma `binomialRandom_eq_map` / 引理 `binomialRandom_eq_map`

English:
lemma binomialRandom_eq_map
  statement: G(V, p) = map fromEdgeSet setBer(Sym2.diagSetᶜ, p)
  proof: by
  refine (map_eq_comap measurable_fromEdgeSet measurableEmbedding_edgeSet ?_
    fromEdgeSet_edgeSet).symm
  filter_upwards [setBernoulli_ae_subset] with S hS
  exact ⟨fromEdgeSet S, by simpa [← Set.compl_ofPred, Set.subset_compl_iff_disjoint_right] using hS⟩

中文:
引理 binomialRandom_eq_map
  结论: G(V, p) = map fromEdgeSet setBer(Sym2.diagSetᶜ, p)
  证明: by
  refine (map_eq_comap measurable_fromEdgeSet measurableEmbedding_edgeSet ?_
    fromEdgeSet_edgeSet).symm
  filter_upwards [setBernoulli_ae_subset] with S hS
  exact ⟨fromEdgeSet S, by simpa [← Set.compl_ofPred, Set.subset_compl_iff_disjoint_right] using hS⟩

Depends on / 依赖: Set.compl_ofPred, Set.subset_compl_iff_disjoint_right, compl_ofPred, filter_upwards, fromEdgeSet, fromEdgeSet_edgeSet, map_eq_comap, measurableEmbedding_edgeSet, measurable_fromEdgeSet, setBernoulli_ae_subset, subset_compl_iff_disjoint_right
-/
lemma binomialRandom_eq_map : G(V, p) = map fromEdgeSet setBer(Sym2.diagSetᶜ, p) := by
  refine (map_eq_comap measurable_fromEdgeSet measurableEmbedding_edgeSet ?_
    fromEdgeSet_edgeSet).symm
  filter_upwards [setBernoulli_ae_subset] with S hS
  exact ⟨fromEdgeSet S, by simpa [← Set.compl_ofPred, Set.subset_compl_iff_disjoint_right] using hS⟩

variable (p) in
/--
lemma `binomialRandom_apply'` / 引理 `binomialRandom_apply'`

English:
lemma binomialRandom_apply'
  given: (S : Set (SimpleGraph V))
  proof: by
  rw [binomialRandom]; rw [measurableEmbedding_edgeSet.comap_apply]

中文:
引理 binomialRandom_apply'
  条件: (S : 集合 (简单图 V))
  证明: by
  rw [binomialRandom]; rw [measurableEmbedding_edgeSet.comap_apply]

Depends on / 依赖: binomialRandom, comap_apply, measurableEmbedding_edgeSet, measurableEmbedding_edgeSet.comap_apply
-/
lemma binomialRandom_apply' (S : Set (SimpleGraph V)) :
    G(V, p) S = setBer(Sym2.diagSetᶜ, p) (edgeSet '' S) := by
  rw [binomialRandom]; rw [measurableEmbedding_edgeSet.comap_apply]

variable (p) in
/--
lemma `binomialRandom_apply` / 引理 `binomialRandom_apply`

English:
lemma binomialRandom_apply
  given: (S : Set (SimpleGraph V))
  proof: by
  simp [binomialRandom_apply', setBernoulli_apply, ← Set.image_comp]

中文:
引理 binomialRandom_apply
  条件: (S : 集合 (简单图 V))
  证明: by
  simp [binomialRandom_apply', setBernoulli_apply, ← Set.image_comp]

Depends on / 依赖: Set.image_comp, binomialRandom_apply, image_comp, setBernoulli_apply
-/
lemma binomialRandom_apply (S : Set (SimpleGraph V)) :
    G(V, p) S = infinitePi
      (fun e : Sym2 V => toNNReal p • .dirac (¬ e.IsDiag) + toNNReal (σ p) • .dirac False)
      ((fun G e => e in G.edgeSet) '' S) := by
  simp [binomialRandom_apply', setBernoulli_apply, ← Set.image_comp]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsProbabilityMeasure G(V, p)
  body: by
  refine measurableEmbedding_edgeSet.isProbabilityMeasure_comap ?_
  filter_upwards [setBernoulli_ae_subset] with s hs
  refine ⟨.fromEdgeSet s, ?_⟩
  simpa [← Set.disjoint_compl_right_iff_subset, ← Set.compl_ofPred] using hs

中文:
实例 :
  签名: 是概率测度 G(V, p)
  定义体: by
  refine measurableEmbedding_edgeSet.isProbabilityMeasure_comap ?_
  filter_upwards [setBernoulli_ae_subset] with s hs
  refine ⟨.fromEdgeSet s, ?_⟩
  simpa [← Set.disjoint_compl_right_iff_subset, ← Set.compl_ofPred] using hs

Depends on / 依赖: Set.compl_ofPred, Set.disjoint_compl_right_iff_subset, compl_ofPred, disjoint_compl_right_iff_subset, filter_upwards, fromEdgeSet, isProbabilityMeasure_comap, measurableEmbedding_edgeSet, measurableEmbedding_edgeSet.isProbabilityMeasure_comap, setBernoulli_ae_subset
-/
instance : IsProbabilityMeasure G(V, p) := by
  refine measurableEmbedding_edgeSet.isProbabilityMeasure_comap ?_
  filter_upwards [setBernoulli_ae_subset] with s hs
  refine ⟨.fromEdgeSet s, ?_⟩
  simpa [← Set.disjoint_compl_right_iff_subset, ← Set.compl_ofPred] using hs

variable (V) in
/--
lemma `binomialRandom_zero` / 引理 `binomialRandom_zero`

English:
lemma binomialRandom_zero
  statement: G(V, 0) = dirac ⊥
  proof: by simp [binomialRandom_eq_map]

中文:
引理 binomialRandom_zero
  结论: G(V, 0) = dirac ⊥
  证明: by simp [binomialRandom_eq_map]
-/
@[simp] lemma binomialRandom_zero : G(V, 0) = dirac ⊥ := by simp [binomialRandom_eq_map]

variable (V) in
/--
lemma `binomialRandom_one` / 引理 `binomialRandom_one`

English:
lemma binomialRandom_one
  statement: G(V, 1) = dirac ⊤
  proof: by simp [binomialRandom_eq_map]

中文:
引理 binomialRandom_one
  结论: G(V, 1) = dirac ⊤
  证明: by simp [binomialRandom_eq_map]
-/
@[simp] lemma binomialRandom_one : G(V, 1) = dirac ⊤ := by simp [binomialRandom_eq_map]

end Countable

variable (p) in
/--
lemma `binomialRandom_singleton` / 引理 `binomialRandom_singleton`

English:
lemma binomialRandom_singleton
  given: [Finite V] (G : SimpleGraph V)
  proof: by
  classical
  cases nonempty_fintype V
  simp only [binomialRandom, measurableEmbedding_edgeSet.comap_apply, Set.image_singleton,
    edgeSet_subset_compl_diagSet, setBernoulli_singleton, Set.toFinite]
  rw [Set.ncard_sdiff (by simp)]
  congr!
  rw [Nat.card_eq_fintype_card]; rw [← Sym2.card_diag

中文:
引理 binomialRandom_singleton
  条件: [有限 V] (G : 简单图 V)
  证明: by
  classical
  cases nonempty_fintype V
  simp only [binomialRandom, measurableEmbedding_edgeSet.comap_apply, Set.image_singleton,
    edgeSet_subset_compl_diagSet, setBernoulli_singleton, Set.toFinite]
  rw [Set.ncard_sdiff (by simp)]
  congr!
  rw [Nat.card_eq_fintype_card]; rw [← Sym2.card_diag
-/
@[simp] lemma binomialRandom_singleton [Finite V] (G : SimpleGraph V) :
    G(V, p) {G} = toNNReal p ^ G.edgeSet.ncard *
      toNNReal (σ p) ^ ((Nat.card V).choose 2 - G.edgeSet.ncard) := by
  classical
  cases nonempty_fintype V
  simp only [binomialRandom, measurableEmbedding_edgeSet.comap_apply, Set.image_singleton,
    edgeSet_subset_compl_diagSet, setBernoulli_singleton, Set.toFinite]
  rw [Set.ncard_sdiff (by simp)]
  congr!
  rw [Nat.card_eq_fintype_card]; rw [← Sym2.card_diagSet_compl]; rw [Fintype.card_eq_nat_card]; rw [← Nat.card_coe_set_eq]

-- This should be restated as an equality of distributions once
-- https://github.com/leanprover-community/mathlib4/pull/28248 is in.
proof_wanted binomialRandom_map_ncard_edgeSet_singleton [Finite V] (n : Nat) :
    G(V, p).map (fun G => G.edgeSet.ncard) {n} = ((Nat.card V).choose 2).choose n * toNNReal p ^ n *
      toNNReal (σ p) ^ ((Nat.card V).choose 2 - n)

end SimpleGraph
