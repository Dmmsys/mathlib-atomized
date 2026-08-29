/-
Copyright (c) 2024 Rida Hamadani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rida Hamadani
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# Diameter of a simple graph

This module defines the eccentricity of vertices, the diameter, and the radius of a simple graph.

## Main definitions

- `SimpleGraph.eccent`: the eccentricity of a vertex in a simple graph, which is the maximum
  distances between it and the other vertices.

- `SimpleGraph.ediam`: the graph extended diameter, which is the maximum eccentricity.
  It is `ℕ∞`-valued.

- `SimpleGraph.diam`: the graph diameter, an `ℕ`-valued version of `SimpleGraph.ediam`.

- `SimpleGraph.radius`: the graph radius, which is the minimum eccentricity. It is `ℕ∞`-valued.

- `SimpleGraph.center`: the set of vertices with eccentricity equal to the graph's radius.

-/

@[expose] public section

assert_not_exists Field

namespace SimpleGraph
variable {α : Type*} {G G' : SimpleGraph α}

section eccent

/--
Definition of `eccent` / `eccent` 的定义

English:
definition eccent
  signature: (G : SimpleGraph α) (u : α)
  body: ⨆ v, G.edist u v

中文:
定义 eccent
  签名: (G : SimpleGraph α) (u : α)
  定义体: ⨆ v, G.edist u v

Depends on / 依赖: G.edist
-/
noncomputable def eccent (G : SimpleGraph α) (u : α) : Nat∞ :=
  ⨆ v, G.edist u v

/--
lemma `eccent_def` / 引理 `eccent_def`

English:
lemma eccent_def
  statement: G.eccent = fun u => ⨆ v, G.edist u v
  proof: rfl

中文:
引理 eccent_def
  结论: G.eccent = fun u => ⨆ v, G.edist u v
  证明: rfl
-/
lemma eccent_def : G.eccent = fun u => ⨆ v, G.edist u v := rfl

/--
lemma `edist_le_eccent` / 引理 `edist_le_eccent`

English:
lemma edist_le_eccent
  given: {u v : α}
  statement: G.edist u v <= G.eccent u
  proof: le_iSup (G.edist u) v

中文:
引理 edist_le_eccent
  条件: {u v : α}
  结论: G.edist u v <= G.eccent u
  证明: le_iSup (G.edist u) v

Depends on / 依赖: G.edist, le_iSup
-/
lemma edist_le_eccent {u v : α} : G.edist u v <= G.eccent u :=
  le_iSup (G.edist u) v

/--
lemma `exists_edist_eq_eccent_of_finite` / 引理 `exists_edist_eq_eccent_of_finite`

English:
lemma exists_edist_eq_eccent_of_finite
  given: [Finite α] (u : α)
  proof: have : Nonempty α := Nonempty.intro u
  exists_eq_ciSup_of_finite

中文:
引理 exists_edist_eq_eccent_of_finite
  条件: [Finite α] (u : α)
  证明: have : Nonempty α := Nonempty.intro u
  exists_eq_ciSup_of_finite

Depends on / 依赖: Nonempty, Nonempty.intro, exists_eq_ciSup_of_finite
-/
lemma exists_edist_eq_eccent_of_finite [Finite α] (u : α) :
    exists v, G.edist u v = G.eccent u :=
  have : Nonempty α := Nonempty.intro u
  exists_eq_ciSup_of_finite

/--
lemma `eccent_eq_top_of_not_connected` / 引理 `eccent_eq_top_of_not_connected`

English:
lemma eccent_eq_top_of_not_connected
  given: (h : ¬ G.Connected) (u : α)
  proof: by
  rw [connected_iff_exists_forall_reachable] at h
  push Not at h
  obtain ⟨v, h⟩ := h u
  rw [eq_top_iff]; rw [← edist_eq_top_of_not_reachable h]
  exact le_iSup (G.edist u) v

中文:
引理 eccent_eq_top_of_not_connected
  条件: (h : ¬ G.Connected) (u : α)
  证明: by
  rw [connected_iff_exists_forall_reachable] at h
  push Not at h
  obtain ⟨v, h⟩ := h u
  rw [eq_top_iff]; rw [← edist_eq_top_of_not_reachable h]
  exact le_iSup (G.edist u) v

Depends on / 依赖: G.edist, connected_iff_exists_forall_reachable, edist_eq_top_of_not_reachable, eq_top_iff, le_iSup
-/
lemma eccent_eq_top_of_not_connected (h : ¬ G.Connected) (u : α) :
    G.eccent u = ⊤ := by
  rw [connected_iff_exists_forall_reachable] at h
  push Not at h
  obtain ⟨v, h⟩ := h u
  rw [eq_top_iff]; rw [← edist_eq_top_of_not_reachable h]
  exact le_iSup (G.edist u) v

/--
lemma `eccent_eq_zero_of_subsingleton` / 引理 `eccent_eq_zero_of_subsingleton`

English:
lemma eccent_eq_zero_of_subsingleton
  given: [Subsingleton α] (u : α)
  statement: G.eccent u = 0
  proof: by
  simpa [eccent, edist_eq_zero_iff] using subsingleton_iff.mp ‹_› u

中文:
引理 eccent_eq_zero_of_subsingleton
  条件: [Subsingleton α] (u : α)
  结论: G.eccent u = 0
  证明: by
  simpa [eccent, edist_eq_zero_iff] using subsingleton_iff.mp ‹_› u

Depends on / 依赖: eccent, edist_eq_zero_iff, subsingleton_iff, subsingleton_iff.mp
-/
lemma eccent_eq_zero_of_subsingleton [Subsingleton α] (u : α) : G.eccent u = 0 := by
  simpa [eccent, edist_eq_zero_iff] using subsingleton_iff.mp ‹_› u

/--
lemma `eccent_ne_zero` / 引理 `eccent_ne_zero`

English:
lemma eccent_ne_zero
  given: [Nontrivial α] (u : α)
  statement: G.eccent u != 0
  proof: by
  obtain ⟨v, huv⟩ := exists_ne ‹_›
  contrapose huv
  simp only [eccent, ENat.iSup_eq_zero, edist_eq_zero_iff] at huv
  exact (huv v).symm

中文:
引理 eccent_ne_zero
  条件: [Nontrivial α] (u : α)
  结论: G.eccent u != 0
  证明: by
  obtain ⟨v, huv⟩ := exists_ne ‹_›
  contrapose huv
  simp only [eccent, ENat.iSup_eq_zero, edist_eq_zero_iff] at huv
  exact (huv v).symm

Depends on / 依赖: ENat.iSup_eq_zero, contrapose, eccent, edist_eq_zero_iff, exists_ne, iSup_eq_zero
-/
lemma eccent_ne_zero [Nontrivial α] (u : α) : G.eccent u != 0 := by
  obtain ⟨v, huv⟩ := exists_ne ‹_›
  contrapose huv
  simp only [eccent, ENat.iSup_eq_zero, edist_eq_zero_iff] at huv
  exact (huv v).symm

/--
lemma `eccent_eq_zero_iff` / 引理 `eccent_eq_zero_iff`

English:
lemma eccent_eq_zero_iff
  given: (u : α)
  statement: G.eccent u = 0 ↔ Subsingleton α
  proof: by
  refine ⟨fun h => ?_, fun _ => eccent_eq_zero_of_subsingleton u⟩
  contrapose! h
  exact eccent_ne_zero u

中文:
引理 eccent_eq_zero_iff
  条件: (u : α)
  结论: G.eccent u = 0 ↔ Subsingleton α
  证明: by
  refine ⟨fun h => ?_, fun _ => eccent_eq_zero_of_subsingleton u⟩
  contrapose! h
  exact eccent_ne_zero u

Depends on / 依赖: contrapose, eccent_eq_zero_of_subsingleton, eccent_ne_zero
-/
lemma eccent_eq_zero_iff (u : α) : G.eccent u = 0 ↔ Subsingleton α := by
  refine ⟨fun h => ?_, fun _ => eccent_eq_zero_of_subsingleton u⟩
  contrapose! h
  exact eccent_ne_zero u

/--
lemma `eccent_pos_iff` / 引理 `eccent_pos_iff`

English:
lemma eccent_pos_iff
  given: (u : α)
  statement: 0 < G.eccent u ↔ Nontrivial α
  proof: by
  rw [pos_iff_ne_zero]; rw [← not_subsingleton_iff_nontrivial]; rw [← eccent_eq_zero_iff]

@[simp]

中文:
引理 eccent_pos_iff
  条件: (u : α)
  结论: 0 < G.eccent u ↔ Nontrivial α
  证明: by
  rw [pos_iff_ne_zero]; rw [← not_subsingleton_iff_nontrivial]; rw [← eccent_eq_zero_iff]

@[simp]

Depends on / 依赖: eccent_eq_zero_iff, not_subsingleton_iff_nontrivial, pos_iff_ne_zero
-/
lemma eccent_pos_iff (u : α) : 0 < G.eccent u ↔ Nontrivial α := by
  rw [pos_iff_ne_zero]; rw [← not_subsingleton_iff_nontrivial]; rw [← eccent_eq_zero_iff]

@[simp]
/--
lemma `eccent_bot` / 引理 `eccent_bot`

English:
lemma eccent_bot
  given: [Nontrivial α] (u : α)
  statement: (⊥ : SimpleGraph α).eccent u = ⊤
  proof: eccent_eq_top_of_not_connected not_connected_bot u

@[simp]

中文:
引理 eccent_bot
  条件: [Nontrivial α] (u : α)
  结论: (⊥ : SimpleGraph α).eccent u = ⊤
  证明: eccent_eq_top_of_not_connected not_connected_bot u

@[simp]

Depends on / 依赖: eccent_eq_top_of_not_connected, not_connected_bot
-/
lemma eccent_bot [Nontrivial α] (u : α) : (⊥ : SimpleGraph α).eccent u = ⊤ :=
  eccent_eq_top_of_not_connected not_connected_bot u

@[simp]
/--
lemma `eccent_top` / 引理 `eccent_top`

English:
lemma eccent_top
  given: [Nontrivial α] (u : α)
  statement: (⊤ : SimpleGraph α).eccent u = 1
  proof: by
apply le_antisymm ?_ Order.one_le_iff_pos.mpr pos_iff_ne_zero.mpr eccent_ne_zero u
  rw [eccent]; rw [iSup_le_iff]
  intro v
  cases eq_or_ne u v <;> simp_all [edist_top_of_ne]

中文:
引理 eccent_top
  条件: [Nontrivial α] (u : α)
  结论: (⊤ : SimpleGraph α).eccent u = 1
  证明: by
apply le_antisymm ?_ Order.one_le_iff_pos.mpr pos_iff_ne_zero.mpr eccent_ne_zero u
  rw [eccent]; rw [iSup_le_iff]
  intro v
  cases eq_or_ne u v <;> simp_all [edist_top_of_ne]

Depends on / 依赖: Order.one_le_iff_pos.mpr, eccent, eccent_ne_zero, edist_top_of_ne, eq_or_ne, iSup_le_iff, le_antisymm, one_le_iff_pos, pos_iff_ne_zero, pos_iff_ne_zero.mpr
-/
lemma eccent_top [Nontrivial α] (u : α) : (⊤ : SimpleGraph α).eccent u = 1 := by
apply le_antisymm ?_ Order.one_le_iff_pos.mpr pos_iff_ne_zero.mpr eccent_ne_zero u
  rw [eccent]; rw [iSup_le_iff]
  intro v
  cases eq_or_ne u v <;> simp_all [edist_top_of_ne]

/--
lemma `eq_top_iff_forall_eccent_eq_one` / 引理 `eq_top_iff_forall_eccent_eq_one`

English:
lemma eq_top_iff_forall_eccent_eq_one
  given: [Nontrivial α]
  proof: by
  refine ⟨fun h => h ▸ eccent_top, fun h => ?_⟩
  ext u v
  refine ⟨Adj.ne, fun huv => ?_⟩
  rw [← edist_eq_one_iff_adj]
  apply le_antisymm ((h u).symm ▸ edist_le_eccent)
  rw [Order.one_le_iff_pos]; rw [pos_iff_ne_zero]; rw [edist_eq_zero_iff.ne]
  exact huv.ne

中文:
引理 eq_top_iff_forall_eccent_eq_one
  条件: [Nontrivial α]
  证明: by
  refine ⟨fun h => h ▸ eccent_top, fun h => ?_⟩
  ext u v
  refine ⟨Adj.ne, fun huv => ?_⟩
  rw [← edist_eq_one_iff_adj]
  apply le_antisymm ((h u).symm ▸ edist_le_eccent)
  rw [Order.one_le_iff_pos]; rw [pos_iff_ne_zero]; rw [edist_eq_zero_iff.ne]
  exact huv.ne

Depends on / 依赖: Adj.ne, Order.one_le_iff_pos, eccent_top, edist_eq_one_iff_adj, edist_eq_zero_iff, edist_eq_zero_iff.ne, edist_le_eccent, huv.ne, le_antisymm, one_le_iff_pos, pos_iff_ne_zero
-/
lemma eq_top_iff_forall_eccent_eq_one [Nontrivial α] :
    G = ⊤ ↔ forall u, G.eccent u = 1 := by
  refine ⟨fun h => h ▸ eccent_top, fun h => ?_⟩
  ext u v
  refine ⟨Adj.ne, fun huv => ?_⟩
  rw [← edist_eq_one_iff_adj]
  apply le_antisymm ((h u).symm ▸ edist_le_eccent)
  rw [Order.one_le_iff_pos]; rw [pos_iff_ne_zero]; rw [edist_eq_zero_iff.ne]
  exact huv.ne

/--
lemma `eccent_le_iff` / 引理 `eccent_le_iff`

English:
lemma eccent_le_iff
  given: (u : α) (k : Nat∞)
  statement: G.eccent u <= k ↔ forall v, G.edist u v <= k
  proof: iSup_le_iff

中文:
引理 eccent_le_iff
  条件: (u : α) (k : 自然数∞)
  结论: G.eccent u <= k ↔ 对任意 v, G.edist u v <= k
  证明: iSup_le_iff

Depends on / 依赖: iSup_le_iff
-/
lemma eccent_le_iff (u : α) (k : Nat∞) : G.eccent u <= k ↔ forall v, G.edist u v <= k :=
  iSup_le_iff

/--
lemma `eccent_le_one_iff` / 引理 `eccent_le_one_iff`

English:
lemma eccent_le_one_iff
  given: (u : α)
  statement: G.eccent u <= 1 ↔ forall v, u != v -> G.Adj u v
  proof: by
  constructor
  · intro h v huv
    have hd : G.edist u v <= 1 := edist_le_eccent.trans h
    have hd' : 1 <= G.edist u v := Order.one_le_iff_pos.mpr (G.edist_pos_of_ne huv)
    exact edist_eq_one_iff_adj.mp (le_antisymm (hd') hd).symm
  · intro hall
    rw [eccent_le_iff]
    intro v
    rw [edi

中文:
引理 eccent_le_one_iff
  条件: (u : α)
  结论: G.eccent u <= 1 ↔ 对任意 v, u != v -> G.Adj u v
  证明: by
  constructor
  · intro h v huv
    have hd : G.edist u v <= 1 := edist_le_eccent.trans h
    have hd' : 1 <= G.edist u v := Order.one_le_iff_pos.mpr (G.edist_pos_of_ne huv)
    exact edist_eq_one_iff_adj.mp (le_antisymm (hd') hd).symm
  · intro hall
    rw [eccent_le_iff]
    intro v
    rw [edi

Depends on / 依赖: G.edist, G.edist_pos_of_ne, Order.one_le_iff_pos.mpr, eccent_le_iff, edist_eq_one_iff_adj, edist_eq_one_iff_adj.mp, edist_le_eccent, edist_le_eccent.trans, edist_le_one_iff_adj_or_eq, edist_pos_of_ne, le_antisymm, one_le_iff_pos, or_iff_not_imp_right, or_iff_not_imp_right.mpr
-/
lemma eccent_le_one_iff (u : α) : G.eccent u <= 1 ↔ forall v, u != v -> G.Adj u v := by
  constructor
  · intro h v huv
    have hd : G.edist u v <= 1 := edist_le_eccent.trans h
    have hd' : 1 <= G.edist u v := Order.one_le_iff_pos.mpr (G.edist_pos_of_ne huv)
    exact edist_eq_one_iff_adj.mp (le_antisymm (hd') hd).symm
  · intro hall
    rw [eccent_le_iff]
    intro v
    rw [edist_le_one_iff_adj_or_eq]
    exact or_iff_not_imp_right.mpr (hall v)

/--
lemma `eccent_eq_one_iff` / 引理 `eccent_eq_one_iff`

English:
lemma eccent_eq_one_iff
  given: [Nontrivial α] (u : α)
  proof: by
  have h : 1 <= G.eccent u := Order.one_le_iff_ne_zero.mpr (eccent_ne_zero u)
  rw [← h.ge_iff_eq']
  exact eccent_le_one_iff u

中文:
引理 eccent_eq_one_iff
  条件: [Nontrivial α] (u : α)
  证明: by
  have h : 1 <= G.eccent u := Order.one_le_iff_ne_zero.mpr (eccent_ne_zero u)
  rw [← h.ge_iff_eq']
  exact eccent_le_one_iff u

Depends on / 依赖: G.eccent, Order.one_le_iff_ne_zero.mpr, eccent, eccent_le_one_iff, eccent_ne_zero, ge_iff_eq, h.ge_iff_eq, one_le_iff_ne_zero
-/
lemma eccent_eq_one_iff [Nontrivial α] (u : α) :
    G.eccent u = 1 ↔ forall v, u != v -> G.Adj u v := by
  have h : 1 <= G.eccent u := Order.one_le_iff_ne_zero.mpr (eccent_ne_zero u)
  rw [← h.ge_iff_eq']
  exact eccent_le_one_iff u

end eccent

section ediam

/--
Definition of `ediam` / `ediam` 的定义

English:
definition ediam
  signature: (G : SimpleGraph α)
  body: ⨆ u, G.eccent u

中文:
定义 ediam
  签名: (G : SimpleGraph α)
  定义体: ⨆ u, G.eccent u

Depends on / 依赖: G.eccent, eccent
-/
noncomputable def ediam (G : SimpleGraph α) : Nat∞ :=
  ⨆ u, G.eccent u

/--
lemma `ediam_eq_iSup_iSup_edist` / 引理 `ediam_eq_iSup_iSup_edist`

English:
lemma ediam_eq_iSup_iSup_edist
  statement: G.ediam = ⨆ u, ⨆ v, G.edist u v
  proof: rfl

中文:
引理 ediam_eq_iSup_iSup_edist
  结论: G.ediam = ⨆ u, ⨆ v, G.edist u v
  证明: rfl
-/
lemma ediam_eq_iSup_iSup_edist : G.ediam = ⨆ u, ⨆ v, G.edist u v :=
  rfl

/--
lemma `ediam_def` / 引理 `ediam_def`

English:
lemma ediam_def
  statement: G.ediam = ⨆ p : α × α, G.edist p.1 p.2
  proof: by
  rw [ediam]; rw [eccent_def]; rw [iSup_prod]

中文:
引理 ediam_def
  结论: G.ediam = ⨆ p : α × α, G.edist p.1 p.2
  证明: by
  rw [ediam]; rw [eccent_def]; rw [iSup_prod]

Depends on / 依赖: eccent_def, iSup_prod
-/
lemma ediam_def : G.ediam = ⨆ p : α × α, G.edist p.1 p.2 := by
  rw [ediam]; rw [eccent_def]; rw [iSup_prod]

/--
lemma `eccent_le_ediam` / 引理 `eccent_le_ediam`

English:
lemma eccent_le_ediam
  given: {u : α}
  statement: G.eccent u <= G.ediam
  proof: le_iSup G.eccent u

中文:
引理 eccent_le_ediam
  条件: {u : α}
  结论: G.eccent u <= G.ediam
  证明: le_iSup G.eccent u

Depends on / 依赖: G.eccent, eccent, le_iSup
-/
lemma eccent_le_ediam {u : α} : G.eccent u <= G.ediam :=
  le_iSup G.eccent u

/--
lemma `edist_le_ediam` / 引理 `edist_le_ediam`

English:
lemma edist_le_ediam
  given: {u v : α}
  statement: G.edist u v <= G.ediam
  proof: le_iSup₂ (f := G.edist) u v

中文:
引理 edist_le_ediam
  条件: {u v : α}
  结论: G.edist u v <= G.ediam
  证明: le_iSup₂ (f := G.edist) u v

Depends on / 依赖: G.edist
-/
lemma edist_le_ediam {u v : α} : G.edist u v <= G.ediam :=
  le_iSup₂ (f := G.edist) u v

/--
lemma `ediam_le_of_edist_le` / 引理 `ediam_le_of_edist_le`

English:
lemma ediam_le_of_edist_le
  given: {k : Nat∞} (h : forall u v, G.edist u v <= k)
  statement: G.ediam <= k
  proof: iSup₂_le h

中文:
引理 ediam_le_of_edist_le
  条件: {k : 自然数∞} (h : 对任意 u v, G.edist u v <= k)
  结论: G.ediam <= k
  证明: iSup₂_le h
-/
lemma ediam_le_of_edist_le {k : Nat∞} (h : forall u v, G.edist u v <= k) : G.ediam <= k :=
  iSup₂_le h

/--
lemma `ediam_le_iff` / 引理 `ediam_le_iff`

English:
lemma ediam_le_iff
  given: {k : Nat∞}
  statement: G.ediam <= k ↔ forall u v, G.edist u v <= k
  proof: iSup₂_le_iff

中文:
引理 ediam_le_iff
  条件: {k : 自然数∞}
  结论: G.ediam <= k ↔ 对任意 u v, G.edist u v <= k
  证明: iSup₂_le_iff
-/
lemma ediam_le_iff {k : Nat∞} : G.ediam <= k ↔ forall u v, G.edist u v <= k :=
  iSup₂_le_iff

/--
lemma `ediam_eq_top` / 引理 `ediam_eq_top`

English:
lemma ediam_eq_top
  statement: G.ediam = ⊤ ↔ forall b < ⊤, exists u v, b < G.edist u v
  proof: by
  simp only [ediam, eccent, iSup_eq_top, lt_iSup_iff]

中文:
引理 ediam_eq_top
  结论: G.ediam = ⊤ ↔ 对任意 b < ⊤, 存在 u v, b < G.edist u v
  证明: by
  simp only [ediam, eccent, iSup_eq_top, lt_iSup_iff]

Depends on / 依赖: eccent, iSup_eq_top, lt_iSup_iff
-/
lemma ediam_eq_top : G.ediam = ⊤ ↔ forall b < ⊤, exists u v, b < G.edist u v := by
  simp only [ediam, eccent, iSup_eq_top, lt_iSup_iff]

/--
lemma `ediam_eq_zero_of_subsingleton` / 引理 `ediam_eq_zero_of_subsingleton`

English:
lemma ediam_eq_zero_of_subsingleton
  given: [Subsingleton α]
  statement: G.ediam = 0
  proof: by
  simp [ediam_def]

中文:
引理 ediam_eq_zero_of_subsingleton
  条件: [Subsingleton α]
  结论: G.ediam = 0
  证明: by
  simp [ediam_def]

Depends on / 依赖: ediam_def
-/
lemma ediam_eq_zero_of_subsingleton [Subsingleton α] : G.ediam = 0 := by
  simp [ediam_def]

/--
lemma `nontrivial_of_ediam_ne_zero` / 引理 `nontrivial_of_ediam_ne_zero`

English:
lemma nontrivial_of_ediam_ne_zero
  given: (h : G.ediam != 0)
  statement: Nontrivial α
  proof: by
  contrapose! h
  exact ediam_eq_zero_of_subsingleton

中文:
引理 nontrivial_of_ediam_ne_zero
  条件: (h : G.ediam != 0)
  结论: Nontrivial α
  证明: by
  contrapose! h
  exact ediam_eq_zero_of_subsingleton

Depends on / 依赖: contrapose, ediam_eq_zero_of_subsingleton
-/
lemma nontrivial_of_ediam_ne_zero (h : G.ediam != 0) : Nontrivial α := by
  contrapose! h
  exact ediam_eq_zero_of_subsingleton

/--
lemma `ediam_ne_zero` / 引理 `ediam_ne_zero`

English:
lemma ediam_ne_zero
  given: [Nontrivial α]
  statement: G.ediam != 0
  proof: by
  obtain ⟨u, v, huv⟩ := exists_pair_ne ‹_›
  contrapose huv
  simp only [ediam, eccent, ENat.iSup_eq_zero, edist_eq_zero_iff] at huv
  exact huv u v

中文:
引理 ediam_ne_zero
  条件: [Nontrivial α]
  结论: G.ediam != 0
  证明: by
  obtain ⟨u, v, huv⟩ := exists_pair_ne ‹_›
  contrapose huv
  simp only [ediam, eccent, ENat.iSup_eq_zero, edist_eq_zero_iff] at huv
  exact huv u v

Depends on / 依赖: ENat.iSup_eq_zero, contrapose, eccent, edist_eq_zero_iff, exists_pair_ne, iSup_eq_zero
-/
lemma ediam_ne_zero [Nontrivial α] : G.ediam != 0 := by
  obtain ⟨u, v, huv⟩ := exists_pair_ne ‹_›
  contrapose huv
  simp only [ediam, eccent, ENat.iSup_eq_zero, edist_eq_zero_iff] at huv
  exact huv u v

/--
lemma `subsingleton_of_ediam_eq_zero` / 引理 `subsingleton_of_ediam_eq_zero`

English:
lemma subsingleton_of_ediam_eq_zero
  given: (h : G.ediam = 0)
  statement: Subsingleton α
  proof: by
  contrapose! h
  exact ediam_ne_zero

中文:
引理 subsingleton_of_ediam_eq_zero
  条件: (h : G.ediam = 0)
  结论: Subsingleton α
  证明: by
  contrapose! h
  exact ediam_ne_zero

Depends on / 依赖: contrapose, ediam_ne_zero
-/
lemma subsingleton_of_ediam_eq_zero (h : G.ediam = 0) : Subsingleton α := by
  contrapose! h
  exact ediam_ne_zero

/--
lemma `ediam_ne_zero_iff_nontrivial` / 引理 `ediam_ne_zero_iff_nontrivial`

English:
lemma ediam_ne_zero_iff_nontrivial
  proof: ⟨nontrivial_of_ediam_ne_zero, fun _ => ediam_ne_zero⟩

@[simp]

中文:
引理 ediam_ne_zero_iff_nontrivial
  证明: ⟨nontrivial_of_ediam_ne_zero, fun _ => ediam_ne_zero⟩

@[simp]

Depends on / 依赖: ediam_ne_zero, nontrivial_of_ediam_ne_zero
-/
lemma ediam_ne_zero_iff_nontrivial :
    G.ediam != 0 ↔ Nontrivial α :=
  ⟨nontrivial_of_ediam_ne_zero, fun _ => ediam_ne_zero⟩

@[simp]
/--
lemma `ediam_eq_zero_iff_subsingleton` / 引理 `ediam_eq_zero_iff_subsingleton`

English:
lemma ediam_eq_zero_iff_subsingleton
  proof: ⟨subsingleton_of_ediam_eq_zero, fun _ => ediam_eq_zero_of_subsingleton⟩

中文:
引理 ediam_eq_zero_iff_subsingleton
  证明: ⟨subsingleton_of_ediam_eq_zero, fun _ => ediam_eq_zero_of_subsingleton⟩

Depends on / 依赖: ediam_eq_zero_of_subsingleton, subsingleton_of_ediam_eq_zero
-/
lemma ediam_eq_zero_iff_subsingleton :
    G.ediam = 0 ↔ Subsingleton α :=
  ⟨subsingleton_of_ediam_eq_zero, fun _ => ediam_eq_zero_of_subsingleton⟩

/--
lemma `ediam_eq_top_of_not_connected` / 引理 `ediam_eq_top_of_not_connected`

English:
lemma ediam_eq_top_of_not_connected
  given: [Nonempty α] (h : ¬ G.Connected)
  statement: G.ediam = ⊤
  proof: by
  rw [connected_iff_exists_forall_reachable] at h
  push Not at h
  obtain ⟨_, hw⟩ := h Classical.ofNonempty
  rw [eq_top_iff]; rw [← edist_eq_top_of_not_reachable hw]
  exact edist_le_ediam

中文:
引理 ediam_eq_top_of_not_connected
  条件: [Nonempty α] (h : ¬ G.Connected)
  结论: G.ediam = ⊤
  证明: by
  rw [connected_iff_exists_forall_reachable] at h
  push Not at h
  obtain ⟨_, hw⟩ := h Classical.ofNonempty
  rw [eq_top_iff]; rw [← edist_eq_top_of_not_reachable hw]
  exact edist_le_ediam

Depends on / 依赖: Classical, Classical.ofNonempty, connected_iff_exists_forall_reachable, edist_eq_top_of_not_reachable, edist_le_ediam, eq_top_iff, ofNonempty
-/
lemma ediam_eq_top_of_not_connected [Nonempty α] (h : ¬ G.Connected) : G.ediam = ⊤ := by
  rw [connected_iff_exists_forall_reachable] at h
  push Not at h
  obtain ⟨_, hw⟩ := h Classical.ofNonempty
  rw [eq_top_iff]; rw [← edist_eq_top_of_not_reachable hw]
  exact edist_le_ediam

/--
lemma `ediam_eq_top_of_not_preconnected` / 引理 `ediam_eq_top_of_not_preconnected`

English:
lemma ediam_eq_top_of_not_preconnected
  given: (h : ¬ G.Preconnected)
  statement: G.ediam = ⊤
  proof: by
  cases isEmpty_or_nonempty α
  · exfalso
exact h IsEmpty.forall_iff.mpr trivial
  · apply ediam_eq_top_of_not_connected
    rw [connected_iff]
    tauto

中文:
引理 ediam_eq_top_of_not_preconnected
  条件: (h : ¬ G.Preconnected)
  结论: G.ediam = ⊤
  证明: by
  cases isEmpty_or_nonempty α
  · exfalso
exact h IsEmpty.forall_iff.mpr trivial
  · apply ediam_eq_top_of_not_connected
    rw [connected_iff]
    tauto

Depends on / 依赖: IsEmpty, IsEmpty.forall_iff.mpr, connected_iff, ediam_eq_top_of_not_connected, forall_iff, isEmpty_or_nonempty
-/
lemma ediam_eq_top_of_not_preconnected (h : ¬ G.Preconnected) : G.ediam = ⊤ := by
  cases isEmpty_or_nonempty α
  · exfalso
exact h IsEmpty.forall_iff.mpr trivial
  · apply ediam_eq_top_of_not_connected
    rw [connected_iff]
    tauto

/--
lemma `preconnected_of_ediam_ne_top` / 引理 `preconnected_of_ediam_ne_top`

English:
lemma preconnected_of_ediam_ne_top
  given: (h : G.ediam != ⊤)
  statement: G.Preconnected
  proof: Not.imp_symm G.ediam_eq_top_of_not_preconnected h

中文:
引理 preconnected_of_ediam_ne_top
  条件: (h : G.ediam != ⊤)
  结论: G.Preconnected
  证明: Not.imp_symm G.ediam_eq_top_of_not_preconnected h

Depends on / 依赖: G.ediam_eq_top_of_not_preconnected, Not.imp_symm, ediam_eq_top_of_not_preconnected, imp_symm
-/
lemma preconnected_of_ediam_ne_top (h : G.ediam != ⊤) : G.Preconnected :=
  Not.imp_symm G.ediam_eq_top_of_not_preconnected h

/--
lemma `connected_of_ediam_ne_top` / 引理 `connected_of_ediam_ne_top`

English:
lemma connected_of_ediam_ne_top
  given: [Nonempty α] (h : G.ediam != ⊤)
  statement: G.Connected
  proof: G.connected_iff.mpr ⟨preconnected_of_ediam_ne_top h, ‹_›⟩

中文:
引理 connected_of_ediam_ne_top
  条件: [Nonempty α] (h : G.ediam != ⊤)
  结论: G.Connected
  证明: G.connected_iff.mpr ⟨preconnected_of_ediam_ne_top h, ‹_›⟩

Depends on / 依赖: G.connected_iff.mpr, connected_iff, preconnected_of_ediam_ne_top
-/
lemma connected_of_ediam_ne_top [Nonempty α] (h : G.ediam != ⊤) : G.Connected :=
  G.connected_iff.mpr ⟨preconnected_of_ediam_ne_top h, ‹_›⟩

/--
lemma `exists_eccent_eq_ediam_of_ne_top` / 引理 `exists_eccent_eq_ediam_of_ne_top`

English:
lemma exists_eccent_eq_ediam_of_ne_top
  given: [Nonempty α] (h : G.ediam != ⊤)
  proof: ENat.exists_eq_iSup_of_lt_top h.lt_top

中文:
引理 exists_eccent_eq_ediam_of_ne_top
  条件: [Nonempty α] (h : G.ediam != ⊤)
  证明: ENat.exists_eq_iSup_of_lt_top h.lt_top

Depends on / 依赖: ENat.exists_eq_iSup_of_lt_top, exists_eq_iSup_of_lt_top, h.lt_top, lt_top
-/
lemma exists_eccent_eq_ediam_of_ne_top [Nonempty α] (h : G.ediam != ⊤) :
    exists u, G.eccent u = G.ediam :=
  ENat.exists_eq_iSup_of_lt_top h.lt_top

-- Note: Neither `Finite α` nor `G.ediam ≠ ⊤` implies the other.
/--
lemma `exists_eccent_eq_ediam_of_finite` / 引理 `exists_eccent_eq_ediam_of_finite`

English:
lemma exists_eccent_eq_ediam_of_finite
  given: [Nonempty α] [Finite α]
  proof: exists_eq_ciSup_of_finite

中文:
引理 exists_eccent_eq_ediam_of_finite
  条件: [Nonempty α] [Finite α]
  证明: exists_eq_ciSup_of_finite

Depends on / 依赖: exists_eq_ciSup_of_finite
-/
lemma exists_eccent_eq_ediam_of_finite [Nonempty α] [Finite α] :
    exists u, G.eccent u = G.ediam :=
  exists_eq_ciSup_of_finite

/--
lemma `exists_edist_eq_ediam_of_ne_top` / 引理 `exists_edist_eq_ediam_of_ne_top`

English:
lemma exists_edist_eq_ediam_of_ne_top
  given: [Nonempty α] (h : G.ediam != ⊤)
  proof: ENat.exists_eq_iSup₂_of_lt_top h.lt_top

中文:
引理 exists_edist_eq_ediam_of_ne_top
  条件: [Nonempty α] (h : G.ediam != ⊤)
  证明: ENat.exists_eq_iSup₂_of_lt_top h.lt_top

Depends on / 依赖: ENat.exists_eq_iSup, h.lt_top, lt_top
-/
lemma exists_edist_eq_ediam_of_ne_top [Nonempty α] (h : G.ediam != ⊤) :
    exists u v, G.edist u v = G.ediam :=
  ENat.exists_eq_iSup₂_of_lt_top h.lt_top

-- Note: Neither `Finite α` nor `G.ediam ≠ ⊤` implies the other.
/--
lemma `exists_edist_eq_ediam_of_finite` / 引理 `exists_edist_eq_ediam_of_finite`

English:
lemma exists_edist_eq_ediam_of_finite
  given: [Nonempty α] [Finite α]
  proof: Prod.exists'.mp ediam_def ▸ exists_eq_ciSup_of_finite

中文:
引理 exists_edist_eq_ediam_of_finite
  条件: [Nonempty α] [Finite α]
  证明: Prod.exists'.mp ediam_def ▸ exists_eq_ciSup_of_finite

Depends on / 依赖: Prod.exists, ediam_def, exists_eq_ciSup_of_finite
-/
lemma exists_edist_eq_ediam_of_finite [Nonempty α] [Finite α] :
    exists u v, G.edist u v = G.ediam :=
Prod.exists'.mp ediam_def ▸ exists_eq_ciSup_of_finite

/--
lemma `connected_iff_ediam_ne_top` / 引理 `connected_iff_ediam_ne_top`

English:
lemma connected_iff_ediam_ne_top
  given: [Nonempty α] [Finite α]
  statement: G.Connected ↔ G.ediam != ⊤
  proof: have ⟨u, v, huv⟩ := G.exists_edist_eq_ediam_of_finite
  ⟨fun h => huv ▸ edist_ne_top_iff_reachable.mpr (h u v),
   fun h => G.connected_of_ediam_ne_top h⟩

@[gcongr]

中文:
引理 connected_iff_ediam_ne_top
  条件: [Nonempty α] [Finite α]
  结论: G.Connected ↔ G.ediam != ⊤
  证明: have ⟨u, v, huv⟩ := G.exists_edist_eq_ediam_of_finite
  ⟨fun h => huv ▸ edist_ne_top_iff_reachable.mpr (h u v),
   fun h => G.connected_of_ediam_ne_top h⟩

@[gcongr]

Depends on / 依赖: G.connected_of_ediam_ne_top, G.exists_edist_eq_ediam_of_finite, connected_of_ediam_ne_top, edist_ne_top_iff_reachable, edist_ne_top_iff_reachable.mpr, exists_edist_eq_ediam_of_finite
-/
lemma connected_iff_ediam_ne_top [Nonempty α] [Finite α] : G.Connected ↔ G.ediam != ⊤ :=
  have ⟨u, v, huv⟩ := G.exists_edist_eq_ediam_of_finite
  ⟨fun h => huv ▸ edist_ne_top_iff_reachable.mpr (h u v),
   fun h => G.connected_of_ediam_ne_top h⟩

@[gcongr]
/--
lemma `ediam_anti` / 引理 `ediam_anti`

English:
lemma ediam_anti
  given: (h : G <= G')
  statement: G'.ediam <= G.ediam
  proof: iSup₂_mono fun _ _ => edist_anti h

@[simp]

中文:
引理 ediam_anti
  条件: (h : G <= G')
  结论: G'.ediam <= G.ediam
  证明: iSup₂_mono fun _ _ => edist_anti h

@[simp]

Depends on / 依赖: edist_anti
-/
lemma ediam_anti (h : G <= G') : G'.ediam <= G.ediam :=
  iSup₂_mono fun _ _ => edist_anti h

@[simp]
/--
lemma `ediam_bot` / 引理 `ediam_bot`

English:
lemma ediam_bot
  given: [Nontrivial α]
  statement: (⊥ : SimpleGraph α).ediam = ⊤
  proof: ediam_eq_top_of_not_connected not_connected_bot

@[simp]

中文:
引理 ediam_bot
  条件: [Nontrivial α]
  结论: (⊥ : SimpleGraph α).ediam = ⊤
  证明: ediam_eq_top_of_not_connected not_connected_bot

@[simp]

Depends on / 依赖: ediam_eq_top_of_not_connected, not_connected_bot
-/
lemma ediam_bot [Nontrivial α] : (⊥ : SimpleGraph α).ediam = ⊤ :=
  ediam_eq_top_of_not_connected not_connected_bot

@[simp]
/--
lemma `ediam_top` / 引理 `ediam_top`

English:
lemma ediam_top
  given: [Nontrivial α]
  statement: (⊤ : SimpleGraph α).ediam = 1
  proof: by
  simp [ediam]

@[simp]

中文:
引理 ediam_top
  条件: [Nontrivial α]
  结论: (⊤ : SimpleGraph α).ediam = 1
  证明: by
  simp [ediam]

@[simp]
-/
lemma ediam_top [Nontrivial α] : (⊤ : SimpleGraph α).ediam = 1 := by
  simp [ediam]

@[simp]
/--
lemma `ediam_eq_one` / 引理 `ediam_eq_one`

English:
lemma ediam_eq_one
  given: [Nontrivial α]
  statement: G.ediam = 1 ↔ G = ⊤
  proof: by
  refine ⟨fun h => ?_, fun h => h ▸ ediam_top⟩
  rw [eq_top_iff_forall_eccent_eq_one]
  intro u
  apply le_antisymm (h ▸ eccent_le_ediam)
  rw [Order.one_le_iff_pos]; rw [pos_iff_ne_zero]
  exact eccent_ne_zero u

中文:
引理 ediam_eq_one
  条件: [Nontrivial α]
  结论: G.ediam = 1 ↔ G = ⊤
  证明: by
  refine ⟨fun h => ?_, fun h => h ▸ ediam_top⟩
  rw [eq_top_iff_forall_eccent_eq_one]
  intro u
  apply le_antisymm (h ▸ eccent_le_ediam)
  rw [Order.one_le_iff_pos]; rw [pos_iff_ne_zero]
  exact eccent_ne_zero u

Depends on / 依赖: Order.one_le_iff_pos, eccent_le_ediam, eccent_ne_zero, ediam_top, eq_top_iff_forall_eccent_eq_one, le_antisymm, one_le_iff_pos, pos_iff_ne_zero
-/
lemma ediam_eq_one [Nontrivial α] : G.ediam = 1 ↔ G = ⊤ := by
  refine ⟨fun h => ?_, fun h => h ▸ ediam_top⟩
  rw [eq_top_iff_forall_eccent_eq_one]
  intro u
  apply le_antisymm (h ▸ eccent_le_ediam)
  rw [Order.one_le_iff_pos]; rw [pos_iff_ne_zero]
  exact eccent_ne_zero u

/--
lemma `ediam_le_two_mul_eccent` / 引理 `ediam_le_two_mul_eccent`

English:
lemma ediam_le_two_mul_eccent
  given: (u : α)
  statement: G.ediam <= 2 * G.eccent u
  proof: by
  refine ediam_le_of_edist_le fun v w => ?_
  calc
    G.edist v w
      <= G.edist v u + G.edist u w := G.edist_triangle
    _ = G.edist u v + G.edist u w := by rw [edist_comm]
    _ <= G.eccent u + G.eccent u := add_le_add edist_le_eccent edist_le_eccent
    _ = 2 * G.eccent u := (two_mul _).sy

中文:
引理 ediam_le_two_mul_eccent
  条件: (u : α)
  结论: G.ediam <= 2 * G.eccent u
  证明: by
  refine ediam_le_of_edist_le fun v w => ?_
  calc
    G.edist v w
      <= G.edist v u + G.edist u w := G.edist_triangle
    _ = G.edist u v + G.edist u w := by rw [edist_comm]
    _ <= G.eccent u + G.eccent u := add_le_add edist_le_eccent edist_le_eccent
    _ = 2 * G.eccent u := (two_mul _).sy

Depends on / 依赖: G.eccent, G.edist, G.edist_triangle, add_le_add, eccent, ediam_le_of_edist_le, edist_comm, edist_le_eccent, edist_triangle, two_mul
-/
lemma ediam_le_two_mul_eccent (u : α) : G.ediam <= 2 * G.eccent u := by
  refine ediam_le_of_edist_le fun v w => ?_
  calc
    G.edist v w
      <= G.edist v u + G.edist u w := G.edist_triangle
    _ = G.edist u v + G.edist u w := by rw [edist_comm]
    _ <= G.eccent u + G.eccent u := add_le_add edist_le_eccent edist_le_eccent
    _ = 2 * G.eccent u := (two_mul _).symm

end ediam

section diam

/--
Definition of `diam` / `diam` 的定义

English:
definition diam
  signature: (G : SimpleGraph α)
  body: G.ediam.toNat

中文:
定义 diam
  签名: (G : SimpleGraph α)
  定义体: G.ediam.toNat

Depends on / 依赖: G.ediam.toNat
-/
noncomputable def diam (G : SimpleGraph α) :=
  G.ediam.toNat

/--
lemma `diam_def` / 引理 `diam_def`

English:
lemma diam_def
  statement: G.diam = (⨆ p : α × α, G.edist p.1 p.2).toNat
  proof: by
  rw [diam]; rw [ediam_def]

中文:
引理 diam_def
  结论: G.diam = (⨆ p : α × α, G.edist p.1 p.2).to自然数
  证明: by
  rw [diam]; rw [ediam_def]

Depends on / 依赖: ediam_def
-/
lemma diam_def : G.diam = (⨆ p : α × α, G.edist p.1 p.2).toNat := by
  rw [diam]; rw [ediam_def]

/--
lemma `dist_le_diam` / 引理 `dist_le_diam`

English:
lemma dist_le_diam
  given: (h : G.ediam != ⊤) {u v : α}
  statement: G.dist u v <= G.diam
  proof: ENat.toNat_le_toNat edist_le_ediam h

中文:
引理 dist_le_diam
  条件: (h : G.ediam != ⊤) {u v : α}
  结论: G.dist u v <= G.diam
  证明: ENat.toNat_le_toNat edist_le_ediam h

Depends on / 依赖: ENat.toNat_le_toNat, edist_le_ediam, toNat_le_toNat
-/
lemma dist_le_diam (h : G.ediam != ⊤) {u v : α} : G.dist u v <= G.diam :=
  ENat.toNat_le_toNat edist_le_ediam h

/--
lemma `nontrivial_of_diam_ne_zero` / 引理 `nontrivial_of_diam_ne_zero`

English:
lemma nontrivial_of_diam_ne_zero
  given: (h : G.diam != 0)
  statement: Nontrivial α
  proof: by
  contrapose! h
  simp [diam, h]

中文:
引理 nontrivial_of_diam_ne_zero
  条件: (h : G.diam != 0)
  结论: Nontrivial α
  证明: by
  contrapose! h
  simp [diam, h]

Depends on / 依赖: contrapose
-/
lemma nontrivial_of_diam_ne_zero (h : G.diam != 0) : Nontrivial α := by
  contrapose! h
  simp [diam, h]

/--
lemma `diam_eq_zero_of_not_connected` / 引理 `diam_eq_zero_of_not_connected`

English:
lemma diam_eq_zero_of_not_connected
  given: (h : ¬ G.Connected)
  statement: G.diam = 0
  proof: by
  cases isEmpty_or_nonempty α
  · rw [diam, ediam, ciSup_of_empty, bot_eq_zero']; rfl
  · rw [diam, ediam_eq_top_of_not_connected h, ENat.toNat_top]

中文:
引理 diam_eq_zero_of_not_connected
  条件: (h : ¬ G.Connected)
  结论: G.diam = 0
  证明: by
  cases isEmpty_or_nonempty α
  · rw [diam, ediam, ciSup_of_empty, bot_eq_zero']; rfl
  · rw [diam, ediam_eq_top_of_not_connected h, ENat.toNat_top]

Depends on / 依赖: ENat.toNat_top, bot_eq_zero, ciSup_of_empty, ediam_eq_top_of_not_connected, isEmpty_or_nonempty, toNat_top
-/
lemma diam_eq_zero_of_not_connected (h : ¬ G.Connected) : G.diam = 0 := by
  cases isEmpty_or_nonempty α
  · rw [diam, ediam, ciSup_of_empty, bot_eq_zero']; rfl
  · rw [diam, ediam_eq_top_of_not_connected h, ENat.toNat_top]

/--
lemma `diam_eq_zero_of_ediam_eq_top` / 引理 `diam_eq_zero_of_ediam_eq_top`

English:
lemma diam_eq_zero_of_ediam_eq_top
  given: (h : G.ediam = ⊤)
  statement: G.diam = 0
  proof: by
  rw [diam]; rw [h]; rw [ENat.toNat_top]

中文:
引理 diam_eq_zero_of_ediam_eq_top
  条件: (h : G.ediam = ⊤)
  结论: G.diam = 0
  证明: by
  rw [diam]; rw [h]; rw [ENat.toNat_top]

Depends on / 依赖: ENat.toNat_top, toNat_top
-/
lemma diam_eq_zero_of_ediam_eq_top (h : G.ediam = ⊤) : G.diam = 0 := by
  rw [diam]; rw [h]; rw [ENat.toNat_top]

/--
lemma `ediam_ne_top_of_diam_ne_zero` / 引理 `ediam_ne_top_of_diam_ne_zero`

English:
lemma ediam_ne_top_of_diam_ne_zero
  given: (h : G.diam != 0)
  statement: G.ediam != ⊤
  proof: mt diam_eq_zero_of_ediam_eq_top h

中文:
引理 ediam_ne_top_of_diam_ne_zero
  条件: (h : G.diam != 0)
  结论: G.ediam != ⊤
  证明: mt diam_eq_zero_of_ediam_eq_top h

Depends on / 依赖: diam_eq_zero_of_ediam_eq_top
-/
lemma ediam_ne_top_of_diam_ne_zero (h : G.diam != 0) : G.ediam != ⊤ :=
  mt diam_eq_zero_of_ediam_eq_top h

/--
lemma `exists_dist_eq_diam` / 引理 `exists_dist_eq_diam`

English:
lemma exists_dist_eq_diam
  given: [Nonempty α]
  proof: by
  by_cases h : G.diam = 0
  · simp [h]
· obtain ⟨u, v, huv⟩ := exists_edist_eq_ediam_of_ne_top ediam_ne_top_of_diam_ne_zero h
    use u, v
    rw [diam]; rw [dist]; rw [congrArg ENat.toNat huv]

中文:
引理 exists_dist_eq_diam
  条件: [Nonempty α]
  证明: by
  by_cases h : G.diam = 0
  · simp [h]
· obtain ⟨u, v, huv⟩ := exists_edist_eq_ediam_of_ne_top ediam_ne_top_of_diam_ne_zero h
    use u, v
    rw [diam]; rw [dist]; rw [congrArg ENat.toNat huv]

Depends on / 依赖: ENat.toNat, G.diam, ediam_ne_top_of_diam_ne_zero, exists_edist_eq_ediam_of_ne_top
-/
lemma exists_dist_eq_diam [Nonempty α] :
    exists u v, G.dist u v = G.diam := by
  by_cases h : G.diam = 0
  · simp [h]
· obtain ⟨u, v, huv⟩ := exists_edist_eq_ediam_of_ne_top ediam_ne_top_of_diam_ne_zero h
    use u, v
    rw [diam]; rw [dist]; rw [congrArg ENat.toNat huv]

/--
lemma `diam_ne_zero_of_ediam_ne_top` / 引理 `diam_ne_zero_of_ediam_ne_top`

English:
lemma diam_ne_zero_of_ediam_ne_top
  given: [Nontrivial α] (h : G.ediam != ⊤)
  statement: G.diam != 0
  proof: have ⟨_, _, hne⟩ := exists_pair_ne ‹_›
pos_iff_ne_zero.mp
lt_of_lt_of_le ((connected_of_ediam_ne_top h).pos_dist_of_ne hne) dist_le_diam h

@[gcongr]

中文:
引理 diam_ne_zero_of_ediam_ne_top
  条件: [Nontrivial α] (h : G.ediam != ⊤)
  结论: G.diam != 0
  证明: have ⟨_, _, hne⟩ := exists_pair_ne ‹_›
pos_iff_ne_zero.mp
lt_of_lt_of_le ((connected_of_ediam_ne_top h).pos_dist_of_ne hne) dist_le_diam h

@[gcongr]

Depends on / 依赖: connected_of_ediam_ne_top, dist_le_diam, exists_pair_ne, lt_of_lt_of_le, pos_dist_of_ne, pos_iff_ne_zero, pos_iff_ne_zero.mp
-/
lemma diam_ne_zero_of_ediam_ne_top [Nontrivial α] (h : G.ediam != ⊤) : G.diam != 0 :=
  have ⟨_, _, hne⟩ := exists_pair_ne ‹_›
pos_iff_ne_zero.mp
lt_of_lt_of_le ((connected_of_ediam_ne_top h).pos_dist_of_ne hne) dist_le_diam h

@[gcongr]
/--
lemma `diam_anti_of_ediam_ne_top` / 引理 `diam_anti_of_ediam_ne_top`

English:
lemma diam_anti_of_ediam_ne_top
  given: (h : G <= G') (hn : G.ediam != ⊤)
  statement: G'.diam <= G.diam
  proof: ENat.toNat_le_toNat (ediam_anti h) hn

@[simp]

中文:
引理 diam_anti_of_ediam_ne_top
  条件: (h : G <= G') (hn : G.ediam != ⊤)
  结论: G'.diam <= G.diam
  证明: ENat.toNat_le_toNat (ediam_anti h) hn

@[simp]

Depends on / 依赖: ENat.toNat_le_toNat, ediam_anti, toNat_le_toNat
-/
lemma diam_anti_of_ediam_ne_top (h : G <= G') (hn : G.ediam != ⊤) : G'.diam <= G.diam :=
  ENat.toNat_le_toNat (ediam_anti h) hn

@[simp]
/--
lemma `diam_bot` / 引理 `diam_bot`

English:
lemma diam_bot
  statement: (⊥ : SimpleGraph α).diam = 0
  proof: by
  rw [diam]; rw [ENat.toNat_eq_zero]
  cases subsingleton_or_nontrivial α
  · exact Or.inl ediam_eq_zero_of_subsingleton
  · exact Or.inr ediam_bot

@[simp]

中文:
引理 diam_bot
  结论: (⊥ : SimpleGraph α).diam = 0
  证明: by
  rw [diam]; rw [ENat.toNat_eq_zero]
  cases subsingleton_or_nontrivial α
  · exact Or.inl ediam_eq_zero_of_subsingleton
  · exact Or.inr ediam_bot

@[simp]

Depends on / 依赖: ENat.toNat_eq_zero, Or.inl, Or.inr, ediam_bot, ediam_eq_zero_of_subsingleton, subsingleton_or_nontrivial, toNat_eq_zero
-/
lemma diam_bot : (⊥ : SimpleGraph α).diam = 0 := by
  rw [diam]; rw [ENat.toNat_eq_zero]
  cases subsingleton_or_nontrivial α
  · exact Or.inl ediam_eq_zero_of_subsingleton
  · exact Or.inr ediam_bot

@[simp]
/--
lemma `diam_top` / 引理 `diam_top`

English:
lemma diam_top
  given: [Nontrivial α]
  statement: (⊤ : SimpleGraph α).diam = 1
  proof: by
  rw [diam]; rw [ediam_top]; rw [ENat.toNat_one]

@[simp]

中文:
引理 diam_top
  条件: [Nontrivial α]
  结论: (⊤ : SimpleGraph α).diam = 1
  证明: by
  rw [diam]; rw [ediam_top]; rw [ENat.toNat_one]

@[simp]

Depends on / 依赖: ENat.toNat_one, ediam_top, toNat_one
-/
lemma diam_top [Nontrivial α] : (⊤ : SimpleGraph α).diam = 1 := by
  rw [diam]; rw [ediam_top]; rw [ENat.toNat_one]

@[simp]
/--
lemma `diam_eq_zero` / 引理 `diam_eq_zero`

English:
lemma diam_eq_zero
  statement: G.diam = 0 ↔ G.ediam = ⊤ ∨ Subsingleton α
  proof: by
  rw [diam]; rw [ENat.toNat_eq_zero]; rw [or_comm]; rw [ediam_eq_zero_iff_subsingleton]

@[simp]

中文:
引理 diam_eq_zero
  结论: G.diam = 0 ↔ G.ediam = ⊤ ∨ Subsingleton α
  证明: by
  rw [diam]; rw [ENat.toNat_eq_zero]; rw [or_comm]; rw [ediam_eq_zero_iff_subsingleton]

@[simp]

Depends on / 依赖: ENat.toNat_eq_zero, ediam_eq_zero_iff_subsingleton, or_comm, toNat_eq_zero
-/
lemma diam_eq_zero : G.diam = 0 ↔ G.ediam = ⊤ ∨ Subsingleton α := by
  rw [diam]; rw [ENat.toNat_eq_zero]; rw [or_comm]; rw [ediam_eq_zero_iff_subsingleton]

@[simp]
/--
lemma `diam_eq_one` / 引理 `diam_eq_one`

English:
lemma diam_eq_one
  given: [Nontrivial α]
  statement: G.diam = 1 ↔ G = ⊤
  proof: by
  rw [diam]; rw [ENat.toNat_eq_iff one_ne_zero]; rw [Nat.cast_one]; rw [ediam_eq_one]

中文:
引理 diam_eq_one
  条件: [Nontrivial α]
  结论: G.diam = 1 ↔ G = ⊤
  证明: by
  rw [diam]; rw [ENat.toNat_eq_iff one_ne_zero]; rw [Nat.cast_one]; rw [ediam_eq_one]

Depends on / 依赖: ENat.toNat_eq_iff, Nat.cast_one, cast_one, ediam_eq_one, one_ne_zero, toNat_eq_iff
-/
lemma diam_eq_one [Nontrivial α] : G.diam = 1 ↔ G = ⊤ := by
  rw [diam]; rw [ENat.toNat_eq_iff one_ne_zero]; rw [Nat.cast_one]; rw [ediam_eq_one]

/--
lemma `diam_eq_zero_iff_ediam_eq_top` / 引理 `diam_eq_zero_iff_ediam_eq_top`

English:
lemma diam_eq_zero_iff_ediam_eq_top
  given: [Nontrivial α]
  statement: G.diam = 0 ↔ G.ediam = ⊤
  proof: by
  rw [← not_iff_not]
  exact ⟨ediam_ne_top_of_diam_ne_zero, diam_ne_zero_of_ediam_ne_top⟩

中文:
引理 diam_eq_zero_iff_ediam_eq_top
  条件: [Nontrivial α]
  结论: G.diam = 0 ↔ G.ediam = ⊤
  证明: by
  rw [← not_iff_not]
  exact ⟨ediam_ne_top_of_diam_ne_zero, diam_ne_zero_of_ediam_ne_top⟩

Depends on / 依赖: diam_ne_zero_of_ediam_ne_top, ediam_ne_top_of_diam_ne_zero, not_iff_not
-/
lemma diam_eq_zero_iff_ediam_eq_top [Nontrivial α] : G.diam = 0 ↔ G.ediam = ⊤ := by
  rw [← not_iff_not]
  exact ⟨ediam_ne_top_of_diam_ne_zero, diam_ne_zero_of_ediam_ne_top⟩

/--
lemma `connected_iff_diam_ne_zero` / 引理 `connected_iff_diam_ne_zero`

English:
lemma connected_iff_diam_ne_zero
  given: [Finite α] [Nontrivial α]
  statement: G.Connected ↔ G.diam != 0
  proof: by
  rw [connected_iff_ediam_ne_top]; rw [not_iff_not]; rw [diam_eq_zero_iff_ediam_eq_top]

中文:
引理 connected_iff_diam_ne_zero
  条件: [Finite α] [Nontrivial α]
  结论: G.Connected ↔ G.diam != 0
  证明: by
  rw [connected_iff_ediam_ne_top]; rw [not_iff_not]; rw [diam_eq_zero_iff_ediam_eq_top]

Depends on / 依赖: connected_iff_ediam_ne_top, diam_eq_zero_iff_ediam_eq_top, not_iff_not
-/
lemma connected_iff_diam_ne_zero [Finite α] [Nontrivial α] : G.Connected ↔ G.diam != 0 := by
  rw [connected_iff_ediam_ne_top]; rw [not_iff_not]; rw [diam_eq_zero_iff_ediam_eq_top]

end diam

section radius

/--
Definition of `radius` / `radius` 的定义

English:
definition radius
  signature: (G : SimpleGraph α)
  body: ⨅ u, G.eccent u

中文:
定义 radius
  签名: (G : SimpleGraph α)
  定义体: ⨅ u, G.eccent u

Depends on / 依赖: G.eccent, eccent
-/
noncomputable def radius (G : SimpleGraph α) : Nat∞ :=
  ⨅ u, G.eccent u

/--
lemma `radius_eq_iInf_iSup_edist` / 引理 `radius_eq_iInf_iSup_edist`

English:
lemma radius_eq_iInf_iSup_edist
  statement: G.radius = ⨅ u, ⨆ v, G.edist u v
  proof: rfl

中文:
引理 radius_eq_iInf_iSup_edist
  结论: G.radius = ⨅ u, ⨆ v, G.edist u v
  证明: rfl
-/
lemma radius_eq_iInf_iSup_edist : G.radius = ⨅ u, ⨆ v, G.edist u v :=
  rfl

/--
lemma `radius_le_eccent` / 引理 `radius_le_eccent`

English:
lemma radius_le_eccent
  given: {u : α}
  statement: G.radius <= G.eccent u
  proof: iInf_le G.eccent u

中文:
引理 radius_le_eccent
  条件: {u : α}
  结论: G.radius <= G.eccent u
  证明: iInf_le G.eccent u

Depends on / 依赖: G.eccent, eccent, iInf_le
-/
lemma radius_le_eccent {u : α} : G.radius <= G.eccent u :=
  iInf_le G.eccent u

/--
lemma `exists_eccent_eq_radius` / 引理 `exists_eccent_eq_radius`

English:
lemma exists_eccent_eq_radius
  given: [Nonempty α]
  statement: exists u, G.eccent u = G.radius
  proof: ENat.exists_eq_iInf G.eccent

中文:
引理 exists_eccent_eq_radius
  条件: [Nonempty α]
  结论: 存在 u, G.eccent u = G.radius
  证明: ENat.exists_eq_iInf G.eccent

Depends on / 依赖: ENat.exists_eq_iInf, G.eccent, eccent, exists_eq_iInf
-/
lemma exists_eccent_eq_radius [Nonempty α] : exists u, G.eccent u = G.radius :=
  ENat.exists_eq_iInf G.eccent

/--
lemma `exists_edist_eq_radius_of_finite` / 引理 `exists_edist_eq_radius_of_finite`

English:
lemma exists_edist_eq_radius_of_finite
  given: [Nonempty α] [Finite α]
  proof: by
  obtain ⟨w, hw⟩ := G.exists_eccent_eq_radius
  obtain ⟨v, hv⟩ := G.exists_edist_eq_eccent_of_finite w
  use w, v
  rw [hv]; rw [hw]

中文:
引理 exists_edist_eq_radius_of_finite
  条件: [Nonempty α] [Finite α]
  证明: by
  obtain ⟨w, hw⟩ := G.exists_eccent_eq_radius
  obtain ⟨v, hv⟩ := G.exists_edist_eq_eccent_of_finite w
  use w, v
  rw [hv]; rw [hw]

Depends on / 依赖: G.exists_eccent_eq_radius, G.exists_edist_eq_eccent_of_finite, exists_eccent_eq_radius, exists_edist_eq_eccent_of_finite
-/
lemma exists_edist_eq_radius_of_finite [Nonempty α] [Finite α] :
    exists u v, G.edist u v = G.radius := by
  obtain ⟨w, hw⟩ := G.exists_eccent_eq_radius
  obtain ⟨v, hv⟩ := G.exists_edist_eq_eccent_of_finite w
  use w, v
  rw [hv]; rw [hw]

/--
lemma `radius_eq_top_of_not_connected` / 引理 `radius_eq_top_of_not_connected`

English:
lemma radius_eq_top_of_not_connected
  given: (h : ¬ G.Connected)
  statement: G.radius = ⊤
  proof: by
  simp [radius, eccent_eq_top_of_not_connected h]

中文:
引理 radius_eq_top_of_not_connected
  条件: (h : ¬ G.Connected)
  结论: G.radius = ⊤
  证明: by
  simp [radius, eccent_eq_top_of_not_connected h]

Depends on / 依赖: eccent_eq_top_of_not_connected, radius
-/
lemma radius_eq_top_of_not_connected (h : ¬ G.Connected) : G.radius = ⊤ := by
  simp [radius, eccent_eq_top_of_not_connected h]

/--
lemma `radius_eq_top_of_isEmpty` / 引理 `radius_eq_top_of_isEmpty`

English:
lemma radius_eq_top_of_isEmpty
  given: [IsEmpty α]
  statement: G.radius = ⊤
  proof: iInf_of_empty G.eccent

中文:
引理 radius_eq_top_of_isEmpty
  条件: [IsEmpty α]
  结论: G.radius = ⊤
  证明: iInf_of_empty G.eccent

Depends on / 依赖: G.eccent, eccent, iInf_of_empty
-/
lemma radius_eq_top_of_isEmpty [IsEmpty α] : G.radius = ⊤ :=
  iInf_of_empty G.eccent

/--
lemma `radius_ne_top_iff` / 引理 `radius_ne_top_iff`

English:
lemma radius_ne_top_iff
  given: [Nonempty α] [Finite α]
  statement: G.radius != ⊤ ↔ G.Connected
  proof: by
  refine ⟨Not.imp_symm radius_eq_top_of_not_connected, fun h => ?_⟩
  obtain ⟨u, v, huv⟩ := G.exists_edist_eq_radius_of_finite
  rw [← huv]; rw [edist_ne_top_iff_reachable]
  exact h u v

中文:
引理 radius_ne_top_iff
  条件: [Nonempty α] [Finite α]
  结论: G.radius != ⊤ ↔ G.Connected
  证明: by
  refine ⟨Not.imp_symm radius_eq_top_of_not_connected, fun h => ?_⟩
  obtain ⟨u, v, huv⟩ := G.exists_edist_eq_radius_of_finite
  rw [← huv]; rw [edist_ne_top_iff_reachable]
  exact h u v

Depends on / 依赖: G.exists_edist_eq_radius_of_finite, Not.imp_symm, edist_ne_top_iff_reachable, exists_edist_eq_radius_of_finite, imp_symm, radius_eq_top_of_not_connected
-/
lemma radius_ne_top_iff [Nonempty α] [Finite α] : G.radius != ⊤ ↔ G.Connected := by
  refine ⟨Not.imp_symm radius_eq_top_of_not_connected, fun h => ?_⟩
  obtain ⟨u, v, huv⟩ := G.exists_edist_eq_radius_of_finite
  rw [← huv]; rw [edist_ne_top_iff_reachable]
  exact h u v

/--
lemma `radius_ne_zero_of_nontrivial` / 引理 `radius_ne_zero_of_nontrivial`

English:
lemma radius_ne_zero_of_nontrivial
  given: [Nontrivial α]
  statement: G.radius != 0
  proof: by
  rw [← Order.one_le_iff_ne_zero]
  apply le_iInf
  simp [Order.one_le_iff_ne_zero, G.eccent_ne_zero]

中文:
引理 radius_ne_zero_of_nontrivial
  条件: [Nontrivial α]
  结论: G.radius != 0
  证明: by
  rw [← Order.one_le_iff_ne_zero]
  apply le_iInf
  simp [Order.one_le_iff_ne_zero, G.eccent_ne_zero]

Depends on / 依赖: G.eccent_ne_zero, Order.one_le_iff_ne_zero, eccent_ne_zero, le_iInf, one_le_iff_ne_zero
-/
lemma radius_ne_zero_of_nontrivial [Nontrivial α] : G.radius != 0 := by
  rw [← Order.one_le_iff_ne_zero]
  apply le_iInf
  simp [Order.one_le_iff_ne_zero, G.eccent_ne_zero]

/--
lemma `radius_eq_zero_iff` / 引理 `radius_eq_zero_iff`

English:
lemma radius_eq_zero_iff
  statement: G.radius = 0 ↔ Nonempty α ∧ Subsingleton α
  proof: by
  refine ⟨fun h => ⟨?_, ?_⟩, fun ⟨_, _⟩ => ?_⟩
  · contrapose! h
    simp [radius]
  · contrapose! h
    simp [radius_ne_zero_of_nontrivial]
  · rw [radius, ENat.iInf_eq_zero]
    use Classical.ofNonempty
    simpa [eccent] using Subsingleton.elim _

中文:
引理 radius_eq_zero_iff
  结论: G.radius = 0 ↔ Nonempty α ∧ Subsingleton α
  证明: by
  refine ⟨fun h => ⟨?_, ?_⟩, fun ⟨_, _⟩ => ?_⟩
  · contrapose! h
    simp [radius]
  · contrapose! h
    simp [radius_ne_zero_of_nontrivial]
  · rw [radius, ENat.iInf_eq_zero]
    use Classical.ofNonempty
    simpa [eccent] using Subsingleton.elim _

Depends on / 依赖: Classical, Classical.ofNonempty, ENat.iInf_eq_zero, Subsingleton, Subsingleton.elim, contrapose, eccent, iInf_eq_zero, ofNonempty, radius, radius_ne_zero_of_nontrivial
-/
lemma radius_eq_zero_iff : G.radius = 0 ↔ Nonempty α ∧ Subsingleton α := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun ⟨_, _⟩ => ?_⟩
  · contrapose! h
    simp [radius]
  · contrapose! h
    simp [radius_ne_zero_of_nontrivial]
  · rw [radius, ENat.iInf_eq_zero]
    use Classical.ofNonempty
    simpa [eccent] using Subsingleton.elim _

/--
lemma `radius_le_ediam` / 引理 `radius_le_ediam`

English:
lemma radius_le_ediam
  given: [Nonempty α]
  statement: G.radius <= G.ediam
  proof: iInf_le_iSup

中文:
引理 radius_le_ediam
  条件: [Nonempty α]
  结论: G.radius <= G.ediam
  证明: iInf_le_iSup

Depends on / 依赖: iInf_le_iSup
-/
lemma radius_le_ediam [Nonempty α] : G.radius <= G.ediam :=
  iInf_le_iSup

/--
lemma `ediam_eq_top_iff_radius_eq_top` / 引理 `ediam_eq_top_iff_radius_eq_top`

English:
lemma ediam_eq_top_iff_radius_eq_top
  given: [Nonempty α]
  statement: G.ediam = ⊤ ↔ G.radius = ⊤
  proof: by
  refine ⟨?_, fun hr => eq_top_iff.mpr (hr ▸ radius_le_ediam)⟩
  contrapose
  intro hr
  obtain ⟨w, hw⟩ := G.exists_eccent_eq_radius
  have hdiam : G.ediam <= 2 * G.eccent w := ediam_le_two_mul_eccent w
exact ne_top_of_lt lt_of_le_of_lt hdiam WithTop.mul_lt_top (ENat.natCast_lt_top 2)
    lt_top_

中文:
引理 ediam_eq_top_iff_radius_eq_top
  条件: [Nonempty α]
  结论: G.ediam = ⊤ ↔ G.radius = ⊤
  证明: by
  refine ⟨?_, fun hr => eq_top_iff.mpr (hr ▸ radius_le_ediam)⟩
  contrapose
  intro hr
  obtain ⟨w, hw⟩ := G.exists_eccent_eq_radius
  have hdiam : G.ediam <= 2 * G.eccent w := ediam_le_two_mul_eccent w
exact ne_top_of_lt lt_of_le_of_lt hdiam WithTop.mul_lt_top (ENat.natCast_lt_top 2)
    lt_top_

Depends on / 依赖: ENat.natCast_lt_top, G.eccent, G.ediam, G.exists_eccent_eq_radius, WithTop, WithTop.mul_lt_top, contrapose, eccent, ediam_le_two_mul_eccent, eq_top_iff, eq_top_iff.mpr, exists_eccent_eq_radius, lt_of_le_of_lt, lt_top_iff_ne_top, lt_top_iff_ne_top.mpr, mul_lt_top, natCast_lt_top, ne_top_of_lt, radius_le_ediam
-/
lemma ediam_eq_top_iff_radius_eq_top [Nonempty α] : G.ediam = ⊤ ↔ G.radius = ⊤ := by
  refine ⟨?_, fun hr => eq_top_iff.mpr (hr ▸ radius_le_ediam)⟩
  contrapose
  intro hr
  obtain ⟨w, hw⟩ := G.exists_eccent_eq_radius
  have hdiam : G.ediam <= 2 * G.eccent w := ediam_le_two_mul_eccent w
exact ne_top_of_lt lt_of_le_of_lt hdiam WithTop.mul_lt_top (ENat.natCast_lt_top 2)
    lt_top_iff_ne_top.mpr (hw ▸ hr)

/--
lemma `ediam_le_two_mul_radius` / 引理 `ediam_le_two_mul_radius`

English:
lemma ediam_le_two_mul_radius
  statement: G.ediam <= 2 * G.radius
  proof: by
  cases isEmpty_or_nonempty α
  · rw [radius_eq_top_of_isEmpty]
    exact le_top
  · by_cases hdiam : G.ediam = ⊤
    · simp [hdiam, ediam_eq_top_iff_radius_eq_top.mp hdiam]
    · obtain ⟨w, hw⟩ := G.exists_eccent_eq_radius
      obtain ⟨_, _, h⟩ := G.exists_edist_eq_ediam_of_ne_top hdiam
      a

中文:
引理 ediam_le_two_mul_radius
  结论: G.ediam <= 2 * G.radius
  证明: by
  cases isEmpty_or_nonempty α
  · rw [radius_eq_top_of_isEmpty]
    exact le_top
  · by_cases hdiam : G.ediam = ⊤
    · simp [hdiam, ediam_eq_top_iff_radius_eq_top.mp hdiam]
    · obtain ⟨w, hw⟩ := G.exists_eccent_eq_radius
      obtain ⟨_, _, h⟩ := G.exists_edist_eq_ediam_of_ne_top hdiam
      a

Depends on / 依赖: G.ediam, G.edist_comm, G.edist_le_eccent, G.edist_triangle, G.exists_eccent_eq_radius, G.exists_edist_eq_ediam_of_ne_top, add_le_add, ediam_eq_top_iff_radius_eq_top, ediam_eq_top_iff_radius_eq_top.mp, edist_comm, edist_le_eccent, edist_triangle, exists_eccent_eq_radius, exists_edist_eq_ediam_of_ne_top, isEmpty_or_nonempty, le_top, le_trans, radius_eq_top_of_isEmpty, two_mul
-/
lemma ediam_le_two_mul_radius : G.ediam <= 2 * G.radius := by
  cases isEmpty_or_nonempty α
  · rw [radius_eq_top_of_isEmpty]
    exact le_top
  · by_cases hdiam : G.ediam = ⊤
    · simp [hdiam, ediam_eq_top_iff_radius_eq_top.mp hdiam]
    · obtain ⟨w, hw⟩ := G.exists_eccent_eq_radius
      obtain ⟨_, _, h⟩ := G.exists_edist_eq_ediam_of_ne_top hdiam
      apply le_trans (h ▸ G.edist_triangle (v := w))
      rw [two_mul]
      exact hw ▸ add_le_add (G.edist_comm ▸ G.edist_le_eccent) G.edist_le_eccent

/--
lemma `radius_eq_ediam_iff` / 引理 `radius_eq_ediam_iff`

English:
lemma radius_eq_ediam_iff
  given: [Nonempty α]
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · use G.radius
    intro u
    exact le_antisymm (h ▸ eccent_le_ediam) radius_le_eccent
  · obtain ⟨e, h⟩ := h
    have ediam_eq : G.ediam = e :=
      le_antisymm (iSup_le fun u => (h u).le) ((h Classical.ofNonempty) ▸ eccent_le_ediam)
    rw [ediam_eq]
    

中文:
引理 radius_eq_ediam_iff
  条件: [Nonempty α]
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · use G.radius
    intro u
    exact le_antisymm (h ▸ eccent_le_ediam) radius_le_eccent
  · obtain ⟨e, h⟩ := h
    have ediam_eq : G.ediam = e :=
      le_antisymm (iSup_le fun u => (h u).le) ((h Classical.ofNonempty) ▸ eccent_le_ediam)
    rw [ediam_eq]
    

Depends on / 依赖: Classical, Classical.ofNonempty, G.ediam, G.radius, eccent_le_ediam, ediam_eq, iSup_le, le_antisymm, le_iInf, ofNonempty, radius, radius_le_eccent
-/
lemma radius_eq_ediam_iff [Nonempty α] :
    G.radius = G.ediam ↔ exists e, forall u, G.eccent u = e := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · use G.radius
    intro u
    exact le_antisymm (h ▸ eccent_le_ediam) radius_le_eccent
  · obtain ⟨e, h⟩ := h
    have ediam_eq : G.ediam = e :=
      le_antisymm (iSup_le fun u => (h u).le) ((h Classical.ofNonempty) ▸ eccent_le_ediam)
    rw [ediam_eq]
    exact le_antisymm ((h Classical.ofNonempty) ▸ radius_le_eccent) (le_iInf fun u => (h u).ge)

@[simp]
/--
lemma `radius_bot` / 引理 `radius_bot`

English:
lemma radius_bot
  given: [Nontrivial α]
  statement: (⊥ : SimpleGraph α).radius = ⊤
  proof: radius_eq_top_of_not_connected not_connected_bot

@[simp]

中文:
引理 radius_bot
  条件: [Nontrivial α]
  结论: (⊥ : SimpleGraph α).radius = ⊤
  证明: radius_eq_top_of_not_connected not_connected_bot

@[simp]

Depends on / 依赖: not_connected_bot, radius_eq_top_of_not_connected
-/
lemma radius_bot [Nontrivial α] : (⊥ : SimpleGraph α).radius = ⊤ :=
  radius_eq_top_of_not_connected not_connected_bot

@[simp]
/--
lemma `radius_top` / 引理 `radius_top`

English:
lemma radius_top
  given: [Nontrivial α]
  statement: (⊤ : SimpleGraph α).radius = 1
  proof: by
  simp [radius]

中文:
引理 radius_top
  条件: [Nontrivial α]
  结论: (⊤ : SimpleGraph α).radius = 1
  证明: by
  simp [radius]

Depends on / 依赖: radius
-/
lemma radius_top [Nontrivial α] : (⊤ : SimpleGraph α).radius = 1 := by
  simp [radius]

end radius

section center

/--
Definition of `center` / `center` 的定义

English:
definition center
  signature: (G : SimpleGraph α)
  body: {u | G.eccent u = G.radius}

中文:
定义 center
  签名: (G : SimpleGraph α)
  定义体: {u | G.eccent u = G.radius}

Depends on / 依赖: G.eccent, G.radius, eccent, radius
-/
def center (G : SimpleGraph α) : Set α :=
  {u | G.eccent u = G.radius}

/--
lemma `center_nonempty` / 引理 `center_nonempty`

English:
lemma center_nonempty
  given: [Nonempty α]
  statement: G.center.Nonempty
  proof: exists_eccent_eq_radius

中文:
引理 center_nonempty
  条件: [Nonempty α]
  结论: G.center.Nonempty
  证明: exists_eccent_eq_radius

Depends on / 依赖: exists_eccent_eq_radius
-/
lemma center_nonempty [Nonempty α] : G.center.Nonempty :=
  exists_eccent_eq_radius

/--
lemma `mem_center_iff` / 引理 `mem_center_iff`

English:
lemma mem_center_iff
  given: (u : α)
  statement: u in G.center ↔ G.eccent u = G.radius
  proof: .rfl

中文:
引理 mem_center_iff
  条件: (u : α)
  结论: u in G.center ↔ G.eccent u = G.radius
  证明: .rfl
-/
lemma mem_center_iff (u : α) : u in G.center ↔ G.eccent u = G.radius := .rfl

/--
lemma `center_eq_univ_iff_radius_eq_ediam` / 引理 `center_eq_univ_iff_radius_eq_ediam`

English:
lemma center_eq_univ_iff_radius_eq_ediam
  given: [Nonempty α]
  proof: by
  rw [radius_eq_ediam_iff]; rw [← Set.univ_subset_iff]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · use G.radius
    exact fun _ => h trivial
  · obtain ⟨e, h⟩ := h
    intro u hu
    rw [mem_center_iff]; rw [h u]
    exact le_antisymm (le_iInf fun u => (h u).ge) ((h Classical.ofNonempty) ▸ radius_le_

中文:
引理 center_eq_univ_iff_radius_eq_ediam
  条件: [Nonempty α]
  证明: by
  rw [radius_eq_ediam_iff]; rw [← Set.univ_subset_iff]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · use G.radius
    exact fun _ => h trivial
  · obtain ⟨e, h⟩ := h
    intro u hu
    rw [mem_center_iff]; rw [h u]
    exact le_antisymm (le_iInf fun u => (h u).ge) ((h Classical.ofNonempty) ▸ radius_le_

Depends on / 依赖: Classical, Classical.ofNonempty, G.radius, Set.univ_subset_iff, le_antisymm, le_iInf, mem_center_iff, ofNonempty, radius, radius_eq_ediam_iff, radius_le_eccent, univ_subset_iff
-/
lemma center_eq_univ_iff_radius_eq_ediam [Nonempty α] :
    G.center = Set.univ ↔ G.radius = G.ediam := by
  rw [radius_eq_ediam_iff]; rw [← Set.univ_subset_iff]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · use G.radius
    exact fun _ => h trivial
  · obtain ⟨e, h⟩ := h
    intro u hu
    rw [mem_center_iff]; rw [h u]
    exact le_antisymm (le_iInf fun u => (h u).ge) ((h Classical.ofNonempty) ▸ radius_le_eccent)

/--
lemma `center_eq_univ_of_subsingleton` / 引理 `center_eq_univ_of_subsingleton`

English:
lemma center_eq_univ_of_subsingleton
  given: [Subsingleton α]
  statement: G.center = Set.univ
  proof: by
  rw [Set.eq_univ_iff_forall]
  intro u
  rw [mem_center_iff]; rw [eccent_eq_zero_of_subsingleton u]; rw [eq_comm]; rw [radius_eq_zero_iff]
  tauto

中文:
引理 center_eq_univ_of_subsingleton
  条件: [Subsingleton α]
  结论: G.center = Set.univ
  证明: by
  rw [Set.eq_univ_iff_forall]
  intro u
  rw [mem_center_iff]; rw [eccent_eq_zero_of_subsingleton u]; rw [eq_comm]; rw [radius_eq_zero_iff]
  tauto

Depends on / 依赖: Set.eq_univ_iff_forall, eccent_eq_zero_of_subsingleton, eq_comm, eq_univ_iff_forall, mem_center_iff, radius_eq_zero_iff
-/
lemma center_eq_univ_of_subsingleton [Subsingleton α] : G.center = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro u
  rw [mem_center_iff]; rw [eccent_eq_zero_of_subsingleton u]; rw [eq_comm]; rw [radius_eq_zero_iff]
  tauto

/--
lemma `center_bot` / 引理 `center_bot`

English:
lemma center_bot
  statement: (⊥ : SimpleGraph α).center = Set.univ
  proof: by
  cases subsingleton_or_nontrivial α
  · exact center_eq_univ_of_subsingleton
  · rw [Set.eq_univ_iff_forall]
    intro u
    rw [mem_center_iff]; rw [eccent_bot]; rw [radius_bot]

中文:
引理 center_bot
  结论: (⊥ : SimpleGraph α).center = Set.univ
  证明: by
  cases subsingleton_or_nontrivial α
  · exact center_eq_univ_of_subsingleton
  · rw [Set.eq_univ_iff_forall]
    intro u
    rw [mem_center_iff]; rw [eccent_bot]; rw [radius_bot]

Depends on / 依赖: Set.eq_univ_iff_forall, center_eq_univ_of_subsingleton, eccent_bot, eq_univ_iff_forall, mem_center_iff, radius_bot, subsingleton_or_nontrivial
-/
lemma center_bot : (⊥ : SimpleGraph α).center = Set.univ := by
  cases subsingleton_or_nontrivial α
  · exact center_eq_univ_of_subsingleton
  · rw [Set.eq_univ_iff_forall]
    intro u
    rw [mem_center_iff]; rw [eccent_bot]; rw [radius_bot]

/--
lemma `center_top` / 引理 `center_top`

English:
lemma center_top
  statement: (⊤ : SimpleGraph α).center = Set.univ
  proof: by
  cases subsingleton_or_nontrivial α
  · exact center_eq_univ_of_subsingleton
  · rw [Set.eq_univ_iff_forall]
    intro u
    rw [mem_center_iff]; rw [eccent_top]; rw [radius_top]

中文:
引理 center_top
  结论: (⊤ : SimpleGraph α).center = Set.univ
  证明: by
  cases subsingleton_or_nontrivial α
  · exact center_eq_univ_of_subsingleton
  · rw [Set.eq_univ_iff_forall]
    intro u
    rw [mem_center_iff]; rw [eccent_top]; rw [radius_top]

Depends on / 依赖: Set.eq_univ_iff_forall, center_eq_univ_of_subsingleton, eccent_top, eq_univ_iff_forall, mem_center_iff, radius_top, subsingleton_or_nontrivial
-/
lemma center_top : (⊤ : SimpleGraph α).center = Set.univ := by
  cases subsingleton_or_nontrivial α
  · exact center_eq_univ_of_subsingleton
  · rw [Set.eq_univ_iff_forall]
    intro u
    rw [mem_center_iff]; rw [eccent_top]; rw [radius_top]

end center

end SimpleGraph
