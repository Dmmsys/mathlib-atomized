/-
Copyright (c) 2023 Kyle Miller, Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Rémi Bottinelli
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Walk.Chord
public import Mathlib.Data.Set.Card

/-!
# Connectivity of subgraphs and induced graphs

## Main definitions

* `SimpleGraph.Subgraph.Preconnected` and `SimpleGraph.Subgraph.Connected` give subgraphs
  connectivity predicates via `SimpleGraph.Subgraph.coe`.

-/

@[expose] public section

namespace SimpleGraph

universe u v
variable {V : Type u} {V' : Type v} {G : SimpleGraph V} {G' : SimpleGraph V'}

namespace Subgraph

/--
Definition of `Preconnected` / `Preconnected` 的定义

English:
structure Preconnected
  parameters: (H : G.Subgraph)
  axioms and operations (1):
    - coe : H.coe.Preconnected

中文:
结构 预连通
  参数: (H : G.子图)
  公理与运算 (1 个):
    - coe : H.coe.预连通
-/
protected structure Preconnected (H : G.Subgraph) : Prop where
  protected coe : H.coe.Preconnected

instance {H : G.Subgraph} : Coe H.Preconnected H.coe.Preconnected := ⟨Preconnected.coe⟩

instance {H : G.Subgraph} : CoeFun H.Preconnected (fun _ => forall u v : H.verts, H.coe.Reachable u v) :=
  ⟨fun h => h.coe⟩

/--
lemma `preconnected_iff` / 引理 `preconnected_iff`

English:
lemma preconnected_iff
  given: {H : G.Subgraph}
  proof: ⟨fun ⟨h⟩ => h, .mk⟩

中文:
引理 preconnected_iff
  条件: {H : G.子图}
  证明: ⟨fun ⟨h⟩ => h, .mk⟩
-/
protected lemma preconnected_iff {H : G.Subgraph} :
    H.Preconnected ↔ H.coe.Preconnected := ⟨fun ⟨h⟩ => h, .mk⟩

/--
Definition of `Connected` / `Connected` 的定义

English:
structure Connected
  parameters: (H : G.Subgraph)
  axioms and operations (1):
    - coe : H.coe.Connected

中文:
结构 连通
  参数: (H : G.子图)
  公理与运算 (1 个):
    - coe : H.coe.连通
-/
protected structure Connected (H : G.Subgraph) : Prop where
  protected coe : H.coe.Connected

instance {H : G.Subgraph} : Coe H.Connected H.coe.Connected := ⟨Connected.coe⟩

instance {H : G.Subgraph} : CoeFun H.Connected (fun _ => forall u v : H.verts, H.coe.Reachable u v) :=
  ⟨fun h => h.coe⟩

/--
lemma `connected_iff'` / 引理 `connected_iff'`

English:
lemma connected_iff'
  given: {H : G.Subgraph}
  proof: ⟨fun ⟨h⟩ => h, .mk⟩

中文:
引理 connected_iff'
  条件: {H : G.子图}
  证明: ⟨fun ⟨h⟩ => h, .mk⟩
-/
protected lemma connected_iff' {H : G.Subgraph} :
    H.Connected ↔ H.coe.Connected := ⟨fun ⟨h⟩ => h, .mk⟩

/--
lemma `connected_iff` / 引理 `connected_iff`

English:
lemma connected_iff
  given: {H : G.Subgraph}
  proof: by
  rw [H.connected_iff']; rw [connected_iff]; rw [H.preconnected_iff]; rw [Set.nonempty_coe_sort]

中文:
引理 connected_iff
  条件: {H : G.子图}
  证明: by
  rw [H.connected_iff']; rw [connected_iff]; rw [H.preconnected_iff]; rw [Set.nonempty_coe_sort]
-/
protected lemma connected_iff {H : G.Subgraph} :
    H.Connected ↔ H.Preconnected ∧ H.verts.Nonempty := by
  rw [H.connected_iff']; rw [connected_iff]; rw [H.preconnected_iff]; rw [Set.nonempty_coe_sort]

/--
lemma `Connected.preconnected` / 引理 `Connected.preconnected`

English:
lemma Connected.preconnected
  given: {H : G.Subgraph} (h : H.Connected)
  statement: H.Preconnected
  proof: by
  rw [H.connected_iff] at h; exact h.1

中文:
引理 连通.preconnected
  条件: {H : G.子图} (h : H.连通)
  结论: H.预连通
  证明: by
  rw [H.connected_iff] at h; exact h.1
-/
protected lemma Connected.preconnected {H : G.Subgraph} (h : H.Connected) : H.Preconnected := by
  rw [H.connected_iff] at h; exact h.1

/--
lemma `Connected.nonempty` / 引理 `Connected.nonempty`

English:
lemma Connected.nonempty
  given: {H : G.Subgraph} (h : H.Connected)
  statement: H.verts.Nonempty
  proof: by
  rw [H.connected_iff] at h; exact h.2

中文:
引理 连通.nonempty
  条件: {H : G.子图} (h : H.连通)
  结论: H.verts.非空
  证明: by
  rw [H.connected_iff] at h; exact h.2
-/
protected lemma Connected.nonempty {H : G.Subgraph} (h : H.Connected) : H.verts.Nonempty := by
  rw [H.connected_iff] at h; exact h.2

/--
theorem `singletonSubgraph_connected` / 定理 `singletonSubgraph_connected`

English:
theorem singletonSubgraph_connected
  given: {v : V}
  statement: (G.singletonSubgraph v).Connected
  proof: ⟨⟨Preconnected.of_subsingleton⟩⟩

@[simp]

中文:
定理 singletonSubgraph_connected
  条件: {v : V}
  结论: (G.singletonSubgraph v).连通
  证明: ⟨⟨Preconnected.of_subsingleton⟩⟩

@[simp]

Depends on / 依赖: Preconnected, Preconnected.of_subsingleton, of_subsingleton
-/
theorem singletonSubgraph_connected {v : V} : (G.singletonSubgraph v).Connected :=
  ⟨⟨Preconnected.of_subsingleton⟩⟩

@[simp]
/--
theorem `subgraphOfAdj_connected` / 定理 `subgraphOfAdj_connected`

English:
theorem subgraphOfAdj_connected
  given: {v w : V} (hvw : G.Adj v w)
  statement: (G.subgraphOfAdj hvw).Connected
  proof: by
  refine ⟨⟨?_⟩⟩
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  simp only [subgraphOfAdj_verts, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  obtain rfl | rfl := ha <;> obtain rfl | rfl := hb <;>
    first | rfl | (apply Adj.reachable; simp)

中文:
定理 subgraphOfAdj_connected
  条件: {v w : V} (hvw : G.伴随 v w)
  结论: (G.subgraphOfAdj hvw).连通
  证明: by
  refine ⟨⟨?_⟩⟩
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  simp only [subgraphOfAdj_verts, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  obtain rfl | rfl := ha <;> obtain rfl | rfl := hb <;>
    first | rfl | (apply Adj.reachable; simp)

Depends on / 依赖: Adj.reachable, Set.mem_insert_iff, Set.mem_singleton_iff, mem_insert_iff, mem_singleton_iff, reachable, subgraphOfAdj_verts
-/
theorem subgraphOfAdj_connected {v w : V} (hvw : G.Adj v w) : (G.subgraphOfAdj hvw).Connected := by
  refine ⟨⟨?_⟩⟩
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  simp only [subgraphOfAdj_verts, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  obtain rfl | rfl := ha <;> obtain rfl | rfl := hb <;>
    first | rfl | (apply Adj.reachable; simp)

/--
lemma `top_induce_pair_connected_of_adj` / 引理 `top_induce_pair_connected_of_adj`

English:
lemma top_induce_pair_connected_of_adj
  given: {u v : V} (huv : G.Adj u v)
  proof: by
  rw [← subgraphOfAdj_eq_induce huv]
  exact subgraphOfAdj_connected huv

@[gcongr, mono]

中文:
引理 top_induce_pair_connected_of_adj
  条件: {u v : V} (huv : G.伴随 u v)
  证明: by
  rw [← subgraphOfAdj_eq_induce huv]
  exact subgraphOfAdj_connected huv

@[gcongr, mono]

Depends on / 依赖: subgraphOfAdj_connected, subgraphOfAdj_eq_induce
-/
lemma top_induce_pair_connected_of_adj {u v : V} (huv : G.Adj u v) :
    ((⊤ : G.Subgraph).induce {u, v}).Connected := by
  rw [← subgraphOfAdj_eq_induce huv]
  exact subgraphOfAdj_connected huv

@[gcongr, mono]
/--
lemma `Connected.mono` / 引理 `Connected.mono`

English:
lemma Connected.mono
  statement: {H H' : G.Subgraph} (hle : H <= H') (hv : H.verts = H'.verts)
  proof: by
  rw [← Subgraph.copy_eq H' H.verts hv H'.Adj rfl]
  refine ⟨h.coe.mono ?_⟩
  rintro ⟨v, hv⟩ ⟨w, hw⟩ hvw
  exact hle.2 hvw

中文:
引理 连通.mono
  结论: {H H' : G.子图} (hle : H <= H') (hv : H.verts = H'.verts)
  证明: by
  rw [← Subgraph.copy_eq H' H.verts hv H'.Adj rfl]
  refine ⟨h.coe.mono ?_⟩
  rintro ⟨v, hv⟩ ⟨w, hw⟩ hvw
  exact hle.2 hvw
-/
protected lemma Connected.mono {H H' : G.Subgraph} (hle : H <= H') (hv : H.verts = H'.verts)
    (h : H.Connected) : H'.Connected := by
  rw [← Subgraph.copy_eq H' H.verts hv H'.Adj rfl]
  refine ⟨h.coe.mono ?_⟩
  rintro ⟨v, hv⟩ ⟨w, hw⟩ hvw
  exact hle.2 hvw

/--
lemma `Connected.mono'` / 引理 `Connected.mono'`

English:
lemma Connected.mono'
  statement: {H H' : G.Subgraph}
  proof: by
  exact h.mono ⟨hv.le, hle⟩ hv

中文:
引理 连通.mono'
  结论: {H H' : G.子图}
  证明: by
  exact h.mono ⟨hv.le, hle⟩ hv
-/
protected lemma Connected.mono' {H H' : G.Subgraph}
    (hle : forall v w, H.Adj v w -> H'.Adj v w) (hv : H.verts = H'.verts)
    (h : H.Connected) : H'.Connected := by
  exact h.mono ⟨hv.le, hle⟩ hv

/--
lemma `connected_sup` / 引理 `connected_sup`

English:
lemma connected_sup
  statement: {H K : G.Subgraph}
  proof: by
  rw [Subgraph.connected_iff']; rw [connected_iff_exists_forall_reachable]
  obtain ⟨u, hu, hu'⟩ := hn
  exists ⟨u, Or.inl hu⟩
  rintro ⟨v, (hv | hv)⟩
  · exact Reachable.map (Subgraph.inclusion (le_sup_left : H <= H ⊔ K)) (hH ⟨u, hu⟩ ⟨v, hv⟩)
  · exact Reachable.map (Subgraph.inclusion (le_sup_r

中文:
引理 connected_sup
  结论: {H K : G.子图}
  证明: by
  rw [Subgraph.connected_iff']; rw [connected_iff_exists_forall_reachable]
  obtain ⟨u, hu, hu'⟩ := hn
  exists ⟨u, Or.inl hu⟩
  rintro ⟨v, (hv | hv)⟩
  · exact Reachable.map (Subgraph.inclusion (le_sup_left : H <= H ⊔ K)) (hH ⟨u, hu⟩ ⟨v, hv⟩)
  · exact Reachable.map (Subgraph.inclusion (le_sup_r

Depends on / 依赖: Or.inl, Reachable, Reachable.map, Subgraph, Subgraph.connected_iff, Subgraph.inclusion, connected_iff, connected_iff_exists_forall_reachable, inclusion, le_sup_left, le_sup_right
-/
lemma connected_sup {H K : G.Subgraph}
    (hH : H.Preconnected) (hK : K.Preconnected) (hn : (H ⊓ K).verts.Nonempty) :
    (H ⊔ K).Connected := by
  rw [Subgraph.connected_iff']; rw [connected_iff_exists_forall_reachable]
  obtain ⟨u, hu, hu'⟩ := hn
  exists ⟨u, Or.inl hu⟩
  rintro ⟨v, (hv | hv)⟩
  · exact Reachable.map (Subgraph.inclusion (le_sup_left : H <= H ⊔ K)) (hH ⟨u, hu⟩ ⟨v, hv⟩)
  · exact Reachable.map (Subgraph.inclusion (le_sup_right : K <= H ⊔ K)) (hK ⟨u, hu'⟩ ⟨v, hv⟩)

/--
lemma `Preconnected.degree_zero_iff` / 引理 `Preconnected.degree_zero_iff`

English:
lemma Preconnected.degree_zero_iff
  statement: {H : G.Subgraph} (h : H.Preconnected) (v : H.verts)
  proof: by
  refine ⟨fun hv => Set.not_nontrivial_iff.mp fun hn => ?_, (degree_eq_zero_of_subsingleton H _ ·)⟩
  have := hn.coe_sort
  simpa [hv] using h.coe.degree_pos_of_nontrivial v

中文:
引理 预连通.degree_zero_iff
  结论: {H : G.子图} (h : H.预连通) (v : H.verts)
  证明: by
  refine ⟨fun hv => Set.not_nontrivial_iff.mp fun hn => ?_, (degree_eq_zero_of_subsingleton H _ ·)⟩
  have := hn.coe_sort
  simpa [hv] using h.coe.degree_pos_of_nontrivial v

Depends on / 依赖: Set.not_nontrivial_iff.mp, coe_sort, degree_eq_zero_of_subsingleton, degree_pos_of_nontrivial, h.coe.degree_pos_of_nontrivial, hn.coe_sort, not_nontrivial_iff
-/
lemma Preconnected.degree_zero_iff {H : G.Subgraph} (h : H.Preconnected) (v : H.verts)
    [Fintype (H.neighborSet v)] : H.degree v = 0 ↔ H.verts.Subsingleton := by
  refine ⟨fun hv => Set.not_nontrivial_iff.mp fun hn => ?_, (degree_eq_zero_of_subsingleton H _ ·)⟩
  have := hn.coe_sort
  simpa [hv] using h.coe.degree_pos_of_nontrivial v

/--
lemma `Preconnected.exists_adj_of_nontrivial` / 引理 `Preconnected.exists_adj_of_nontrivial`

English:
lemma Preconnected.exists_adj_of_nontrivial
  statement: {H : G.Subgraph} [Nontrivial H.verts]
  proof: by
  have := h.coe.exists_adj_of_nontrivial v
  tauto

中文:
引理 预连通.存在_adj_of_nontrivial
  结论: {H : G.子图} [非平凡 H.verts]
  证明: by
  have := h.coe.exists_adj_of_nontrivial v
  tauto
-/
lemma Preconnected.exists_adj_of_nontrivial {H : G.Subgraph} [Nontrivial H.verts]
    (h : H.Preconnected) (v : H.verts) : exists u, H.Adj v u := by
  have := h.coe.exists_adj_of_nontrivial v
  tauto

/--
lemma `Connected.exists_verts_eq_connectedComponentSupp` / 引理 `Connected.exists_verts_eq_connectedComponentSupp`

English:
lemma Connected.exists_verts_eq_connectedComponentSupp
  statement: {H : Subgraph G}
  proof: by
  rw [SimpleGraph.ConnectedComponent.exists]
  obtain ⟨v, hv⟩ := hc.nonempty
  use v
  ext w
  simp only [ConnectedComponent.mem_supp_iff, ConnectedComponent.eq]
  exact ⟨fun hw => by simpa using (hc ⟨w, hw⟩ ⟨v, hv⟩).map H.hom,
    fun a => a.symm.mem_subgraphVerts h hv⟩

中文:
引理 连通.存在_verts_eq_connectedComponentSupp
  结论: {H : 子图 G}
  证明: by
  rw [SimpleGraph.ConnectedComponent.exists]
  obtain ⟨v, hv⟩ := hc.nonempty
  use v
  ext w
  simp only [ConnectedComponent.mem_supp_iff, ConnectedComponent.eq]
  exact ⟨fun hw => by simpa using (hc ⟨w, hw⟩ ⟨v, hv⟩).map H.hom,
    fun a => a.symm.mem_subgraphVerts h hv⟩

Depends on / 依赖: ConnectedComponent, ConnectedComponent.eq, ConnectedComponent.mem_supp_iff, H.hom, SimpleGraph, SimpleGraph.ConnectedComponent.exists, a.symm.mem_subgraphVerts, hc.nonempty, mem_subgraphVerts, mem_supp_iff, nonempty
-/
lemma Connected.exists_verts_eq_connectedComponentSupp {H : Subgraph G}
    (hc : H.Connected) (h : forall v in H.verts, forall w, G.Adj v w -> H.Adj v w) :
    exists c : G.ConnectedComponent, H.verts = c.supp := by
  rw [SimpleGraph.ConnectedComponent.exists]
  obtain ⟨v, hv⟩ := hc.nonempty
  use v
  ext w
  simp only [ConnectedComponent.mem_supp_iff, ConnectedComponent.eq]
  exact ⟨fun hw => by simpa using (hc ⟨w, hw⟩ ⟨v, hv⟩).map H.hom,
    fun a => a.symm.mem_subgraphVerts h hv⟩

end Subgraph

namespace ConnectedComponent

variable (C : G.ConnectedComponent)

/--
Definition of `toSubgraph` / `toSubgraph` 的定义

English:
abbreviation toSubgraph
  signature: : G.Subgraph
  body: .induce ⊤ C.supp

@[simp]

中文:
缩写 toSubgraph
  签名: : G.子图
  定义体: .induce ⊤ C.supp

@[simp]

Depends on / 依赖: C.supp, induce
-/
abbrev toSubgraph : G.Subgraph :=
  .induce ⊤ C.supp

@[simp]
/--
lemma `coe_toSubgraph` / 引理 `coe_toSubgraph`

English:
lemma coe_toSubgraph
  statement: C.toSubgraph.coe = C.toSimpleGraph
  proof: .symm induce_eq_coe_induce_top C.supp

@[simp]

中文:
引理 coe_toSubgraph
  结论: C.toSubgraph.coe = C.toSimpleGraph
  证明: .symm induce_eq_coe_induce_top C.supp

@[simp]

Depends on / 依赖: C.supp, induce_eq_coe_induce_top
-/
lemma coe_toSubgraph : C.toSubgraph.coe = C.toSimpleGraph :=
.symm induce_eq_coe_induce_top C.supp

@[simp]
/--
lemma `spanningCoe_toSubgraph` / 引理 `spanningCoe_toSubgraph`

English:
lemma spanningCoe_toSubgraph
  statement: C.toSubgraph.spanningCoe = C.toSimpleGraph.spanningCoe
  proof: spanningCoe_induce_top _

中文:
引理 spanningCoe_toSubgraph
  结论: C.toSubgraph.spanningCoe = C.toSimpleGraph.spanningCoe
  证明: spanningCoe_induce_top _

Depends on / 依赖: spanningCoe_induce_top
-/
lemma spanningCoe_toSubgraph : C.toSubgraph.spanningCoe = C.toSimpleGraph.spanningCoe :=
  spanningCoe_induce_top _

/--
lemma `connected_toSubgraph` / 引理 `connected_toSubgraph`

English:
lemma connected_toSubgraph
  statement: C.toSubgraph.Connected
  proof: ⟨C.coe_toSubgraph ▸ C.connected_toSimpleGraph⟩

中文:
引理 connected_toSubgraph
  结论: C.toSubgraph.连通
  证明: ⟨C.coe_toSubgraph ▸ C.connected_toSimpleGraph⟩

Depends on / 依赖: C.coe_toSubgraph, C.connected_toSimpleGraph, coe_toSubgraph, connected_toSimpleGraph
-/
lemma connected_toSubgraph : C.toSubgraph.Connected :=
  ⟨C.coe_toSubgraph ▸ C.connected_toSimpleGraph⟩

/--
theorem `maximal_connected_toSubgraph` / 定理 `maximal_connected_toSubgraph`

English:
theorem maximal_connected_toSubgraph
  given: (C : G.ConnectedComponent)
  proof: by
  refine C.ind fun v => ⟨connected_toSubgraph _, fun G' hconn hle => ?_⟩
refine le_trans Subgraph.le_induce_top_verts Subgraph.induce_mono_right fun u hu => ?_
exact ConnectedComponent.sound .map G'.hom hconn.coe.preconnected ⟨u, hu⟩ ⟨v, hle.left rfl⟩

中文:
定理 maximal_connected_toSubgraph
  条件: (C : G.ConnectedComponent)
  证明: by
  refine C.ind fun v => ⟨connected_toSubgraph _, fun G' hconn hle => ?_⟩
refine le_trans Subgraph.le_induce_top_verts Subgraph.induce_mono_right fun u hu => ?_
exact ConnectedComponent.sound .map G'.hom hconn.coe.preconnected ⟨u, hu⟩ ⟨v, hle.left rfl⟩

Depends on / 依赖: C.ind, ConnectedComponent, ConnectedComponent.sound, Subgraph, Subgraph.induce_mono_right, Subgraph.le_induce_top_verts, connected_toSubgraph, hconn.coe.preconnected, hle.left, induce_mono_right, le_induce_top_verts, le_trans, preconnected
-/
theorem maximal_connected_toSubgraph (C : G.ConnectedComponent) :
    Maximal Subgraph.Connected C.toSubgraph := by
  refine C.ind fun v => ⟨connected_toSubgraph _, fun G' hconn hle => ?_⟩
refine le_trans Subgraph.le_induce_top_verts Subgraph.induce_mono_right fun u hu => ?_
exact ConnectedComponent.sound .map G'.hom hconn.coe.preconnected ⟨u, hu⟩ ⟨v, hle.left rfl⟩

/--
theorem `maximal_subgraph_connected_iff` / 定理 `maximal_subgraph_connected_iff`

English:
theorem maximal_subgraph_connected_iff
  given: (G' : G.Subgraph)
  proof: by
  refine ⟨fun ⟨hconn, h⟩ => ?_, fun ⟨C, h⟩ => ?_⟩
  · have ⟨v, hv⟩ := hconn.nonempty
    suffices G' <= (G.connectedComponentMk v).toSubgraph from
      ⟨G.connectedComponentMk v, le_antisymm (h (connected_toSubgraph _) this) this⟩
exact le_trans Subgraph.le_induce_top_verts Subgraph.induce_mono_

中文:
定理 maximal_subgraph_connected_iff
  条件: (G' : G.子图)
  证明: by
  refine ⟨fun ⟨hconn, h⟩ => ?_, fun ⟨C, h⟩ => ?_⟩
  · have ⟨v, hv⟩ := hconn.nonempty
    suffices G' <= (G.connectedComponentMk v).toSubgraph from
      ⟨G.connectedComponentMk v, le_antisymm (h (connected_toSubgraph _) this) this⟩
exact le_trans Subgraph.le_induce_top_verts Subgraph.induce_mono_

Depends on / 依赖: ConnectedComponent, ConnectedComponent.sound, G.connectedComponentMk, Subgraph, Subgraph.induce_mono_right, Subgraph.le_induce_top_verts, connectedComponentMk, connected_toSubgraph, hconn.coe.preconnected, hconn.nonempty, induce_mono_right, le_antisymm, le_induce_top_verts, le_trans, maximal_connected_toSubgraph, nonempty, preconnected, toSubgraph
-/
theorem maximal_subgraph_connected_iff (G' : G.Subgraph) :
    Maximal Subgraph.Connected G' ↔ exists C : G.ConnectedComponent, C.toSubgraph = G' := by
  refine ⟨fun ⟨hconn, h⟩ => ?_, fun ⟨C, h⟩ => ?_⟩
  · have ⟨v, hv⟩ := hconn.nonempty
    suffices G' <= (G.connectedComponentMk v).toSubgraph from
      ⟨G.connectedComponentMk v, le_antisymm (h (connected_toSubgraph _) this) this⟩
exact le_trans Subgraph.le_induce_top_verts Subgraph.induce_mono_right fun u hu =>
ConnectedComponent.sound .map G'.hom hconn.coe.preconnected ⟨u, hu⟩ ⟨v, hv⟩
  · exact h ▸ maximal_connected_toSubgraph _

end ConnectedComponent

/-! ### Walks as subgraphs -/

namespace Walk

variable {u v w : V}

/-- The subgraph consisting of the vertices and edges of the walk. -/
@[simp]
/--
Definition of `toSubgraph` / `toSubgraph` 的定义

English:
definition toSubgraph
  signature: {u v : V}

中文:
定义 toSubgraph
  签名: {u v : V}
-/
protected def toSubgraph {u v : V} : G.Walk u v -> G.Subgraph
  | nil => G.singletonSubgraph u
  | cons h p => G.subgraphOfAdj h ⊔ p.toSubgraph

/--
theorem `toSubgraph_cons_nil_eq_subgraphOfAdj` / 定理 `toSubgraph_cons_nil_eq_subgraphOfAdj`

English:
theorem toSubgraph_cons_nil_eq_subgraphOfAdj
  given: (h : G.Adj u v)
  proof: by simp

中文:
定理 toSubgraph_cons_nil_eq_subgraphOfAdj
  条件: (h : G.伴随 u v)
  证明: by simp
-/
theorem toSubgraph_cons_nil_eq_subgraphOfAdj (h : G.Adj u v) :
    (cons h nil).toSubgraph = G.subgraphOfAdj h := by simp

/--
theorem `mem_verts_toSubgraph` / 定理 `mem_verts_toSubgraph`

English:
theorem mem_verts_toSubgraph
  given: (p : G.Walk u v)
  statement: w in p.toSubgraph.verts ↔ w in p.support
  proof: by
  induction p with
  | nil => simp
  | cons h p' ih =>
    rename_i x y z
    have : w = y ∨ w in p'.support ↔ w in p'.support :=
      ⟨by rintro (rfl | h) <;> simp [*], by simp +contextual⟩
    simp [ih, or_assoc, this]

中文:
定理 mem_verts_toSubgraph
  条件: (p : G.途径 u v)
  结论: w in p.toSubgraph.verts ↔ w in p.support
  证明: by
  induction p with
  | nil => simp
  | cons h p' ih =>
    rename_i x y z
    have : w = y ∨ w in p'.support ↔ w in p'.support :=
      ⟨by rintro (rfl | h) <;> simp [*], by simp +contextual⟩
    simp [ih, or_assoc, this]

Depends on / 依赖: contextual, or_assoc, rename_i, support
-/
theorem mem_verts_toSubgraph (p : G.Walk u v) : w in p.toSubgraph.verts ↔ w in p.support := by
  induction p with
  | nil => simp
  | cons h p' ih =>
    rename_i x y z
    have : w = y ∨ w in p'.support ↔ w in p'.support :=
      ⟨by rintro (rfl | h) <;> simp [*], by simp +contextual⟩
    simp [ih, or_assoc, this]

/--
lemma `not_nil_of_adj_toSubgraph` / 引理 `not_nil_of_adj_toSubgraph`

English:
lemma not_nil_of_adj_toSubgraph
  given: {u v} {x : V} {p : G.Walk u v} (hadj : p.toSubgraph.Adj w x)
  proof: by
  cases p <;> simp_all

中文:
引理 not_nil_of_adj_toSubgraph
  条件: {u v} {x : V} {p : G.途径 u v} (hadj : p.toSubgraph.伴随 w x)
  证明: by
  cases p <;> simp_all
-/
lemma not_nil_of_adj_toSubgraph {u v} {x : V} {p : G.Walk u v} (hadj : p.toSubgraph.Adj w x) :
    ¬p.Nil := by
  cases p <;> simp_all

/--
lemma `start_mem_verts_toSubgraph` / 引理 `start_mem_verts_toSubgraph`

English:
lemma start_mem_verts_toSubgraph
  given: (p : G.Walk u v)
  statement: u in p.toSubgraph.verts
  proof: by
  simp [mem_verts_toSubgraph]

中文:
引理 start_mem_verts_toSubgraph
  条件: (p : G.途径 u v)
  结论: u in p.toSubgraph.verts
  证明: by
  simp [mem_verts_toSubgraph]

Depends on / 依赖: mem_verts_toSubgraph
-/
lemma start_mem_verts_toSubgraph (p : G.Walk u v) : u in p.toSubgraph.verts := by
  simp [mem_verts_toSubgraph]

/--
lemma `end_mem_verts_toSubgraph` / 引理 `end_mem_verts_toSubgraph`

English:
lemma end_mem_verts_toSubgraph
  given: (p : G.Walk u v)
  statement: v in p.toSubgraph.verts
  proof: by
  simp [mem_verts_toSubgraph]

@[simp]

中文:
引理 end_mem_verts_toSubgraph
  条件: (p : G.途径 u v)
  结论: v in p.toSubgraph.verts
  证明: by
  simp [mem_verts_toSubgraph]

@[simp]

Depends on / 依赖: mem_verts_toSubgraph
-/
lemma end_mem_verts_toSubgraph (p : G.Walk u v) : v in p.toSubgraph.verts := by
  simp [mem_verts_toSubgraph]

@[simp]
/--
theorem `verts_toSubgraph` / 定理 `verts_toSubgraph`

English:
theorem verts_toSubgraph
  given: (p : G.Walk u v)
  statement: p.toSubgraph.verts = { w | w in p.support }
  proof: Set.ext fun _ => p.mem_verts_toSubgraph

中文:
定理 verts_toSubgraph
  条件: (p : G.途径 u v)
  结论: p.toSubgraph.verts = { w | w in p.support }
  证明: Set.ext fun _ => p.mem_verts_toSubgraph

Depends on / 依赖: Set.ext, mem_verts_toSubgraph, p.mem_verts_toSubgraph
-/
theorem verts_toSubgraph (p : G.Walk u v) : p.toSubgraph.verts = { w | w in p.support } :=
  Set.ext fun _ => p.mem_verts_toSubgraph

/--
theorem `mem_edges_toSubgraph` / 定理 `mem_edges_toSubgraph`

English:
theorem mem_edges_toSubgraph
  given: (p : G.Walk u v) {e : Sym2 V}
  proof: by induction p <;> simp [*]

@[simp]

中文:
定理 mem_edges_toSubgraph
  条件: (p : G.途径 u v) {e : Sym2 V}
  证明: by induction p <;> simp [*]

@[simp]
-/
theorem mem_edges_toSubgraph (p : G.Walk u v) {e : Sym2 V} :
    e in p.toSubgraph.edgeSet ↔ e in p.edges := by induction p <;> simp [*]

@[simp]
/--
theorem `edgeSet_toSubgraph` / 定理 `edgeSet_toSubgraph`

English:
theorem edgeSet_toSubgraph
  given: (p : G.Walk u v)
  statement: p.toSubgraph.edgeSet = p.edgeSet
  proof: Set.ext fun _ => p.mem_edges_toSubgraph

中文:
定理 edgeSet_toSubgraph
  条件: (p : G.途径 u v)
  结论: p.toSubgraph.edgeSet = p.edgeSet
  证明: Set.ext fun _ => p.mem_edges_toSubgraph

Depends on / 依赖: Set.ext, mem_edges_toSubgraph, p.mem_edges_toSubgraph
-/
theorem edgeSet_toSubgraph (p : G.Walk u v) : p.toSubgraph.edgeSet = p.edgeSet :=
  Set.ext fun _ => p.mem_edges_toSubgraph

/--
theorem `_root_.SimpleGraph.Adj.toSubgraph_toWalk` / 定理 `_root_.SimpleGraph.Adj.toSubgraph_toWalk`

English:
theorem _root_.SimpleGraph.Adj.toSubgraph_toWalk
  given: (h : G.Adj u v)
  proof: by
  ext <;> simp

@[simp]

中文:
定理 _root_.简单图.伴随.toSubgraph_toWalk
  条件: (h : G.伴随 u v)
  证明: by
  ext <;> simp

@[simp]
-/
theorem _root_.SimpleGraph.Adj.toSubgraph_toWalk (h : G.Adj u v) :
    h.toWalk.toSubgraph = G.subgraphOfAdj h := by
  ext <;> simp

@[simp]
/--
theorem `toSubgraph_append` / 定理 `toSubgraph_append`

English:
theorem toSubgraph_append
  given: (p : G.Walk u v) (q : G.Walk v w)
  proof: by induction p <;> simp [*, sup_assoc]

@[simp]

中文:
定理 toSubgraph_append
  条件: (p : G.途径 u v) (q : G.途径 v w)
  证明: by induction p <;> simp [*, sup_assoc]

@[simp]

Depends on / 依赖: sup_assoc
-/
theorem toSubgraph_append (p : G.Walk u v) (q : G.Walk v w) :
    (p.append q).toSubgraph = p.toSubgraph ⊔ q.toSubgraph := by induction p <;> simp [*, sup_assoc]

@[simp]
/--
theorem `toSubgraph_reverse` / 定理 `toSubgraph_reverse`

English:
theorem toSubgraph_reverse
  given: (p : G.Walk u v)
  statement: p.reverse.toSubgraph = p.toSubgraph
  proof: by
  induction p with
  | nil => simp
  | cons _ _ _ =>
    simp only [*, Walk.toSubgraph, reverse_cons, toSubgraph_append, subgraphOfAdj_symm]
    rw [sup_comm]
    congr
    ext <;> simp [-Set.bot_eq_empty]

@[simp]

中文:
定理 toSubgraph_reverse
  条件: (p : G.途径 u v)
  结论: p.reverse.toSubgraph = p.toSubgraph
  证明: by
  induction p with
  | nil => simp
  | cons _ _ _ =>
    simp only [*, Walk.toSubgraph, reverse_cons, toSubgraph_append, subgraphOfAdj_symm]
    rw [sup_comm]
    congr
    ext <;> simp [-Set.bot_eq_empty]

@[simp]

Depends on / 依赖: Set.bot_eq_empty, Walk.toSubgraph, bot_eq_empty, reverse_cons, subgraphOfAdj_symm, sup_comm, toSubgraph, toSubgraph_append
-/
theorem toSubgraph_reverse (p : G.Walk u v) : p.reverse.toSubgraph = p.toSubgraph := by
  induction p with
  | nil => simp
  | cons _ _ _ =>
    simp only [*, Walk.toSubgraph, reverse_cons, toSubgraph_append, subgraphOfAdj_symm]
    rw [sup_comm]
    congr
    ext <;> simp [-Set.bot_eq_empty]

@[simp]
/--
theorem `toSubgraph_rotate` / 定理 `toSubgraph_rotate`

English:
theorem toSubgraph_rotate
  given: [DecidableEq V] (c : G.Walk v v) (h : u in c.support)
  proof: by
  rw [rotate]; rw [toSubgraph_append]; rw [sup_comm]; rw [← toSubgraph_append]; rw [take_spec]

@[simp]

中文:
定理 toSubgraph_rotate
  条件: [DecidableEq V] (c : G.途径 v v) (h : u in c.support)
  证明: by
  rw [rotate]; rw [toSubgraph_append]; rw [sup_comm]; rw [← toSubgraph_append]; rw [take_spec]

@[simp]

Depends on / 依赖: rotate, sup_comm, take_spec, toSubgraph_append
-/
theorem toSubgraph_rotate [DecidableEq V] (c : G.Walk v v) (h : u in c.support) :
    (c.rotate u h).toSubgraph = c.toSubgraph := by
  rw [rotate]; rw [toSubgraph_append]; rw [sup_comm]; rw [← toSubgraph_append]; rw [take_spec]

@[simp]
/--
theorem `toSubgraph_map` / 定理 `toSubgraph_map`

English:
theorem toSubgraph_map
  given: (f : G ->g G') (p : G.Walk u v)
  proof: by induction p <;> simp [*, Subgraph.map_sup]

中文:
定理 toSubgraph_map
  条件: (f : G ->g G') (p : G.途径 u v)
  证明: by induction p <;> simp [*, Subgraph.map_sup]

Depends on / 依赖: Subgraph, Subgraph.map_sup, map_sup
-/
theorem toSubgraph_map (f : G ->g G') (p : G.Walk u v) :
    (p.map f).toSubgraph = p.toSubgraph.map f := by induction p <;> simp [*, Subgraph.map_sup]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `adj_toSubgraph_mapLe` / 引理 `adj_toSubgraph_mapLe`

English:
lemma adj_toSubgraph_mapLe
  given: {G' : SimpleGraph V} {w x : V} {p : G.Walk u v} (h : G <= G')
  proof: by
  simp

@[simp]

中文:
引理 adj_toSubgraph_mapLe
  条件: {G' : 简单图 V} {w x : V} {p : G.途径 u v} (h : G <= G')
  证明: by
  simp

@[simp]
-/
lemma adj_toSubgraph_mapLe {G' : SimpleGraph V} {w x : V} {p : G.Walk u v} (h : G <= G') :
    (p.mapLe h).toSubgraph.Adj w x ↔ p.toSubgraph.Adj w x := by
  simp

@[simp]
/--
theorem `finite_neighborSet_toSubgraph` / 定理 `finite_neighborSet_toSubgraph`

English:
theorem finite_neighborSet_toSubgraph
  given: (p : G.Walk u v)
  statement: (p.toSubgraph.neighborSet w).Finite
  proof: by
  induction p with
  | nil =>
    rw [Walk.toSubgraph]; rw [neighborSet_singletonSubgraph]
    apply Set.toFinite
  | cons ha _ ih =>
    rw [Walk.toSubgraph]; rw [Subgraph.neighborSet_sup]
    refine Set.Finite.union ?_ ih
    refine Set.Finite.subset ?_ (neighborSet_subgraphOfAdj_subset ha)
   

中文:
定理 finite_neighborSet_toSubgraph
  条件: (p : G.途径 u v)
  结论: (p.toSubgraph.neighborSet w).有限
  证明: by
  induction p with
  | nil =>
    rw [Walk.toSubgraph]; rw [neighborSet_singletonSubgraph]
    apply Set.toFinite
  | cons ha _ ih =>
    rw [Walk.toSubgraph]; rw [Subgraph.neighborSet_sup]
    refine Set.Finite.union ?_ ih
    refine Set.Finite.subset ?_ (neighborSet_subgraphOfAdj_subset ha)
   

Depends on / 依赖: Finite, Set.Finite.subset, Set.Finite.union, Set.toFinite, Subgraph, Subgraph.neighborSet_sup, Walk.toSubgraph, neighborSet_singletonSubgraph, neighborSet_subgraphOfAdj_subset, neighborSet_sup, subset, toFinite, toSubgraph
-/
theorem finite_neighborSet_toSubgraph (p : G.Walk u v) : (p.toSubgraph.neighborSet w).Finite := by
  induction p with
  | nil =>
    rw [Walk.toSubgraph]; rw [neighborSet_singletonSubgraph]
    apply Set.toFinite
  | cons ha _ ih =>
    rw [Walk.toSubgraph]; rw [Subgraph.neighborSet_sup]
    refine Set.Finite.union ?_ ih
    refine Set.Finite.subset ?_ (neighborSet_subgraphOfAdj_subset ha)
    apply Set.toFinite

/--
lemma `toSubgraph_le_induce_support` / 引理 `toSubgraph_le_induce_support`

English:
lemma toSubgraph_le_induce_support
  given: (p : G.Walk u v)
  proof: by
  convert! Subgraph.le_induce_top_verts
  exact p.verts_toSubgraph.symm

中文:
引理 toSubgraph_le_induce_support
  条件: (p : G.途径 u v)
  证明: by
  convert! Subgraph.le_induce_top_verts
  exact p.verts_toSubgraph.symm

Depends on / 依赖: Subgraph, Subgraph.le_induce_top_verts, convert, le_induce_top_verts, p.verts_toSubgraph.symm, verts_toSubgraph
-/
lemma toSubgraph_le_induce_support (p : G.Walk u v) :
    p.toSubgraph <= (⊤ : G.Subgraph).induce {v | v in p.support} := by
  convert! Subgraph.le_induce_top_verts
  exact p.verts_toSubgraph.symm

/--
theorem `toSubgraph_adj_getVert` / 定理 `toSubgraph_adj_getVert`

English:
theorem toSubgraph_adj_getVert
  given: {u v} (w : G.Walk u v) {i : Nat} (hi : i < w.length)
  proof: by
  induction w generalizing i with
  | nil => cases hi
  | cons hxy i' ih =>
    cases i
    · simp
    · simp only [Walk.toSubgraph, getVert_cons_succ, Subgraph.sup_adj, subgraphOfAdj_adj, Sym2.eq,
        Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
      right
      exact ih (Nat.succ_lt_su

中文:
定理 toSubgraph_adj_getVert
  条件: {u v} (w : G.途径 u v) {i : 自然数} (hi : i < w.length)
  证明: by
  induction w generalizing i with
  | nil => cases hi
  | cons hxy i' ih =>
    cases i
    · simp
    · simp only [Walk.toSubgraph, getVert_cons_succ, Subgraph.sup_adj, subgraphOfAdj_adj, Sym2.eq,
        Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
      right
      exact ih (Nat.succ_lt_su

Depends on / 依赖: Nat.succ_lt_succ_iff.mp, Prod.mk.injEq, Prod.swap_prod_mk, Subgraph, Subgraph.sup_adj, Sym2.eq, Sym2.rel_iff, Walk.toSubgraph, generalizing, getVert_cons_succ, rel_iff, subgraphOfAdj_adj, succ_lt_succ_iff, sup_adj, swap_prod_mk, toSubgraph
-/
theorem toSubgraph_adj_getVert {u v} (w : G.Walk u v) {i : Nat} (hi : i < w.length) :
    w.toSubgraph.Adj (w.getVert i) (w.getVert (i + 1)) := by
  induction w generalizing i with
  | nil => cases hi
  | cons hxy i' ih =>
    cases i
    · simp
    · simp only [Walk.toSubgraph, getVert_cons_succ, Subgraph.sup_adj, subgraphOfAdj_adj, Sym2.eq,
        Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
      right
      exact ih (Nat.succ_lt_succ_iff.mp hi)

/--
theorem `toSubgraph_adj_snd` / 定理 `toSubgraph_adj_snd`

English:
theorem toSubgraph_adj_snd
  given: {u v} (w : G.Walk u v) (h : ¬ w.Nil)
  statement: w.toSubgraph.Adj u w.snd
  proof: by
  simpa using w.toSubgraph_adj_getVert (not_nil_iff_lt_length.mp h)

中文:
定理 toSubgraph_adj_snd
  条件: {u v} (w : G.途径 u v) (h : ¬ w.Nil)
  结论: w.toSubgraph.伴随 u w.snd
  证明: by
  simpa using w.toSubgraph_adj_getVert (not_nil_iff_lt_length.mp h)

Depends on / 依赖: not_nil_iff_lt_length, not_nil_iff_lt_length.mp, toSubgraph_adj_getVert, w.toSubgraph_adj_getVert
-/
theorem toSubgraph_adj_snd {u v} (w : G.Walk u v) (h : ¬ w.Nil) : w.toSubgraph.Adj u w.snd := by
  simpa using w.toSubgraph_adj_getVert (not_nil_iff_lt_length.mp h)

/--
theorem `toSubgraph_adj_penultimate` / 定理 `toSubgraph_adj_penultimate`

English:
theorem toSubgraph_adj_penultimate
  given: {u v} (w : G.Walk u v) (h : ¬ w.Nil)
  proof: by
  rw [not_nil_iff_lt_length] at h
  simpa [show w.length - 1 + 1 = w.length by lia]
    using w.toSubgraph_adj_getVert (by lia : w.length - 1 < w.length)

中文:
定理 toSubgraph_adj_penultimate
  条件: {u v} (w : G.途径 u v) (h : ¬ w.Nil)
  证明: by
  rw [not_nil_iff_lt_length] at h
  simpa [show w.length - 1 + 1 = w.length by lia]
    using w.toSubgraph_adj_getVert (by lia : w.length - 1 < w.length)

Depends on / 依赖: length, not_nil_iff_lt_length, toSubgraph_adj_getVert, w.length, w.toSubgraph_adj_getVert
-/
theorem toSubgraph_adj_penultimate {u v} (w : G.Walk u v) (h : ¬ w.Nil) :
    w.toSubgraph.Adj w.penultimate v := by
  rw [not_nil_iff_lt_length] at h
  simpa [show w.length - 1 + 1 = w.length by lia]
    using w.toSubgraph_adj_getVert (by lia : w.length - 1 < w.length)

/--
lemma `adj_toSubgraph_iff_mem_edges` / 引理 `adj_toSubgraph_iff_mem_edges`

English:
lemma adj_toSubgraph_iff_mem_edges
  given: {u v u' v' : V} {p : G.Walk u v}
  proof: by
  rw [← mem_edges_toSubgraph]; rw [Subgraph.mem_edgeSet]

中文:
引理 adj_toSubgraph_iff_mem_edges
  条件: {u v u' v' : V} {p : G.途径 u v}
  证明: by
  rw [← mem_edges_toSubgraph]; rw [Subgraph.mem_edgeSet]

Depends on / 依赖: Subgraph, Subgraph.mem_edgeSet, mem_edgeSet, mem_edges_toSubgraph
-/
lemma adj_toSubgraph_iff_mem_edges {u v u' v' : V} {p : G.Walk u v} :
    p.toSubgraph.Adj u' v' ↔ s(u', v') in p.edges := by
  rw [← mem_edges_toSubgraph]; rw [Subgraph.mem_edgeSet]

/--
theorem `toSubgraph_adj_iff` / 定理 `toSubgraph_adj_iff`

English:
theorem toSubgraph_adj_iff
  given: {u v u' v'} (w : G.Walk u v)
  proof: by
  grind [adj_toSubgraph_iff_mem_edges, mk_mem_edges_iff_exists]

中文:
定理 toSubgraph_adj_iff
  条件: {u v u' v'} (w : G.途径 u v)
  证明: by
  grind [adj_toSubgraph_iff_mem_edges, mk_mem_edges_iff_exists]

Depends on / 依赖: adj_toSubgraph_iff_mem_edges, mk_mem_edges_iff_exists
-/
theorem toSubgraph_adj_iff {u v u' v'} (w : G.Walk u v) :
    w.toSubgraph.Adj u' v' ↔ exists i, s(w.getVert i, w.getVert (i + 1)) =
      s(u', v') ∧ i < w.length := by
  grind [adj_toSubgraph_iff_mem_edges, mk_mem_edges_iff_exists]

/--
lemma `mem_support_of_adj_toSubgraph` / 引理 `mem_support_of_adj_toSubgraph`

English:
lemma mem_support_of_adj_toSubgraph
  given: {u v u' v' : V} {p : G.Walk u v} (hp : p.toSubgraph.Adj u' v')
  proof: p.mem_verts_toSubgraph.mp (p.toSubgraph.edge_vert hp)

中文:
引理 mem_support_of_adj_toSubgraph
  条件: {u v u' v' : V} {p : G.途径 u v} (hp : p.toSubgraph.伴随 u' v')
  证明: p.mem_verts_toSubgraph.mp (p.toSubgraph.edge_vert hp)

Depends on / 依赖: edge_vert, mem_verts_toSubgraph, p.mem_verts_toSubgraph.mp, p.toSubgraph.edge_vert, toSubgraph
-/
lemma mem_support_of_adj_toSubgraph {u v u' v' : V} {p : G.Walk u v} (hp : p.toSubgraph.Adj u' v') :
    u' in p.support := p.mem_verts_toSubgraph.mp (p.toSubgraph.edge_vert hp)

/--
theorem `toSubgraph_le_iff` / 定理 `toSubgraph_le_iff`

English:
theorem toSubgraph_le_iff
  given: {w : G.Walk u v} (hnil : ¬w.Nil) {G' : G.Subgraph}
  proof: by
refine ⟨fun hw e he => Subgraph.edgeSet_mono hw w.mem_edges_toSubgraph.mpr he, fun hw => ?_⟩
refine ⟨fun v' hv' => ?_, fun u' v' hadj => hw w.mem_edges_toSubgraph.mp (hadj : s(_, _) in _)⟩
  rw [mem_verts_toSubgraph]; rw [mem_support_iff_exists_mem_edges_of_not_nil hnil] at hv'
  have ⟨e, he, hv'

中文:
定理 toSubgraph_le_iff
  条件: {w : G.途径 u v} (hnil : ¬w.Nil) {G' : G.子图}
  证明: by
refine ⟨fun hw e he => Subgraph.edgeSet_mono hw w.mem_edges_toSubgraph.mpr he, fun hw => ?_⟩
refine ⟨fun v' hv' => ?_, fun u' v' hadj => hw w.mem_edges_toSubgraph.mp (hadj : s(_, _) in _)⟩
  rw [mem_verts_toSubgraph]; rw [mem_support_iff_exists_mem_edges_of_not_nil hnil] at hv'
  have ⟨e, he, hv'

Depends on / 依赖: Subgraph, Subgraph.edgeSet_mono, edgeSet_mono, mem_edges_toSubgraph, mem_support_iff_exists_mem_edges_of_not_nil, mem_verts_of_mem_edge, mem_verts_toSubgraph, w.mem_edges_toSubgraph.mp, w.mem_edges_toSubgraph.mpr
-/
theorem toSubgraph_le_iff {w : G.Walk u v} (hnil : ¬w.Nil) {G' : G.Subgraph} :
    w.toSubgraph <= G' ↔ w.edgeSet subseteq G'.edgeSet := by
refine ⟨fun hw e he => Subgraph.edgeSet_mono hw w.mem_edges_toSubgraph.mpr he, fun hw => ?_⟩
refine ⟨fun v' hv' => ?_, fun u' v' hadj => hw w.mem_edges_toSubgraph.mp (hadj : s(_, _) in _)⟩
  rw [mem_verts_toSubgraph]; rw [mem_support_iff_exists_mem_edges_of_not_nil hnil] at hv'
  have ⟨e, he, hv'e⟩ := hv'
  exact G'.mem_verts_of_mem_edge (hw he) hv'e

/--
lemma `toSubgraph_bypass_le_toSubgraph` / 引理 `toSubgraph_bypass_le_toSubgraph`

English:
lemma toSubgraph_bypass_le_toSubgraph
  given: {u v : V} {p : G.Walk u v} [DecidableEq V]
  proof: by
  constructor
  · simpa using! p.support_bypass_subset_support
  · simpa [adj_toSubgraph_iff_mem_edges] using! fun _ _ h => p.edges_toPath_subset_edges h

中文:
引理 toSubgraph_bypass_le_toSubgraph
  条件: {u v : V} {p : G.途径 u v} [DecidableEq V]
  证明: by
  constructor
  · simpa using! p.support_bypass_subset_support
  · simpa [adj_toSubgraph_iff_mem_edges] using! fun _ _ h => p.edges_toPath_subset_edges h

Depends on / 依赖: adj_toSubgraph_iff_mem_edges, edges_toPath_subset_edges, p.edges_toPath_subset_edges, p.support_bypass_subset_support, support_bypass_subset_support
-/
lemma toSubgraph_bypass_le_toSubgraph {u v : V} {p : G.Walk u v} [DecidableEq V] :
    p.bypass.toSubgraph <= p.toSubgraph := by
  constructor
  · simpa using! p.support_bypass_subset_support
  · simpa [adj_toSubgraph_iff_mem_edges] using! fun _ _ h => p.edges_toPath_subset_edges h

/--
Definition of `mapToSubgraph` / `mapToSubgraph` 的定义

English:
definition mapToSubgraph
  signature: {u v : V}
  body: (le_sup_left : _ <= Walk.toSubgraph _).right rfl let h : cons ..
.toSubgraph.coe.Adj ⟨_, h.fst_mem⟩ ⟨_, h.snd_mem⟩ := h let h : cons ..
cons h .map Subgraph.inclusion le_sup_right mapToSubgraph _

中文:
定义 mapToSubgraph
  签名: {u v : V}
  定义体: (le_sup_left : _ <= Walk.toSubgraph _).right rfl let h : cons ..
.toSubgraph.coe.Adj ⟨_, h.fst_mem⟩ ⟨_, h.snd_mem⟩ := h let h : cons ..
cons h .map Subgraph.inclusion le_sup_right mapToSubgraph _

Depends on / 依赖: Walk.toSubgraph, le_sup_left, toSubgraph
-/
def mapToSubgraph {u v : V} : forall w : G.Walk u v, w.toSubgraph.coe.Walk
    ⟨_, w.start_mem_verts_toSubgraph⟩ ⟨_, w.end_mem_verts_toSubgraph⟩
  | nil => nil
  | cons .. =>
.toSubgraph.Adj .. := (le_sup_left : _ <= Walk.toSubgraph _).right rfl let h : cons ..
.toSubgraph.coe.Adj ⟨_, h.fst_mem⟩ ⟨_, h.snd_mem⟩ := h let h : cons ..
cons h .map Subgraph.inclusion le_sup_right mapToSubgraph _

set_option backward.isDefEq.respectTransparency false in
/--
theorem `map_mapToSubgraph_hom` / 定理 `map_mapToSubgraph_hom`

English:
theorem map_mapToSubgraph_hom
  given: {u v : V}
  statement: forall w : G.Walk u v, w.mapToSubgraph.map w.toSubgraph.hom = w

中文:
定理 map_mapToSubgraph_hom
  条件: {u v : V}
  结论: 对任意 w : G.途径 u v, w.mapToSubgraph.map w.toSubgraph.hom = w
-/
theorem map_mapToSubgraph_hom {u v : V} : forall w : G.Walk u v, w.mapToSubgraph.map w.toSubgraph.hom = w
  | nil => rfl
  | cons _ w => by
    rw [mapToSubgraph]; rw [Walk.map]; rw [map_map]
    exact congrArg₂ _ rfl w.map_mapToSubgraph_hom

set_option backward.isDefEq.respectTransparency false in
/--
theorem `map_mapToSubgraph_eq_induce` / 定理 `map_mapToSubgraph_eq_induce`

English:
theorem map_mapToSubgraph_eq_induce
  given: (s : Set V) {u v : V}

中文:
定理 map_mapToSubgraph_eq_induce
  条件: (s : 集合 V) {u v : V}
-/
theorem map_mapToSubgraph_eq_induce (s : Set V) {u v : V} :
    forall (w : G.Walk u v) (hs : forall x in w.support, x in s),
      w.mapToSubgraph.map (⟨(⟨·, by grind [mem_verts_toSubgraph]⟩), w.toSubgraph.adj_sub⟩ :
        w.toSubgraph.coe ->g G.induce s) = w.induce s hs
  | nil, hs => rfl
  | cons hadj w, hs => by
    rw [mapToSubgraph]; rw [map_cons]; rw [map_map]
exact congrArg _ w.map_mapToSubgraph_eq_induce s (hs · <| List.mem_of_mem_tail ·)

/--
theorem `map_mapToSubgraph_eq_induce_id` / 定理 `map_mapToSubgraph_eq_induce_id`

English:
theorem map_mapToSubgraph_eq_induce_id
  given: {u v : V} (w : G.Walk u v)
  proof: w.map_mapToSubgraph_eq_induce ..

中文:
定理 map_mapToSubgraph_eq_induce_id
  条件: {u v : V} (w : G.途径 u v)
  证明: w.map_mapToSubgraph_eq_induce ..

Depends on / 依赖: map_mapToSubgraph_eq_induce, w.map_mapToSubgraph_eq_induce
-/
theorem map_mapToSubgraph_eq_induce_id {u v : V} (w : G.Walk u v) :
    w.mapToSubgraph.map (⟨fun v => ⟨v, w.mem_verts_toSubgraph.mp v.prop⟩, w.toSubgraph.adj_sub⟩ :
      w.toSubgraph.coe ->g G.induce _) = w.induce _ (fun _ => id) :=
  w.map_mapToSubgraph_eq_induce ..

/--
theorem `isInduced_toSubgraph` / 定理 `isInduced_toSubgraph`

English:
theorem isInduced_toSubgraph
  given: {w : G.Walk u v}
  statement: w.toSubgraph.IsInduced ↔ w.IsChordless
  proof: by
  simp_rw [Subgraph.IsInduced, IsChordless, IsChord, Sym2.forall, Sym2.lift_mk, G.mem_edgeSet,
    mem_verts_toSubgraph, adj_toSubgraph_iff_mem_edges]
  grind only

中文:
定理 isInduced_toSubgraph
  条件: {w : G.途径 u v}
  结论: w.toSubgraph.是Induced ↔ w.IsChordless
  证明: by
  simp_rw [Subgraph.IsInduced, IsChordless, IsChord, Sym2.forall, Sym2.lift_mk, G.mem_edgeSet,
    mem_verts_toSubgraph, adj_toSubgraph_iff_mem_edges]
  grind only

Depends on / 依赖: G.mem_edgeSet, IsChord, IsChordless, IsInduced, Subgraph, Subgraph.IsInduced, Sym2.forall, Sym2.lift_mk, adj_toSubgraph_iff_mem_edges, lift_mk, mem_edgeSet, mem_verts_toSubgraph, simp_rw
-/
theorem isInduced_toSubgraph {w : G.Walk u v} : w.toSubgraph.IsInduced ↔ w.IsChordless := by
  simp_rw [Subgraph.IsInduced, IsChordless, IsChord, Sym2.forall, Sym2.lift_mk, G.mem_edgeSet,
    mem_verts_toSubgraph, adj_toSubgraph_iff_mem_edges]
  grind only

namespace IsPath

/--
lemma `neighborSet_toSubgraph_startpoint` / 引理 `neighborSet_toSubgraph_startpoint`

English:
lemma neighborSet_toSubgraph_startpoint
  statement: {u v} {p : G.Walk u v}
  proof: by
  have hadj1 := p.toSubgraph_adj_snd hnp
  ext v
  simp_all only [Subgraph.mem_neighborSet, Set.mem_singleton_iff,
    SimpleGraph.Walk.toSubgraph_adj_iff, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
  grind [getVert_eq_start_iff]

中文:
引理 neighborSet_toSubgraph_startpoint
  结论: {u v} {p : G.途径 u v}
  证明: by
  have hadj1 := p.toSubgraph_adj_snd hnp
  ext v
  simp_all only [Subgraph.mem_neighborSet, Set.mem_singleton_iff,
    SimpleGraph.Walk.toSubgraph_adj_iff, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
  grind [getVert_eq_start_iff]

Depends on / 依赖: Prod.mk.injEq, Prod.swap_prod_mk, Set.mem_singleton_iff, SimpleGraph, SimpleGraph.Walk.toSubgraph_adj_iff, Subgraph, Subgraph.mem_neighborSet, Sym2.eq, Sym2.rel_iff, getVert_eq_start_iff, mem_neighborSet, mem_singleton_iff, p.toSubgraph_adj_snd, rel_iff, swap_prod_mk, toSubgraph_adj_iff, toSubgraph_adj_snd
-/
lemma neighborSet_toSubgraph_startpoint {u v} {p : G.Walk u v}
    (hp : p.IsPath) (hnp : ¬ p.Nil) : p.toSubgraph.neighborSet u = {p.snd} := by
  have hadj1 := p.toSubgraph_adj_snd hnp
  ext v
  simp_all only [Subgraph.mem_neighborSet, Set.mem_singleton_iff,
    SimpleGraph.Walk.toSubgraph_adj_iff, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
  grind [getVert_eq_start_iff]

/--
lemma `neighborSet_toSubgraph_endpoint` / 引理 `neighborSet_toSubgraph_endpoint`

English:
lemma neighborSet_toSubgraph_endpoint
  statement: {u v} {p : G.Walk u v}
  proof: by
  simpa using IsPath.neighborSet_toSubgraph_startpoint hp.reverse
      (by rw [Walk.not_nil_iff_lt_length, Walk.length_reverse]; exact
        Walk.not_nil_iff_lt_length.mp hnp)

中文:
引理 neighborSet_toSubgraph_endpoint
  结论: {u v} {p : G.途径 u v}
  证明: by
  simpa using IsPath.neighborSet_toSubgraph_startpoint hp.reverse
      (by rw [Walk.not_nil_iff_lt_length, Walk.length_reverse]; exact
        Walk.not_nil_iff_lt_length.mp hnp)

Depends on / 依赖: IsPath, IsPath.neighborSet_toSubgraph_startpoint, Walk.length_reverse, Walk.not_nil_iff_lt_length, Walk.not_nil_iff_lt_length.mp, hp.reverse, length_reverse, neighborSet_toSubgraph_startpoint, not_nil_iff_lt_length, reverse
-/
lemma neighborSet_toSubgraph_endpoint {u v} {p : G.Walk u v}
    (hp : p.IsPath) (hnp : ¬ p.Nil) : p.toSubgraph.neighborSet v = {p.penultimate} := by
  simpa using IsPath.neighborSet_toSubgraph_startpoint hp.reverse
      (by rw [Walk.not_nil_iff_lt_length, Walk.length_reverse]; exact
        Walk.not_nil_iff_lt_length.mp hnp)

/--
lemma `neighborSet_toSubgraph_internal` / 引理 `neighborSet_toSubgraph_internal`

English:
lemma neighborSet_toSubgraph_internal
  statement: {u} {i : Nat} {p : G.Walk u v} (hp : p.IsPath)
  proof: by
  have hadj1 := ((show i - 1 + 1 = i by lia) ▸
    p.toSubgraph_adj_getVert (by lia : (i - 1) < p.length)).symm
  ext v
  simp_all only [ne_eq, Subgraph.mem_neighborSet, Set.mem_insert_iff, Set.mem_singleton_iff,
    SimpleGraph.Walk.toSubgraph_adj_iff, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
    

中文:
引理 neighborSet_toSubgraph_internal
  结论: {u} {i : 自然数} {p : G.途径 u v} (hp : p.是道路)
  证明: by
  have hadj1 := ((show i - 1 + 1 = i by lia) ▸
    p.toSubgraph_adj_getVert (by lia : (i - 1) < p.length)).symm
  ext v
  simp_all only [ne_eq, Subgraph.mem_neighborSet, Set.mem_insert_iff, Set.mem_singleton_iff,
    SimpleGraph.Walk.toSubgraph_adj_iff, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
    

Depends on / 依赖: Prod.mk.injEq, Prod.swap_prod_mk, Set.mem_insert_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff, SimpleGraph, SimpleGraph.Walk.toSubgraph_adj_iff, Subgraph, Subgraph.mem_neighborSet, Sym2.eq, Sym2.rel_iff, getVert_injOn, hp.getVert_injOn, length, mem_insert_iff, mem_neighborSet, mem_ofPred_eq, mem_singleton_iff, ne_eq, p.length
-/
lemma neighborSet_toSubgraph_internal {u} {i : Nat} {p : G.Walk u v} (hp : p.IsPath)
    (h : i != 0) (h' : i < p.length) :
    p.toSubgraph.neighborSet (p.getVert i) = {p.getVert (i - 1), p.getVert (i + 1)} := by
  have hadj1 := ((show i - 1 + 1 = i by lia) ▸
    p.toSubgraph_adj_getVert (by lia : (i - 1) < p.length)).symm
  ext v
  simp_all only [ne_eq, Subgraph.mem_neighborSet, Set.mem_insert_iff, Set.mem_singleton_iff,
    SimpleGraph.Walk.toSubgraph_adj_iff, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
    Prod.swap_prod_mk]
  refine ⟨?_, by aesop⟩
  rintro ⟨i', ⟨hl, _⟩ | ⟨_, hl⟩⟩ <;>
    apply hp.getVert_injOn (by rw [Set.mem_ofPred_eq]; lia)
      (by rw [Set.mem_ofPred_eq]; lia) at hl <;> aesop

/--
lemma `ncard_neighborSet_toSubgraph_internal_eq_two` / 引理 `ncard_neighborSet_toSubgraph_internal_eq_two`

English:
lemma ncard_neighborSet_toSubgraph_internal_eq_two
  statement: {u} {i : Nat} {p : G.Walk u v} (hp : p.IsPath)
  proof: by
  rw [hp.neighborSet_toSubgraph_internal h h']
  have : p.getVert (i - 1) != p.getVert (i + 1) := by
    intro h
    have := hp.getVert_injOn (by rw [Set.mem_ofPred_eq]; lia) (by rw [Set.mem_ofPred_eq]; lia) h
    lia
  simp_all

中文:
引理 ncard_neighborSet_toSubgraph_internal_eq_two
  结论: {u} {i : 自然数} {p : G.途径 u v} (hp : p.是道路)
  证明: by
  rw [hp.neighborSet_toSubgraph_internal h h']
  have : p.getVert (i - 1) != p.getVert (i + 1) := by
    intro h
    have := hp.getVert_injOn (by rw [Set.mem_ofPred_eq]; lia) (by rw [Set.mem_ofPred_eq]; lia) h
    lia
  simp_all

Depends on / 依赖: Set.mem_ofPred_eq, getVert, getVert_injOn, hp.getVert_injOn, hp.neighborSet_toSubgraph_internal, mem_ofPred_eq, neighborSet_toSubgraph_internal, p.getVert
-/
lemma ncard_neighborSet_toSubgraph_internal_eq_two {u} {i : Nat} {p : G.Walk u v} (hp : p.IsPath)
    (h : i != 0) (h' : i < p.length) :
    (p.toSubgraph.neighborSet (p.getVert i)).ncard = 2 := by
  rw [hp.neighborSet_toSubgraph_internal h h']
  have : p.getVert (i - 1) != p.getVert (i + 1) := by
    intro h
    have := hp.getVert_injOn (by rw [Set.mem_ofPred_eq]; lia) (by rw [Set.mem_ofPred_eq]; lia) h
    lia
  simp_all

/--
lemma `snd_of_toSubgraph_adj` / 引理 `snd_of_toSubgraph_adj`

English:
lemma snd_of_toSubgraph_adj
  statement: {u v v'} {p : G.Walk u v} (hp : p.IsPath)
  proof: by
  have ⟨i, hi⟩ := p.toSubgraph_adj_iff.mp hadj
  simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at hi
  rcases hi.1 with ⟨hl1, rfl⟩ | ⟨hr1, hr2⟩
  · have : i = 0 := by
      apply hp.getVert_injOn (by rw [Set.mem_ofPred]; lia) (by rw [Set.mem_ofPred]; lia)
      rw [p.getVer

中文:
引理 snd_of_toSubgraph_adj
  结论: {u v v'} {p : G.途径 u v} (hp : p.是道路)
  证明: by
  have ⟨i, hi⟩ := p.toSubgraph_adj_iff.mp hadj
  simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at hi
  rcases hi.1 with ⟨hl1, rfl⟩ | ⟨hr1, hr2⟩
  · have : i = 0 := by
      apply hp.getVert_injOn (by rw [Set.mem_ofPred]; lia) (by rw [Set.mem_ofPred]; lia)
      rw [p.getVer

Depends on / 依赖: Prod.mk.injEq, Prod.swap_prod_mk, Set.mem_ofPred, Sym2.eq, Sym2.rel_iff, getVert_injOn, getVert_zero, hp.getVert_injOn, mem_ofPred, p.getVert_zero, p.toSubgraph_adj_iff.mp, rel_iff, swap_prod_mk, toSubgraph_adj_iff
-/
lemma snd_of_toSubgraph_adj {u v v'} {p : G.Walk u v} (hp : p.IsPath)
    (hadj : p.toSubgraph.Adj u v') : p.snd = v' := by
  have ⟨i, hi⟩ := p.toSubgraph_adj_iff.mp hadj
  simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at hi
  rcases hi.1 with ⟨hl1, rfl⟩ | ⟨hr1, hr2⟩
  · have : i = 0 := by
      apply hp.getVert_injOn (by rw [Set.mem_ofPred]; lia) (by rw [Set.mem_ofPred]; lia)
      rw [p.getVert_zero]; rw [hl1]
    simp [this]
  · have : i + 1 = 0 := by
      apply hp.getVert_injOn (by rw [Set.mem_ofPred]; lia) (by rw [Set.mem_ofPred]; lia)
      rw [p.getVert_zero]; rw [hr2]
    contradiction

end IsPath

namespace IsCycle

/--
lemma `neighborSet_toSubgraph_endpoint` / 引理 `neighborSet_toSubgraph_endpoint`

English:
lemma neighborSet_toSubgraph_endpoint
  given: {u} {p : G.Walk u u} (hpc : p.IsCycle)
  proof: by
  have hadj1 := p.toSubgraph_adj_snd hpc.not_nil
  ext v
  simp_all only [Subgraph.mem_neighborSet, Set.mem_insert_iff, Set.mem_singleton_iff,
    SimpleGraph.Walk.toSubgraph_adj_iff, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
  grind [getVert_endpoint_iff, add_tsub_cancel_right]

中文:
引理 neighborSet_toSubgraph_endpoint
  条件: {u} {p : G.途径 u u} (hpc : p.是环)
  证明: by
  have hadj1 := p.toSubgraph_adj_snd hpc.not_nil
  ext v
  simp_all only [Subgraph.mem_neighborSet, Set.mem_insert_iff, Set.mem_singleton_iff,
    SimpleGraph.Walk.toSubgraph_adj_iff, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
  grind [getVert_endpoint_iff, add_tsub_cancel_right]

Depends on / 依赖: Prod.mk.injEq, Prod.swap_prod_mk, Set.mem_insert_iff, Set.mem_singleton_iff, SimpleGraph, SimpleGraph.Walk.toSubgraph_adj_iff, Subgraph, Subgraph.mem_neighborSet, Sym2.eq, Sym2.rel_iff, add_tsub_cancel_right, getVert_endpoint_iff, hpc.not_nil, mem_insert_iff, mem_neighborSet, mem_singleton_iff, not_nil, p.toSubgraph_adj_snd, rel_iff, swap_prod_mk
-/
lemma neighborSet_toSubgraph_endpoint {u} {p : G.Walk u u} (hpc : p.IsCycle) :
    p.toSubgraph.neighborSet u = {p.snd, p.penultimate} := by
  have hadj1 := p.toSubgraph_adj_snd hpc.not_nil
  ext v
  simp_all only [Subgraph.mem_neighborSet, Set.mem_insert_iff, Set.mem_singleton_iff,
    SimpleGraph.Walk.toSubgraph_adj_iff, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
  grind [getVert_endpoint_iff, add_tsub_cancel_right]

/--
lemma `neighborSet_toSubgraph_internal` / 引理 `neighborSet_toSubgraph_internal`

English:
lemma neighborSet_toSubgraph_internal
  statement: {u} {i : Nat} {p : G.Walk u u} (hpc : p.IsCycle)
  proof: by
  have hadj1 := ((show i - 1 + 1 = i by lia) ▸
    p.toSubgraph_adj_getVert (by lia : (i - 1) < p.length)).symm
  ext v
  simp_all only [ne_eq, Subgraph.mem_neighborSet, Set.mem_insert_iff, Set.mem_singleton_iff,
    SimpleGraph.Walk.toSubgraph_adj_iff, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
    

中文:
引理 neighborSet_toSubgraph_internal
  结论: {u} {i : 自然数} {p : G.途径 u u} (hpc : p.是环)
  证明: by
  have hadj1 := ((show i - 1 + 1 = i by lia) ▸
    p.toSubgraph_adj_getVert (by lia : (i - 1) < p.length)).symm
  ext v
  simp_all only [ne_eq, Subgraph.mem_neighborSet, Set.mem_insert_iff, Set.mem_singleton_iff,
    SimpleGraph.Walk.toSubgraph_adj_iff, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
    

Depends on / 依赖: Prod.mk.injEq, Prod.swap_prod_mk, Set.mem_insert_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff, SimpleGraph, SimpleGraph.Walk.toSubgraph_adj_iff, Subgraph, Subgraph.mem_neighborSet, Sym2.eq, Sym2.rel_iff, getVert_injOn, hpc.getVert_injOn, length, mem_insert_iff, mem_neighborSet, mem_ofPred_eq, mem_singleton_iff, ne_eq, p.length
-/
lemma neighborSet_toSubgraph_internal {u} {i : Nat} {p : G.Walk u u} (hpc : p.IsCycle)
    (h : i != 0) (h' : i < p.length) :
    p.toSubgraph.neighborSet (p.getVert i) = {p.getVert (i - 1), p.getVert (i + 1)} := by
  have hadj1 := ((show i - 1 + 1 = i by lia) ▸
    p.toSubgraph_adj_getVert (by lia : (i - 1) < p.length)).symm
  ext v
  simp_all only [ne_eq, Subgraph.mem_neighborSet, Set.mem_insert_iff, Set.mem_singleton_iff,
    SimpleGraph.Walk.toSubgraph_adj_iff, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
    Prod.swap_prod_mk]
  refine ⟨?_, by aesop⟩
  rintro ⟨i', ⟨hl1, hl2⟩ | ⟨hr1, hr2⟩⟩
  · apply hpc.getVert_injOn' (by rw [Set.mem_ofPred_eq]; lia)
      (by rw [Set.mem_ofPred_eq]; lia) at hl1
    simp_all
  · apply hpc.getVert_injOn (by rw [Set.mem_ofPred_eq]; lia)
      (by rw [Set.mem_ofPred_eq]; lia) at hr2
    aesop

/--
lemma `ncard_neighborSet_toSubgraph_eq_two` / 引理 `ncard_neighborSet_toSubgraph_eq_two`

English:
lemma ncard_neighborSet_toSubgraph_eq_two
  statement: {u v} {p : G.Walk u u} (hpc : p.IsCycle)
  proof: by
  simp only [SimpleGraph.Walk.mem_support_iff_exists_getVert] at h ⊢
  obtain ⟨i, hi⟩ := h
  by_cases! he : i = 0 ∨ i = p.length
  · have huv : u = v := by aesop
    rw [← huv]; rw [hpc.neighborSet_toSubgraph_endpoint]
    exact Set.ncard_pair hpc.snd_ne_penultimate
  rw [← hi.1]; rw [hpc.neighbo

中文:
引理 ncard_neighborSet_toSubgraph_eq_two
  结论: {u v} {p : G.途径 u u} (hpc : p.是环)
  证明: by
  simp only [SimpleGraph.Walk.mem_support_iff_exists_getVert] at h ⊢
  obtain ⟨i, hi⟩ := h
  by_cases! he : i = 0 ∨ i = p.length
  · have huv : u = v := by aesop
    rw [← huv]; rw [hpc.neighborSet_toSubgraph_endpoint]
    exact Set.ncard_pair hpc.snd_ne_penultimate
  rw [← hi.1]; rw [hpc.neighbo

Depends on / 依赖: Set.ncard_pair, SimpleGraph, SimpleGraph.Walk.mem_support_iff_exists_getVert, getVert_sub_one_ne_getVert_add_one, hpc.getVert_sub_one_ne_getVert_add_one, hpc.neighborSet_toSubgraph_endpoint, hpc.neighborSet_toSubgraph_internal, hpc.snd_ne_penultimate, length, mem_support_iff_exists_getVert, ncard_pair, neighborSet_toSubgraph_endpoint, neighborSet_toSubgraph_internal, p.length, snd_ne_penultimate
-/
lemma ncard_neighborSet_toSubgraph_eq_two {u v} {p : G.Walk u u} (hpc : p.IsCycle)
    (h : v in p.support) : (p.toSubgraph.neighborSet v).ncard = 2 := by
  simp only [SimpleGraph.Walk.mem_support_iff_exists_getVert] at h ⊢
  obtain ⟨i, hi⟩ := h
  by_cases! he : i = 0 ∨ i = p.length
  · have huv : u = v := by aesop
    rw [← huv]; rw [hpc.neighborSet_toSubgraph_endpoint]
    exact Set.ncard_pair hpc.snd_ne_penultimate
  rw [← hi.1]; rw [hpc.neighborSet_toSubgraph_internal he.1 (by lia)]
  exact Set.ncard_pair (hpc.getVert_sub_one_ne_getVert_add_one (by lia))

/--
lemma `exists_isCycle_snd_verts_eq` / 引理 `exists_isCycle_snd_verts_eq`

English:
lemma exists_isCycle_snd_verts_eq
  given: {p : G.Walk v v} (h : p.IsCycle) (hadj : p.toSubgraph.Adj v w)
  proof: by
  have : w in p.toSubgraph.neighborSet v := hadj
  rw [h.neighborSet_toSubgraph_endpoint] at this
  push _ in _ at this
  obtain hl | hr := this
  · exact ⟨p, ⟨h, hl.symm, rfl⟩⟩
  · use p.reverse
    rw [penultimate]; rw [← getVert_reverse] at hr
    exact ⟨h.reverse, hr.symm, by rw [toSubgraph_r

中文:
引理 存在_isCycle_snd_verts_eq
  条件: {p : G.途径 v v} (h : p.是环) (hadj : p.toSubgraph.伴随 v w)
  证明: by
  have : w in p.toSubgraph.neighborSet v := hadj
  rw [h.neighborSet_toSubgraph_endpoint] at this
  push _ in _ at this
  obtain hl | hr := this
  · exact ⟨p, ⟨h, hl.symm, rfl⟩⟩
  · use p.reverse
    rw [penultimate]; rw [← getVert_reverse] at hr
    exact ⟨h.reverse, hr.symm, by rw [toSubgraph_r

Depends on / 依赖: getVert_reverse, h.neighborSet_toSubgraph_endpoint, h.reverse, hl.symm, hr.symm, neighborSet, neighborSet_toSubgraph_endpoint, p.reverse, p.toSubgraph.neighborSet, penultimate, reverse, toSubgraph, toSubgraph_reverse
-/
lemma exists_isCycle_snd_verts_eq {p : G.Walk v v} (h : p.IsCycle) (hadj : p.toSubgraph.Adj v w) :
    exists (p' : G.Walk v v), p'.IsCycle ∧ p'.snd = w ∧ p'.toSubgraph.verts = p.toSubgraph.verts := by
  have : w in p.toSubgraph.neighborSet v := hadj
  rw [h.neighborSet_toSubgraph_endpoint] at this
  push _ in _ at this
  obtain hl | hr := this
  · exact ⟨p, ⟨h, hl.symm, rfl⟩⟩
  · use p.reverse
    rw [penultimate]; rw [← getVert_reverse] at hr
    exact ⟨h.reverse, hr.symm, by rw [toSubgraph_reverse _]⟩

end IsCycle

open Finset

variable [DecidableEq V] {u v : V} {p : G.Walk u v}

/--
lemma `exists_mem_support_mem_erase_mem_support_takeUntil_eq_empty` / 引理 `exists_mem_support_mem_erase_mem_support_takeUntil_eq_empty`

English:
lemma exists_mem_support_mem_erase_mem_support_takeUntil_eq_empty
  statement: (s : Finset V)
  proof: by
  simp only [← Finset.subset_empty]
  induction hp : p.length + #s using Nat.strong_induction_on generalizing s v with | _ n ih
  simp only [Finset.Nonempty, mem_filter] at h
  obtain ⟨x, hxs, hx⟩ := h
  obtain h | h := Finset.eq_empty_or_nonempty {t in s.erase x | t in (p.takeUntil x hx).support

中文:
引理 存在_mem_support_mem_erase_mem_support_takeUntil_eq_empty
  结论: (s : 有限集 V)
  证明: by
  simp only [← Finset.subset_empty]
  induction hp : p.length + #s using Nat.strong_induction_on generalizing s v with | _ n ih
  simp only [Finset.Nonempty, mem_filter] at h
  obtain ⟨x, hxs, hx⟩ := h
  obtain h | h := Finset.eq_empty_or_nonempty {t in s.erase x | t in (p.takeUntil x hx).support

Depends on / 依赖: Finset, Finset.Nonempty, Finset.eq_empty_or_nonempty, Finset.subset_empty, Nat.strong_induction_on, Nonempty, card_erase_add_one, eq_empty_or_nonempty, generalizing, h.le, length, length_takeUntil_le_length, mem_filter, p.length, p.length_takeUntil_le_length, p.takeUntil, s.erase, strong_induction_on, subset_empty, support
-/
lemma exists_mem_support_mem_erase_mem_support_takeUntil_eq_empty (s : Finset V)
    (h : {x in s | x in p.support}.Nonempty) :
    exists x in s, exists hx : x in p.support, {t in s.erase x | t in (p.takeUntil x hx).support} = ∅ := by
  simp only [← Finset.subset_empty]
  induction hp : p.length + #s using Nat.strong_induction_on generalizing s v with | _ n ih
  simp only [Finset.Nonempty, mem_filter] at h
  obtain ⟨x, hxs, hx⟩ := h
  obtain h | h := Finset.eq_empty_or_nonempty {t in s.erase x | t in (p.takeUntil x hx).support}
  · use x, hxs, hx, h.le
  have : (p.takeUntil x hx).length + #(s.erase x) < n := by
    rw [← card_erase_add_one hxs] at hp
    have := p.length_takeUntil_le_length hx
    lia
  obtain ⟨y, hys, hyp, h⟩ := ih _ this (s.erase x) h rfl
  use y, mem_of_mem_erase hys, support_takeUntil_subset_support p hx hyp
  rwa [takeUntil_takeUntil, erase_right_comm, filter_erase, erase_eq_of_notMem] at h
  simp only [mem_filter, mem_erase, ne_eq, not_and, and_imp]
  rintro hxy -
  exact notMem_support_takeUntil_support_takeUntil_subset (Ne.symm hxy) hx hyp

/--
lemma `exists_mem_support_forall_mem_support_imp_eq` / 引理 `exists_mem_support_forall_mem_support_imp_eq`

English:
lemma exists_mem_support_forall_mem_support_imp_eq
  statement: (s : Finset V)
  proof: by
  obtain ⟨x, hxs, hx, h⟩ := p.exists_mem_support_mem_erase_mem_support_takeUntil_eq_empty s h
  use x, hxs, hx
  suffices {t in s | t in (p.takeUntil x hx).support} subseteq {x} by simpa [Finset.subset_iff] using this
  rwa [Finset.filter_erase, ← Finset.subset_empty, ← Finset.subset_insert_iff,


中文:
引理 存在_mem_support_对任意_mem_support_imp_eq
  结论: (s : 有限集 V)
  证明: by
  obtain ⟨x, hxs, hx, h⟩ := p.exists_mem_support_mem_erase_mem_support_takeUntil_eq_empty s h
  use x, hxs, hx
  suffices {t in s | t in (p.takeUntil x hx).support} subseteq {x} by simpa [Finset.subset_iff] using this
  rwa [Finset.filter_erase, ← Finset.subset_empty, ← Finset.subset_insert_iff,


Depends on / 依赖: Finset, Finset.filter_erase, Finset.subset_empty, Finset.subset_iff, Finset.subset_insert_iff, LawfulSingleton, LawfulSingleton.insert_empty_eq, exists_mem_support_mem_erase_mem_support_takeUntil_eq_empty, filter_erase, insert_empty_eq, p.exists_mem_support_mem_erase_mem_support_takeUntil_eq_empty, p.takeUntil, subset_empty, subset_iff, subset_insert_iff, subseteq, support, takeUntil
-/
lemma exists_mem_support_forall_mem_support_imp_eq (s : Finset V)
    (h : {x in s | x in p.support}.Nonempty) :
    exists x in s, exists (hx : x in p.support),
      forall t in s, t in (p.takeUntil x hx).support -> t = x := by
  obtain ⟨x, hxs, hx, h⟩ := p.exists_mem_support_mem_erase_mem_support_takeUntil_eq_empty s h
  use x, hxs, hx
  suffices {t in s | t in (p.takeUntil x hx).support} subseteq {x} by simpa [Finset.subset_iff] using this
  rwa [Finset.filter_erase, ← Finset.subset_empty, ← Finset.subset_insert_iff,
    LawfulSingleton.insert_empty_eq] at h

end Walk

namespace Subgraph

/--
lemma `_root_.SimpleGraph.Walk.toSubgraph_connected` / 引理 `_root_.SimpleGraph.Walk.toSubgraph_connected`

English:
lemma _root_.SimpleGraph.Walk.toSubgraph_connected
  given: {u v : V} (p : G.Walk u v)
  proof: by
  induction p with
  | nil => apply singletonSubgraph_connected
  | @cons _ w _ h p ih =>
    apply Subgraph.connected_sup (subgraphOfAdj_connected h).preconnected ih.preconnected
    exists w
    simp

中文:
引理 _root_.简单图.途径.toSubgraph_connected
  条件: {u v : V} (p : G.途径 u v)
  证明: by
  induction p with
  | nil => apply singletonSubgraph_connected
  | @cons _ w _ h p ih =>
    apply Subgraph.connected_sup (subgraphOfAdj_connected h).preconnected ih.preconnected
    exists w
    simp

Depends on / 依赖: Subgraph, Subgraph.connected_sup, connected_sup, ih.preconnected, preconnected, singletonSubgraph_connected, subgraphOfAdj_connected
-/
lemma _root_.SimpleGraph.Walk.toSubgraph_connected {u v : V} (p : G.Walk u v) :
    p.toSubgraph.Connected := by
  induction p with
  | nil => apply singletonSubgraph_connected
  | @cons _ w _ h p ih =>
    apply Subgraph.connected_sup (subgraphOfAdj_connected h).preconnected ih.preconnected
    exists w
    simp

/--
lemma `induce_union_connected` / 引理 `induce_union_connected`

English:
lemma induce_union_connected
  statement: {H : G.Subgraph} {s t : Set V}
  proof: (Subgraph.connected_sup sconn tconn sintert).mono le_induce_union by simp

中文:
引理 induce_union_connected
  结论: {H : G.子图} {s t : 集合 V}
  证明: (Subgraph.connected_sup sconn tconn sintert).mono le_induce_union by simp

Depends on / 依赖: Subgraph, Subgraph.connected_sup, connected_sup, le_induce_union, sintert
-/
lemma induce_union_connected {H : G.Subgraph} {s t : Set V}
    (sconn : (H.induce s).Preconnected) (tconn : (H.induce t).Preconnected)
    (sintert : (s ⊓ t).Nonempty) :
    (H.induce (s union t)).Connected :=
(Subgraph.connected_sup sconn tconn sintert).mono le_induce_union by simp

/--
lemma `connected_induce_top_sup` / 引理 `connected_induce_top_sup`

English:
lemma connected_induce_top_sup
  statement: {H K : G.Subgraph} (Hconn : H.Preconnected) (Kconn : K.Preconnected)
  proof: by
  refine Subgraph.connected_sup (Subgraph.connected_sup ?_ Hconn ?_).preconnected Kconn ?_
  · exact (top_induce_pair_connected_of_adj huv).preconnected
  · exact ⟨u, by simp [uH]⟩
  · exact ⟨v, by simp [vK]⟩

中文:
引理 connected_induce_top_sup
  结论: {H K : G.子图} (Hconn : H.预连通) (Kconn : K.预连通)
  证明: by
  refine Subgraph.connected_sup (Subgraph.connected_sup ?_ Hconn ?_).preconnected Kconn ?_
  · exact (top_induce_pair_connected_of_adj huv).preconnected
  · exact ⟨u, by simp [uH]⟩
  · exact ⟨v, by simp [vK]⟩

Depends on / 依赖: Subgraph, Subgraph.connected_sup, connected_sup, preconnected, top_induce_pair_connected_of_adj
-/
lemma connected_induce_top_sup {H K : G.Subgraph} (Hconn : H.Preconnected) (Kconn : K.Preconnected)
    {u v : V} (uH : u in H.verts) (vK : v in K.verts) (huv : G.Adj u v) :
    ((⊤ : G.Subgraph).induce {u, v} ⊔ H ⊔ K).Connected := by
  refine Subgraph.connected_sup (Subgraph.connected_sup ?_ Hconn ?_).preconnected Kconn ?_
  · exact (top_induce_pair_connected_of_adj huv).preconnected
  · exact ⟨u, by simp [uH]⟩
  · exact ⟨v, by simp [vK]⟩

set_option backward.isDefEq.respectTransparency false in
/--
lemma `preconnected_iff_forall_exists_walk_subgraph` / 引理 `preconnected_iff_forall_exists_walk_subgraph`

English:
lemma preconnected_iff_forall_exists_walk_subgraph
  given: (H : G.Subgraph)
  proof: by
  constructor
  · intro hc u v hu hv
    refine (hc ⟨_, hu⟩ ⟨_, hv⟩).elim fun p => ?_
    exists p.map (Subgraph.hom _)
    simp [coeSubgraph_le]
  · intro hw
    rw [Subgraph.preconnected_iff]
    rintro ⟨u, hu⟩ ⟨v, hv⟩
    obtain ⟨p, h⟩ := hw hu hv
    exact Reachable.map (Subgraph.inclusion h)

中文:
引理 preconnected_iff_对任意_存在_walk_subgraph
  条件: (H : G.子图)
  证明: by
  constructor
  · intro hc u v hu hv
    refine (hc ⟨_, hu⟩ ⟨_, hv⟩).elim fun p => ?_
    exists p.map (Subgraph.hom _)
    simp [coeSubgraph_le]
  · intro hw
    rw [Subgraph.preconnected_iff]
    rintro ⟨u, hu⟩ ⟨v, hv⟩
    obtain ⟨p, h⟩ := hw hu hv
    exact Reachable.map (Subgraph.inclusion h)

Depends on / 依赖: Reachable, Reachable.map, Subgraph, Subgraph.hom, Subgraph.inclusion, Subgraph.preconnected_iff, coeSubgraph_le, end_mem_verts_toSubgraph, inclusion, p.end_mem_verts_toSubgraph, p.map, p.start_mem_verts_toSubgraph, p.toSubgraph_connected, preconnected_iff, start_mem_verts_toSubgraph, toSubgraph_connected
-/
lemma preconnected_iff_forall_exists_walk_subgraph (H : G.Subgraph) :
    H.Preconnected ↔ forall {u v}, u in H.verts -> v in H.verts -> exists p : G.Walk u v, p.toSubgraph <= H := by
  constructor
  · intro hc u v hu hv
    refine (hc ⟨_, hu⟩ ⟨_, hv⟩).elim fun p => ?_
    exists p.map (Subgraph.hom _)
    simp [coeSubgraph_le]
  · intro hw
    rw [Subgraph.preconnected_iff]
    rintro ⟨u, hu⟩ ⟨v, hv⟩
    obtain ⟨p, h⟩ := hw hu hv
    exact Reachable.map (Subgraph.inclusion h)
      (p.toSubgraph_connected ⟨_, p.start_mem_verts_toSubgraph⟩ ⟨_, p.end_mem_verts_toSubgraph⟩)

/--
lemma `connected_iff_forall_exists_walk_subgraph` / 引理 `connected_iff_forall_exists_walk_subgraph`

English:
lemma connected_iff_forall_exists_walk_subgraph
  given: (H : G.Subgraph)
  proof: by
  rw [H.connected_iff]; rw [preconnected_iff_forall_exists_walk_subgraph]; rw [and_comm]

中文:
引理 connected_iff_对任意_存在_walk_subgraph
  条件: (H : G.子图)
  证明: by
  rw [H.connected_iff]; rw [preconnected_iff_forall_exists_walk_subgraph]; rw [and_comm]

Depends on / 依赖: H.connected_iff, and_comm, connected_iff, preconnected_iff_forall_exists_walk_subgraph
-/
lemma connected_iff_forall_exists_walk_subgraph (H : G.Subgraph) :
    H.Connected ↔
      H.verts.Nonempty ∧
        forall {u v}, u in H.verts -> v in H.verts -> exists p : G.Walk u v, p.toSubgraph <= H := by
  rw [H.connected_iff]; rw [preconnected_iff_forall_exists_walk_subgraph]; rw [and_comm]

end Subgraph

section induced_subgraphs

set_option backward.isDefEq.respectTransparency false in
/--
lemma `preconnected_induce_iff` / 引理 `preconnected_induce_iff`

English:
lemma preconnected_induce_iff
  given: {s : Set V}
  proof: by
  rw [induce_eq_coe_induce_top]; rw [← Subgraph.preconnected_iff]

中文:
引理 preconnected_induce_iff
  条件: {s : 集合 V}
  证明: by
  rw [induce_eq_coe_induce_top]; rw [← Subgraph.preconnected_iff]

Depends on / 依赖: Subgraph, Subgraph.preconnected_iff, induce_eq_coe_induce_top, preconnected_iff
-/
lemma preconnected_induce_iff {s : Set V} :
    (G.induce s).Preconnected ↔ ((⊤ : G.Subgraph).induce s).Preconnected := by
  rw [induce_eq_coe_induce_top]; rw [← Subgraph.preconnected_iff]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `connected_induce_iff` / 引理 `connected_induce_iff`

English:
lemma connected_induce_iff
  given: {s : Set V}
  proof: by
  rw [induce_eq_coe_induce_top]; rw [← Subgraph.connected_iff']

中文:
引理 connected_induce_iff
  条件: {s : 集合 V}
  证明: by
  rw [induce_eq_coe_induce_top]; rw [← Subgraph.connected_iff']

Depends on / 依赖: Subgraph, Subgraph.connected_iff, connected_iff, induce_eq_coe_induce_top
-/
lemma connected_induce_iff {s : Set V} :
    (G.induce s).Connected ↔ ((⊤ : G.Subgraph).induce s).Connected := by
  rw [induce_eq_coe_induce_top]; rw [← Subgraph.connected_iff']

/--
lemma `induce_union_connected` / 引理 `induce_union_connected`

English:
lemma induce_union_connected
  statement: {s t : Set V}
  proof: by
  rw [connected_induce_iff]
  rw [preconnected_induce_iff] at sconn tconn
  exact Subgraph.induce_union_connected sconn tconn sintert

中文:
引理 induce_union_connected
  结论: {s t : 集合 V}
  证明: by
  rw [connected_induce_iff]
  rw [preconnected_induce_iff] at sconn tconn
  exact Subgraph.induce_union_connected sconn tconn sintert

Depends on / 依赖: Subgraph, Subgraph.induce_union_connected, connected_induce_iff, induce_union_connected, preconnected_induce_iff, sintert
-/
lemma induce_union_connected {s t : Set V}
    (sconn : (G.induce s).Preconnected) (tconn : (G.induce t).Preconnected)
    (sintert : (s inter t).Nonempty) :
    (G.induce (s union t)).Connected := by
  rw [connected_induce_iff]
  rw [preconnected_induce_iff] at sconn tconn
  exact Subgraph.induce_union_connected sconn tconn sintert

/--
lemma `induce_pair_connected_of_adj` / 引理 `induce_pair_connected_of_adj`

English:
lemma induce_pair_connected_of_adj
  given: {u v : V} (huv : G.Adj u v)
  proof: by
  rw [connected_induce_iff]
  exact Subgraph.top_induce_pair_connected_of_adj huv

中文:
引理 induce_pair_connected_of_adj
  条件: {u v : V} (huv : G.伴随 u v)
  证明: by
  rw [connected_induce_iff]
  exact Subgraph.top_induce_pair_connected_of_adj huv

Depends on / 依赖: Subgraph, Subgraph.top_induce_pair_connected_of_adj, connected_induce_iff, top_induce_pair_connected_of_adj
-/
lemma induce_pair_connected_of_adj {u v : V} (huv : G.Adj u v) :
    (G.induce {u, v}).Connected := by
  rw [connected_induce_iff]
  exact Subgraph.top_induce_pair_connected_of_adj huv

/--
lemma `Subgraph.Connected.induce_verts` / 引理 `Subgraph.Connected.induce_verts`

English:
lemma Subgraph.Connected.induce_verts
  given: {H : G.Subgraph} (h : H.Connected)
  proof: by
  rw [connected_induce_iff]
  exact h.mono le_induce_top_verts (by exact rfl)

中文:
引理 子图.连通.induce_verts
  条件: {H : G.子图} (h : H.连通)
  证明: by
  rw [connected_induce_iff]
  exact h.mono le_induce_top_verts (by exact rfl)

Depends on / 依赖: connected_induce_iff, h.mono, le_induce_top_verts
-/
lemma Subgraph.Connected.induce_verts {H : G.Subgraph} (h : H.Connected) :
    (G.induce H.verts).Connected := by
  rw [connected_induce_iff]
  exact h.mono le_induce_top_verts (by exact rfl)

/--
lemma `Walk.connected_induce_support` / 引理 `Walk.connected_induce_support`

English:
lemma Walk.connected_induce_support
  given: {u v : V} (p : G.Walk u v)
  proof: by
  rw [← p.verts_toSubgraph]
  exact p.toSubgraph_connected.induce_verts

中文:
引理 途径.connected_induce_support
  条件: {u v : V} (p : G.途径 u v)
  证明: by
  rw [← p.verts_toSubgraph]
  exact p.toSubgraph_connected.induce_verts

Depends on / 依赖: induce_verts, p.toSubgraph_connected.induce_verts, p.verts_toSubgraph, toSubgraph_connected, verts_toSubgraph
-/
lemma Walk.connected_induce_support {u v : V} (p : G.Walk u v) :
    (G.induce {v | v in p.support}).Connected := by
  rw [← p.verts_toSubgraph]
  exact p.toSubgraph_connected.induce_verts

/--
lemma `connected_induce_union` / 引理 `connected_induce_union`

English:
lemma connected_induce_union
  statement: {v w : V} {s t : Set V}
  proof: by
  rw [connected_induce_iff]
  rw [preconnected_induce_iff] at sconn tconn
  apply (Subgraph.connected_induce_top_sup sconn tconn hv hw ha).mono
  · simp only [sup_le_iff, Subgraph.le_induce_union_left,
      Subgraph.le_induce_union_right, and_true, ← Subgraph.subgraphOfAdj_eq_induce ha]
    appl

中文:
引理 connected_induce_union
  结论: {v w : V} {s t : 集合 V}
  证明: by
  rw [connected_induce_iff]
  rw [preconnected_induce_iff] at sconn tconn
  apply (Subgraph.connected_induce_top_sup sconn tconn hv hw ha).mono
  · simp only [sup_le_iff, Subgraph.le_induce_union_left,
      Subgraph.le_induce_union_right, and_true, ← Subgraph.subgraphOfAdj_eq_induce ha]
    appl

Depends on / 依赖: Set.insert_subset_iff, Set.singleton_subset_iff, Set.union_assoc, Subgraph, Subgraph.connected_induce_top_sup, Subgraph.induce_verts, Subgraph.le_induce_union_left, Subgraph.le_induce_union_right, Subgraph.subgraphOfAdj_eq_induce, Subgraph.verts_sup, and_true, connected_induce_iff, connected_induce_top_sup, induce_verts, insert_subset_iff, le_induce_union_left, le_induce_union_right, preconnected_induce_iff, singleton_subset_iff, subgraphOfAdj_eq_induce
-/
lemma connected_induce_union {v w : V} {s t : Set V}
    (sconn : (G.induce s).Preconnected) (tconn : (G.induce t).Preconnected)
    (hv : v in s) (hw : w in t) (ha : G.Adj v w) :
    (G.induce (s union t)).Connected := by
  rw [connected_induce_iff]
  rw [preconnected_induce_iff] at sconn tconn
  apply (Subgraph.connected_induce_top_sup sconn tconn hv hw ha).mono
  · simp only [sup_le_iff, Subgraph.le_induce_union_left,
      Subgraph.le_induce_union_right, and_true, ← Subgraph.subgraphOfAdj_eq_induce ha]
    apply subgraphOfAdj_le_of_adj
    simp [hv, hw, ha]
  · simp only [Subgraph.verts_sup, Subgraph.induce_verts]
    rw [Set.union_assoc]
    simp [Set.insert_subset_iff, Set.singleton_subset_iff, hv, hw]

/--
lemma `induce_connected_of_patches` / 引理 `induce_connected_of_patches`

English:
lemma induce_connected_of_patches
  statement: {s : Set V} (u : V) (hu : u in s)
  proof: by
  rw [connected_iff_exists_forall_reachable]
  refine ⟨⟨u, hu⟩, ?_⟩
  rintro ⟨v, hv⟩
  obtain ⟨sv, svs, hu', hv', uv⟩ := patches hv
  exact uv.map (induceHomOfLE _ svs).toHom

中文:
引理 induce_connected_of_patches
  结论: {s : 集合 V} (u : V) (hu : u in s)
  证明: by
  rw [connected_iff_exists_forall_reachable]
  refine ⟨⟨u, hu⟩, ?_⟩
  rintro ⟨v, hv⟩
  obtain ⟨sv, svs, hu', hv', uv⟩ := patches hv
  exact uv.map (induceHomOfLE _ svs).toHom

Depends on / 依赖: connected_iff_exists_forall_reachable, induceHomOfLE, patches, uv.map
-/
lemma induce_connected_of_patches {s : Set V} (u : V) (hu : u in s)
    (patches : forall {v}, v in s -> exists s' subseteq s, exists (hu' : u in s') (hv' : v in s'),
                  (G.induce s').Reachable ⟨u, hu'⟩ ⟨v, hv'⟩) : (G.induce s).Connected := by
  rw [connected_iff_exists_forall_reachable]
  refine ⟨⟨u, hu⟩, ?_⟩
  rintro ⟨v, hv⟩
  obtain ⟨sv, svs, hu', hv', uv⟩ := patches hv
  exact uv.map (induceHomOfLE _ svs).toHom

/--
lemma `induce_sUnion_connected_of_pairwise_not_disjoint` / 引理 `induce_sUnion_connected_of_pairwise_not_disjoint`

English:
lemma induce_sUnion_connected_of_pairwise_not_disjoint
  statement: {S : Set (Set V)} (Sn : S.Nonempty)
  proof: by
  obtain ⟨s, sS⟩ := Sn
  obtain ⟨v, vs⟩ := (Sc sS).nonempty
  apply G.induce_connected_of_patches _ (Set.subset_sUnion_of_mem sS vs)
  rintro w hw
  simp only [Set.mem_sUnion] at hw
  obtain ⟨t, tS, wt⟩ := hw
  refine ⟨s union t, Set.union_subset (Set.subset_sUnion_of_mem sS) (Set.subset_sUnion_o

中文:
引理 induce_sUnion_connected_of_pairwise_not_disjoint
  结论: {S : 集合 (集合 V)} (Sn : S.非空)
  证明: by
  obtain ⟨s, sS⟩ := Sn
  obtain ⟨v, vs⟩ := (Sc sS).nonempty
  apply G.induce_connected_of_patches _ (Set.subset_sUnion_of_mem sS vs)
  rintro w hw
  simp only [Set.mem_sUnion] at hw
  obtain ⟨t, tS, wt⟩ := hw
  refine ⟨s union t, Set.union_subset (Set.subset_sUnion_of_mem sS) (Set.subset_sUnion_o

Depends on / 依赖: G.induce_connected_of_patches, Or.inl, Or.inr, Set.mem_sUnion, Set.subset_sUnion_of_mem, Set.union_subset, induce_connected_of_patches, induce_union_connected, mem_sUnion, nonempty, preconnected, subset_sUnion_of_mem, union_subset
-/
lemma induce_sUnion_connected_of_pairwise_not_disjoint {S : Set (Set V)} (Sn : S.Nonempty)
    (Snd : forall {s t}, s in S -> t in S -> (s inter t).Nonempty)
    (Sc : forall {s}, s in S -> (G.induce s).Connected) :
    (G.induce (⋃₀ S)).Connected := by
  obtain ⟨s, sS⟩ := Sn
  obtain ⟨v, vs⟩ := (Sc sS).nonempty
  apply G.induce_connected_of_patches _ (Set.subset_sUnion_of_mem sS vs)
  rintro w hw
  simp only [Set.mem_sUnion] at hw
  obtain ⟨t, tS, wt⟩ := hw
  refine ⟨s union t, Set.union_subset (Set.subset_sUnion_of_mem sS) (Set.subset_sUnion_of_mem tS),
          Or.inl vs, Or.inr wt,
          induce_union_connected (Sc sS).preconnected (Sc tS).preconnected (Snd sS tS) _ _⟩

/--
lemma `extend_finset_to_connected` / 引理 `extend_finset_to_connected`

English:
lemma extend_finset_to_connected
  given: (Gpc : G.Preconnected) {t : Finset V} (tn : t.Nonempty)
  proof: by
  classical
  obtain ⟨u, ut⟩ := tn
  refine ⟨t.biUnion (fun v => (Gpc u v).some.support.toFinset), fun v vt => ?_, ?_⟩
  · simp only [Finset.mem_biUnion, List.mem_toFinset]
    exact ⟨v, vt, Walk.end_mem_support _⟩
  · apply G.induce_connected_of_patches u
    · simp only [Finset.coe_biUnion, Fin

中文:
引理 extend_finset_to_connected
  条件: (Gpc : G.预连通) {t : 有限集 V} (tn : t.非空)
  证明: by
  classical
  obtain ⟨u, ut⟩ := tn
  refine ⟨t.biUnion (fun v => (Gpc u v).some.support.toFinset), fun v vt => ?_, ?_⟩
  · simp only [Finset.mem_biUnion, List.mem_toFinset]
    exact ⟨v, vt, Walk.end_mem_support _⟩
  · apply G.induce_connected_of_patches u
    · simp only [Finset.coe_biUnion, Fin

Depends on / 依赖: Finset, Finset.coe_biUnion, Finset.mem_biUnion, Finset.mem_coe, G.induce_connected_of_patches, List.coe_toFinset, List.mem_toFinset, Set.mem_iUnion, Set.mem_ofPred_eq, Walk.end_mem_support, Walk.start_mem_support, and_true, biUnion, classical, coe_biUnion, coe_toFinset, end_mem_support, exists_prop, induce_connected_of_patches, mem_biUnion
-/
lemma extend_finset_to_connected (Gpc : G.Preconnected) {t : Finset V} (tn : t.Nonempty) :
    exists (t' : Finset V), t subseteq t' ∧ (G.induce (t' : Set V)).Connected := by
  classical
  obtain ⟨u, ut⟩ := tn
  refine ⟨t.biUnion (fun v => (Gpc u v).some.support.toFinset), fun v vt => ?_, ?_⟩
  · simp only [Finset.mem_biUnion, List.mem_toFinset]
    exact ⟨v, vt, Walk.end_mem_support _⟩
  · apply G.induce_connected_of_patches u
    · simp only [Finset.coe_biUnion, Finset.mem_coe, List.coe_toFinset, Set.mem_iUnion,
                 Set.mem_ofPred_eq, Walk.start_mem_support, exists_prop, and_true]
      exact ⟨u, ut⟩
    intro v hv
    simp only [Finset.mem_coe, Finset.mem_biUnion, List.mem_toFinset] at hv
    obtain ⟨w, wt, hw⟩ := hv
    refine ⟨{x | x in (Gpc u w).some.support}, ?_, ?_⟩
    · simp only [Finset.coe_biUnion, Finset.mem_coe, List.coe_toFinset]
      exact fun x xw => Set.mem_iUnion₂.mpr ⟨w, wt, xw⟩
    · simp only [Set.mem_ofPred_eq, Walk.start_mem_support, exists_true_left]
      refine ⟨hw, Walk.connected_induce_support _ _ _⟩

end induced_subgraphs

/--
lemma `Reachable.coe_toSubgraph` / 引理 `Reachable.coe_toSubgraph`

English:
lemma Reachable.coe_toSubgraph
  statement: {H : SimpleGraph V} {u v : V} (h : H <= G)
  proof: hreachable.map ⟨((toSubgraph H h).vert · _), (·)⟩

中文:
引理 Reachable.coe_toSubgraph
  结论: {H : 简单图 V} {u v : V} (h : H <= G)
  证明: hreachable.map ⟨((toSubgraph H h).vert · _), (·)⟩
-/
protected lemma Reachable.coe_toSubgraph {H : SimpleGraph V} {u v : V} (h : H <= G)
    (hreachable : H.Reachable u v) :
    (toSubgraph H h).coe.Reachable ⟨u, trivial⟩ ⟨v, trivial⟩ :=
  hreachable.map ⟨((toSubgraph H h).vert · _), (·)⟩

/--
lemma `Preconnected.toSubgraph` / 引理 `Preconnected.toSubgraph`

English:
lemma Preconnected.toSubgraph
  statement: {H : SimpleGraph V} (h : H <= G)
  proof: Subgraph.preconnected_iff.mpr (fun u v => (hpreconn u v).coe_toSubgraph h)

中文:
引理 预连通.toSubgraph
  结论: {H : 简单图 V} (h : H <= G)
  证明: Subgraph.preconnected_iff.mpr (fun u v => (hpreconn u v).coe_toSubgraph h)
-/
protected lemma Preconnected.toSubgraph {H : SimpleGraph V} (h : H <= G)
    (hpreconn : H.Preconnected) : (toSubgraph H h).Preconnected :=
  Subgraph.preconnected_iff.mpr (fun u v => (hpreconn u v).coe_toSubgraph h)

/--
lemma `Connected.toSubgraph` / 引理 `Connected.toSubgraph`

English:
lemma Connected.toSubgraph
  given: {H : SimpleGraph V} (h : H <= G) (hconn : H.Connected)
  proof: Subgraph.connected_iff.mpr ⟨hconn.preconnected.toSubgraph h, by simp [hconn.nonempty]⟩

中文:
引理 连通.toSubgraph
  条件: {H : 简单图 V} (h : H <= G) (hconn : H.连通)
  证明: Subgraph.connected_iff.mpr ⟨hconn.preconnected.toSubgraph h, by simp [hconn.nonempty]⟩
-/
protected lemma Connected.toSubgraph {H : SimpleGraph V} (h : H <= G) (hconn : H.Connected) :
    (toSubgraph H h).Connected :=
  Subgraph.connected_iff.mpr ⟨hconn.preconnected.toSubgraph h, by simp [hconn.nonempty]⟩

/--
lemma `Reachable.coe_subgraphMap` / 引理 `Reachable.coe_subgraphMap`

English:
lemma Reachable.coe_subgraphMap
  statement: {G' : G.Subgraph} {G'' : G'.coe.Subgraph}
  proof: hreachable.map {
    toFun v := (G''.map f).vert _ (Set.mem_image_of_mem f v.prop)
    map_rel' r := Relation.map_apply.mpr (by tauto)
  }

中文:
引理 Reachable.coe_subgraphMap
  结论: {G' : G.子图} {G'' : G'.coe.子图}
  证明: hreachable.map {
    toFun v := (G''.map f).vert _ (Set.mem_image_of_mem f v.prop)
    map_rel' r := Relation.map_apply.mpr (by tauto)
  }
-/
protected lemma Reachable.coe_subgraphMap {G' : G.Subgraph} {G'' : G'.coe.Subgraph}
    (f : G'.coe ->g G) {u v : G''.verts} (hreachable : G''.coe.Reachable u v) :
    (G''.map f).coe.Reachable ⟨f u, Set.mem_image_of_mem _ u.prop⟩
      ⟨f v, Set.mem_image_of_mem _ v.prop⟩ :=
  hreachable.map {
    toFun v := (G''.map f).vert _ (Set.mem_image_of_mem f v.prop)
    map_rel' r := Relation.map_apply.mpr (by tauto)
  }

/--
lemma `Reachable.coe_coeSubgraph` / 引理 `Reachable.coe_coeSubgraph`

English:
lemma Reachable.coe_coeSubgraph
  statement: {G' : G.Subgraph} (G'' : G'.coe.Subgraph)
  proof: hreachable.coe_subgraphMap G'.hom

中文:
引理 Reachable.coe_coeSubgraph
  结论: {G' : G.子图} (G'' : G'.coe.子图)
  证明: hreachable.coe_subgraphMap G'.hom
-/
protected lemma Reachable.coe_coeSubgraph {G' : G.Subgraph} (G'' : G'.coe.Subgraph)
    {u v : G''.verts} (hreachable : G''.coe.Reachable u v) :
    (Subgraph.coeSubgraph G'').coe.Reachable (Subgraph.vert _ u (by simp_all))
      (Subgraph.vert _ v (by simp_all)) :=
  hreachable.coe_subgraphMap G'.hom

namespace Subgraph

/--
lemma `Preconnected.map` / 引理 `Preconnected.map`

English:
lemma Preconnected.map
  statement: {G' : G.Subgraph} {G'' : G'.coe.Subgraph}
  proof: by
  rw [Subgraph.preconnected_iff]
  intro ⟨u', u, hu, hfu⟩ ⟨v', v, hv, hfv⟩
  simp_rw [← hfu, ← hfv]
  exact (hpreconn.coe ⟨u, hu⟩ ⟨v, hv⟩).coe_subgraphMap f

中文:
引理 预连通.map
  结论: {G' : G.子图} {G'' : G'.coe.子图}
  证明: by
  rw [Subgraph.preconnected_iff]
  intro ⟨u', u, hu, hfu⟩ ⟨v', v, hv, hfv⟩
  simp_rw [← hfu, ← hfv]
  exact (hpreconn.coe ⟨u, hu⟩ ⟨v, hv⟩).coe_subgraphMap f
-/
protected lemma Preconnected.map {G' : G.Subgraph} {G'' : G'.coe.Subgraph}
    (f : G'.coe ->g G) (hpreconn : G''.Preconnected) : (G''.map f).Preconnected := by
  rw [Subgraph.preconnected_iff]
  intro ⟨u', u, hu, hfu⟩ ⟨v', v, hv, hfv⟩
  simp_rw [← hfu, ← hfv]
  exact (hpreconn.coe ⟨u, hu⟩ ⟨v, hv⟩).coe_subgraphMap f

/--
lemma `Connected.map` / 引理 `Connected.map`

English:
lemma Connected.map
  statement: {G' : G.Subgraph} {G'' : G'.coe.Subgraph}
  proof: Subgraph.connected_iff.mpr ⟨hconn.preconnected.map f, by simp [hconn.nonempty]⟩

中文:
引理 连通.map
  结论: {G' : G.子图} {G'' : G'.coe.子图}
  证明: Subgraph.connected_iff.mpr ⟨hconn.preconnected.map f, by simp [hconn.nonempty]⟩
-/
protected lemma Connected.map {G' : G.Subgraph} {G'' : G'.coe.Subgraph}
    (f : G'.coe ->g G) (hconn : G''.Connected) : (G''.map f).Connected :=
  Subgraph.connected_iff.mpr ⟨hconn.preconnected.map f, by simp [hconn.nonempty]⟩

/--
lemma `Preconnected.coeSubgraph` / 引理 `Preconnected.coeSubgraph`

English:
lemma Preconnected.coeSubgraph
  statement: {G' : G.Subgraph} (G'' : G'.coe.Subgraph)
  proof: hpreconn.map G'.hom

中文:
引理 预连通.coeSubgraph
  结论: {G' : G.子图} (G'' : G'.coe.子图)
  证明: hpreconn.map G'.hom
-/
protected lemma Preconnected.coeSubgraph {G' : G.Subgraph} (G'' : G'.coe.Subgraph)
    (hpreconn : G''.Preconnected) : (Subgraph.coeSubgraph G'').Preconnected :=
  hpreconn.map G'.hom

/--
lemma `Connected.coeSubgraph` / 引理 `Connected.coeSubgraph`

English:
lemma Connected.coeSubgraph
  statement: {G' : G.Subgraph} (G'' : G'.coe.Subgraph)
  proof: hconn.map G'.hom

中文:
引理 连通.coeSubgraph
  结论: {G' : G.子图} (G'' : G'.coe.子图)
  证明: hconn.map G'.hom
-/
protected lemma Connected.coeSubgraph {G' : G.Subgraph} (G'' : G'.coe.Subgraph)
    (hconn : G''.Connected) : (Subgraph.coeSubgraph G'').Connected :=
  hconn.map G'.hom

end Subgraph

end SimpleGraph
