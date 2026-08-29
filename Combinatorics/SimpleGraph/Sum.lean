/-
Copyright (c) 2022 Iván Renison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iván Renison
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Disjoint sum of graphs

This file defines the disjoint sum of graphs. The disjoint sum of `G : SimpleGraph V` and
`H : SimpleGraph W` is a graph on `V ⊕ W` where `u` and `v` are adjacent if and only if they are
both in `G` and adjacent in `G`, or they are both in `H` and adjacent in `H`.

## Main declarations

* `SimpleGraph.Sum`: The disjoint sum of graphs.

## Notation

* `G ⊕g H`: The disjoint sum of `G` and `H`.
-/

@[expose] public section

namespace SimpleGraph
variable {U U' V V' W W' γ : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {I : SimpleGraph U}
  {G' : SimpleGraph V'} {H' : SimpleGraph W'} {I' : SimpleGraph U'} {v v' : V} {w w' : W}

/-- Disjoint sum of `G` and `H`. -/
@[simps!]
/--
Definition of `sum` / `sum` 的定义

English:
definition sum
  signature: (G : SimpleGraph V) (H : SimpleGraph W)

中文:
定义 求和
  签名: (G : 简单图 V) (H : 简单图 W)
-/
protected def sum (G : SimpleGraph V) (H : SimpleGraph W) : SimpleGraph (V oplus W) where
  Adj
    | Sum.inl u, Sum.inl v => G.Adj u v
    | Sum.inr u, Sum.inr v => H.Adj u v
    | _, _ => false
  symm.symm
    | Sum.inl u, Sum.inl v => G.adj_symm
    | Sum.inr u, Sum.inr v => H.adj_symm
    | Sum.inl _, Sum.inr _ | Sum.inr _, Sum.inl _ => id

@[inherit_doc] infixl:60 " oplusg " => SimpleGraph.sum

/--
theorem `sum_adj_inl` / 定理 `sum_adj_inl`

English:
theorem sum_adj_inl
  statement: (G oplusg H).Adj (.inl v) (.inl v') ↔ G.Adj v v'
  proof: by
  simp

中文:
定理 sum_adj_inl
  结论: (G oplusg H).伴随 (.inl v) (.inl v') ↔ G.伴随 v v'
  证明: by
  simp
-/
theorem sum_adj_inl : (G oplusg H).Adj (.inl v) (.inl v') ↔ G.Adj v v' := by
  simp

/--
theorem `sum_adj_inr` / 定理 `sum_adj_inr`

English:
theorem sum_adj_inr
  statement: (G oplusg H).Adj (.inr w) (.inr w') ↔ H.Adj w w'
  proof: by
  simp

中文:
定理 sum_adj_inr
  结论: (G oplusg H).伴随 (.inr w) (.inr w') ↔ H.伴随 w w'
  证明: by
  simp
-/
theorem sum_adj_inr : (G oplusg H).Adj (.inr w) (.inr w') ↔ H.Adj w w' := by
  simp

/-- The disjoint sum is commutative up to isomorphism. `Iso.sumComm` as a graph isomorphism. -/
@[simps!]
/--
Definition of `Iso.sumComm` / `Iso.sumComm` 的定义

English:
definition Iso.sumComm
  signature: : G oplusg H ≃g H oplusg G
  body: ⟨Equiv.sumComm V W, by
  rintro (u | u) (v | v) <;> simp⟩

中文:
定义 同构.sumComm
  签名: : G oplusg H ≃g H oplusg G
  定义体: ⟨Equiv.sumComm V W, by
  rintro (u | u) (v | v) <;> simp⟩

Depends on / 依赖: Equiv.sumComm, sumComm
-/
def Iso.sumComm : G oplusg H ≃g H oplusg G := ⟨Equiv.sumComm V W, by
  rintro (u | u) (v | v) <;> simp⟩

/-- The disjoint sum is associative up to isomorphism. `Iso.sumAssoc` as a graph isomorphism. -/
@[simps!]
/--
Definition of `Iso.sumAssoc` / `Iso.sumAssoc` 的定义

English:
definition Iso.sumAssoc
  signature: : (G oplusg H) oplusg I ≃g G oplusg (H oplusg I) where
  body: .sumAssoc ..
  map_rel_iff' := by rintro ((u | u) | u) ((v | v) | v) <;> simp

中文:
定义 同构.sumAssoc
  签名: : (G oplusg H) oplusg I ≃g G oplusg (H oplusg I) where
  定义体: .sumAssoc ..
  map_rel_iff' := by rintro ((u | u) | u) ((v | v) | v) <;> simp

Depends on / 依赖: sumAssoc
-/
def Iso.sumAssoc : (G oplusg H) oplusg I ≃g G oplusg (H oplusg I) where
  toEquiv := .sumAssoc ..
  map_rel_iff' := by rintro ((u | u) | u) ((v | v) | v) <;> simp

set_option backward.isDefEq.respectTransparency.types false in
/-- The embedding of `G` into `G ⊕g H`. -/
@[simps]
/--
Definition of `Embedding.sumInl` / `Embedding.sumInl` 的定义

English:
definition Embedding.sumInl
  signature: : G ↪g G oplusg H where
  body: _root_.Sum.inl u
  inj' u v := by simp
  map_rel_iff' := by simp

中文:
定义 嵌入.sumInl
  签名: : G ↪g G oplusg H where
  定义体: _root_.Sum.inl u
  inj' u v := by simp
  map_rel_iff' := by simp

Depends on / 依赖: _root_, _root_.Sum.inl
-/
def Embedding.sumInl : G ↪g G oplusg H where
  toFun u := _root_.Sum.inl u
  inj' u v := by simp
  map_rel_iff' := by simp

set_option backward.isDefEq.respectTransparency.types false in
/-- The embedding of `H` into `G ⊕g H`. -/
@[simps]
/--
Definition of `Embedding.sumInr` / `Embedding.sumInr` 的定义

English:
definition Embedding.sumInr
  signature: : H ↪g G oplusg H where
  body: _root_.Sum.inr u
  inj' u v := by simp
  map_rel_iff' := by simp

中文:
定义 嵌入.sumInr
  签名: : H ↪g G oplusg H where
  定义体: _root_.Sum.inr u
  inj' u v := by simp
  map_rel_iff' := by simp

Depends on / 依赖: _root_, _root_.Sum.inr
-/
def Embedding.sumInr : H ↪g G oplusg H where
  toFun u := _root_.Sum.inr u
  inj' u v := by simp
  map_rel_iff' := by simp

/-- Given homomorphisms `f : G →g G'` and `g : H →g H'`, returns a homomorphism from `G ⊕g H` to
`G' ⊕g H'` that applies `f` to the left component and `g` to the right component. -/
@[simps]
/--
Definition of `Hom.sum` / `Hom.sum` 的定义

English:
definition Hom.sum
  signature: (f : G ->g G') (g : H ->g H')
  body: Sum.map f g
  map_rel' {u v} := by cases u <;> cases v <;> simp_all [f.map_rel, g.map_rel]

中文:
定义 态射.求和
  签名: (f : G ->g G') (g : H ->g H')
  定义体: Sum.map f g
  map_rel' {u v} := by cases u <;> cases v <;> simp_all [f.map_rel, g.map_rel]

Depends on / 依赖: Sum.map
-/
def Hom.sum (f : G ->g G') (g : H ->g H') : G oplusg H ->g G' oplusg H' where
  toFun := Sum.map f g
  map_rel' {u v} := by cases u <;> cases v <;> simp_all [f.map_rel, g.map_rel]

/--
lemma `Hom.sum_comp_sumComm` / 引理 `Hom.sum_comp_sumComm`

English:
lemma Hom.sum_comp_sumComm
  given: (f : G ->g G') (g : H ->g H')
  proof: by
  ext (v | w) <;> simp

中文:
引理 态射.sum_comp_sumComm
  条件: (f : G ->g G') (g : H ->g H')
  证明: by
  ext (v | w) <;> simp
-/
lemma Hom.sum_comp_sumComm (f : G ->g G') (g : H ->g H') :
    comp (sum f g) Iso.sumComm.toHom = comp Iso.sumComm.toHom (sum g f) := by
  ext (v | w) <;> simp

/--
lemma `Hom.sum_sum_comp_sumAssoc` / 引理 `Hom.sum_sum_comp_sumAssoc`

English:
lemma Hom.sum_sum_comp_sumAssoc
  given: (f : G ->g G') (g : H ->g H') (h : I ->g I')
  proof: by
  ext ((v | w) | u) <;> simp

中文:
引理 态射.sum_sum_comp_sumAssoc
  条件: (f : G ->g G') (g : H ->g H') (h : I ->g I')
  证明: by
  ext ((v | w) | u) <;> simp
-/
lemma Hom.sum_sum_comp_sumAssoc (f : G ->g G') (g : H ->g H') (h : I ->g I') :
    comp (sum f (sum g h)) Iso.sumAssoc.toHom = comp Iso.sumAssoc.toHom (sum (sum f g) h) := by
  ext ((v | w) | u) <;> simp

set_option backward.isDefEq.respectTransparency.types false in
/-- Given embeddings `f : G ↪g G'` and `g : H ↪g H'`, returns an embedding from `G ⊕g H` to
`G' ⊕g H'` that applies `f` to the left component and `g` to the right component. -/
@[simps]
/--
Definition of `Embedding.sum` / `Embedding.sum` 的定义

English:
definition Embedding.sum
  signature: (f : G ↪g G') (g : H ↪g H')
  body: Sum.map f g
  inj' u v := by cases u <;> cases v <;> simp
  map_rel_iff' {u v} := by cases u <;> cases v <;> simp

中文:
定义 嵌入.求和
  签名: (f : G ↪g G') (g : H ↪g H')
  定义体: Sum.map f g
  inj' u v := by cases u <;> cases v <;> simp
  map_rel_iff' {u v} := by cases u <;> cases v <;> simp

Depends on / 依赖: Sum.map
-/
def Embedding.sum (f : G ↪g G') (g : H ↪g H') : G oplusg H ↪g G' oplusg H' where
  toFun := Sum.map f g
  inj' u v := by cases u <;> cases v <;> simp
  map_rel_iff' {u v} := by cases u <;> cases v <;> simp

/--
lemma `Embedding.toHom_sum` / 引理 `Embedding.toHom_sum`

English:
lemma Embedding.toHom_sum
  given: (f : G ↪g G') (g : H ↪g H')
  proof: rfl

中文:
引理 嵌入.toHom_sum
  条件: (f : G ↪g G') (g : H ↪g H')
  证明: rfl
-/
lemma Embedding.toHom_sum (f : G ↪g G') (g : H ↪g H') :
    (Embedding.sum f g).toHom = Hom.sum f.toHom g.toHom := rfl

/--
lemma `Embedding.sum_comp_sumComm` / 引理 `Embedding.sum_comp_sumComm`

English:
lemma Embedding.sum_comp_sumComm
  given: (f : G ↪g G') (g : H ↪g H')
  proof: by
  ext (v | w) <;> simp

中文:
引理 嵌入.sum_comp_sumComm
  条件: (f : G ↪g G') (g : H ↪g H')
  证明: by
  ext (v | w) <;> simp
-/
lemma Embedding.sum_comp_sumComm (f : G ↪g G') (g : H ↪g H') :
    comp (sum g f) Iso.sumComm.toEmbedding = comp Iso.sumComm.toEmbedding (sum f g) := by
  ext (v | w) <;> simp

/--
lemma `Embedding.sum_sum_comp_sumAssoc` / 引理 `Embedding.sum_sum_comp_sumAssoc`

English:
lemma Embedding.sum_sum_comp_sumAssoc
  given: (f : G ↪g G') (g : H ↪g H') (h : I ↪g I')
  proof: by
  ext ((v | w) | u) <;> simp

中文:
引理 嵌入.sum_sum_comp_sumAssoc
  条件: (f : G ↪g G') (g : H ↪g H') (h : I ↪g I')
  证明: by
  ext ((v | w) | u) <;> simp
-/
lemma Embedding.sum_sum_comp_sumAssoc (f : G ↪g G') (g : H ↪g H') (h : I ↪g I') :
    comp (sum f (sum g h)) Iso.sumAssoc.toEmbedding =
      comp Iso.sumAssoc.toEmbedding (sum (sum f g) h) := by
  ext ((v | w) | u) <;> simp

/-- Given isomorphisms `f : G ≃g G'` and `g : H ≃g H'`, returns an isomorphism from `G ⊕g H` to
`G' ⊕g H'` that applies `f` to the left component and `g` to the right component. -/
@[simps!, simps toEquiv]
/--
Definition of `Iso.sumCongr` / `Iso.sumCongr` 的定义

English:
definition Iso.sumCongr
  signature: (f : G ≃g G') (g : H ≃g H')
  body: f.toEquiv.sumCongr g.toEquiv
  map_rel_iff' {u v} := by cases u <;> cases v <;> simp [f.map_rel_iff, g.map_rel_iff]

中文:
定义 同构.sumCongr
  签名: (f : G ≃g G') (g : H ≃g H')
  定义体: f.toEquiv.sumCongr g.toEquiv
  map_rel_iff' {u v} := by cases u <;> cases v <;> simp [f.map_rel_iff, g.map_rel_iff]

Depends on / 依赖: f.toEquiv.sumCongr, g.toEquiv, sumCongr, toEquiv
-/
def Iso.sumCongr (f : G ≃g G') (g : H ≃g H') : G oplusg H ≃g G' oplusg H' where
  toEquiv := f.toEquiv.sumCongr g.toEquiv
  map_rel_iff' {u v} := by cases u <;> cases v <;> simp [f.map_rel_iff, g.map_rel_iff]

/--
lemma `Iso.toHom_sumCongr` / 引理 `Iso.toHom_sumCongr`

English:
lemma Iso.toHom_sumCongr
  given: (f : G ≃g G') (g : H ≃g H')
  proof: rfl

中文:
引理 同构.toHom_sumCongr
  条件: (f : G ≃g G') (g : H ≃g H')
  证明: rfl
-/
lemma Iso.toHom_sumCongr (f : G ≃g G') (g : H ≃g H') :
    (Iso.sumCongr f g).toHom = Hom.sum f.toHom g.toHom := rfl

/--
lemma `Iso.toEmbedding_sumCongr` / 引理 `Iso.toEmbedding_sumCongr`

English:
lemma Iso.toEmbedding_sumCongr
  given: (f : G ≃g G') (g : H ≃g H')
  proof: rfl

中文:
引理 同构.toEmbedding_sumCongr
  条件: (f : G ≃g G') (g : H ≃g H')
  证明: rfl
-/
lemma Iso.toEmbedding_sumCongr (f : G ≃g G') (g : H ≃g H') :
    (Iso.sumCongr f g).toEmbedding = Embedding.sum f.toEmbedding g.toEmbedding := rfl

/--
lemma `Iso.sumComm_comp_sumCongr` / 引理 `Iso.sumComm_comp_sumCongr`

English:
lemma Iso.sumComm_comp_sumCongr
  given: (f : G ≃g G') (g : H ≃g H')
  proof: by
  ext (v | w) <;> simp

中文:
引理 同构.sumComm_comp_sumCongr
  条件: (f : G ≃g G') (g : H ≃g H')
  证明: by
  ext (v | w) <;> simp
-/
lemma Iso.sumComm_comp_sumCongr (f : G ≃g G') (g : H ≃g H') :
    comp sumComm (sumCongr f g) = comp (sumCongr g f) sumComm := by
  ext (v | w) <;> simp

/--
lemma `Iso.sumAssoc_comp_sumCongr` / 引理 `Iso.sumAssoc_comp_sumCongr`

English:
lemma Iso.sumAssoc_comp_sumCongr
  given: (f : G ≃g G') (g : H ≃g H') (h : I ≃g I')
  proof: by
  ext ((v | w) | u) <;> simp

中文:
引理 同构.sumAssoc_comp_sumCongr
  条件: (f : G ≃g G') (g : H ≃g H') (h : I ≃g I')
  证明: by
  ext ((v | w) | u) <;> simp
-/
lemma Iso.sumAssoc_comp_sumCongr (f : G ≃g G') (g : H ≃g H') (h : I ≃g I') :
    comp sumAssoc (sumCongr (sumCongr f g) h) = comp (sumCongr f (sumCongr g h)) sumAssoc := by
  ext ((v | w) | u) <;> simp

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `edgeSetSumEquiv` / `edgeSetSumEquiv` 的定义

English:
definition edgeSetSumEquiv
  signature: : (G oplusg H).edgeSet ≃ G.edgeSet oplus H.edgeSet where
  body: fun ⟨e, he⟩ => e.fromRelNdrec (sym := symm _) he (fun
      | Sum.inl u, Sum.inl v, h => .inl ⟨s(u, v), h⟩
      | Sum.inr u, Sum.inr v, h => .inr ⟨s(u, v), h⟩
      | Sum.inl u, Sum.inr v, h => by contradiction
      | Sum.inr u, Sum.inl v, h => by contradiction
    ) (by grind)
  invFun
    | Sum.inl ⟨e, he⟩ =>
e.fromRelNdrec (sym := G.symm) he (fun u v h => ⟨s(.inl u, .inl v), h⟩) by simp
    | Sum.inr ⟨e, he⟩ =>
e.fromRelNdrec (sym := H.symm) he (fun u v h => ⟨s(.inr u, .inr v), h⟩) by simp
  left_inv := by rintro ⟨⟨u | u, v | v⟩, h⟩ <;> first | contradiction | rfl
  right_inv := by rintro (⟨⟨u, v⟩, h⟩ | ⟨⟨u, v⟩, h⟩) <;> rfl

中文:
定义 edgeSetSumEquiv
  签名: : (G oplusg H).edgeSet ≃ G.edgeSet oplus H.edgeSet where
  定义体: fun ⟨e, he⟩ => e.fromRelNdrec (sym := symm _) he (fun
      | Sum.inl u, Sum.inl v, h => .inl ⟨s(u, v), h⟩
      | Sum.inr u, Sum.inr v, h => .inr ⟨s(u, v), h⟩
      | Sum.inl u, Sum.inr v, h => by contradiction
      | Sum.inr u, Sum.inl v, h => by contradiction
    ) (by grind)
  invFun
    | Sum.inl ⟨e, he⟩ =>
e.fromRelNdrec (sym := G.symm) he (fun u v h => ⟨s(.inl u, .inl v), h⟩) by simp
    | Sum.inr ⟨e, he⟩ =>
e.fromRelNdrec (sym := H.symm) he (fun u v h => ⟨s(.inr u, .inr v), h⟩) by simp
  left_inv := by rintro ⟨⟨u | u, v | v⟩, h⟩ <;> first | contradiction | rfl
  right_inv := by rintro (⟨⟨u, v⟩, h⟩ | ⟨⟨u, v⟩, h⟩) <;> rfl

Depends on / 依赖: G.symm, H.symm, Sum.inl, Sum.inr, e.fromRelNdrec, fromRelNdrec, invFun, left_inv
-/
def edgeSetSumEquiv : (G oplusg H).edgeSet ≃ G.edgeSet oplus H.edgeSet where
  toFun :=
    fun ⟨e, he⟩ => e.fromRelNdrec (sym := symm _) he (fun
      | Sum.inl u, Sum.inl v, h => .inl ⟨s(u, v), h⟩
      | Sum.inr u, Sum.inr v, h => .inr ⟨s(u, v), h⟩
      | Sum.inl u, Sum.inr v, h => by contradiction
      | Sum.inr u, Sum.inl v, h => by contradiction
    ) (by grind)
  invFun
    | Sum.inl ⟨e, he⟩ =>
e.fromRelNdrec (sym := G.symm) he (fun u v h => ⟨s(.inl u, .inl v), h⟩) by simp
    | Sum.inr ⟨e, he⟩ =>
e.fromRelNdrec (sym := H.symm) he (fun u v h => ⟨s(.inr u, .inr v), h⟩) by simp
  left_inv := by rintro ⟨⟨u | u, v | v⟩, h⟩ <;> first | contradiction | rfl
  right_inv := by rintro (⟨⟨u, v⟩, h⟩ | ⟨⟨u, v⟩, h⟩) <;> rfl

/--
lemma `not_adj_sum_inl_inr` / 引理 `not_adj_sum_inl_inr`

English:
lemma not_adj_sum_inl_inr
  given: (v w)
  statement: ¬(G oplusg H).Adj (.inl v) (.inr w)
  proof: by simp

中文:
引理 not_adj_sum_inl_inr
  条件: (v w)
  结论: ¬(G oplusg H).伴随 (.inl v) (.inr w)
  证明: by simp
-/
lemma not_adj_sum_inl_inr (v w) : ¬(G oplusg H).Adj (.inl v) (.inr w) := by simp

/--
lemma `not_reachable_sum_inl_inr` / 引理 `not_reachable_sum_inl_inr`

English:
lemma not_reachable_sum_inl_inr
  given: (v w)
  statement: ¬(G oplusg H).Reachable (.inl v) (.inr w)
  proof: by
  rintro ⟨p⟩
  have hs : forall x : V oplus W, x ∉ Set.range .inl ↔ x in Set.range .inr := by simp
  obtain ⟨⟨d, hadj⟩, _, hd1, hd2⟩ := p.exists_boundary_dart (Set.range .inl) (by simp) (by simp)
  simp only [hs] at hadj hd1 hd2
  obtain ⟨v', hv'⟩ := hd1
  obtain ⟨w', hw'⟩ := hd2
  rw [← hv']; rw [← hw'] at hadj
  exact not_adj_sum_inl_inr _ _ hadj

中文:
引理 not_reachable_sum_inl_inr
  条件: (v w)
  结论: ¬(G oplusg H).Reachable (.inl v) (.inr w)
  证明: by
  rintro ⟨p⟩
  have hs : forall x : V oplus W, x ∉ Set.range .inl ↔ x in Set.range .inr := by simp
  obtain ⟨⟨d, hadj⟩, _, hd1, hd2⟩ := p.exists_boundary_dart (Set.range .inl) (by simp) (by simp)
  simp only [hs] at hadj hd1 hd2
  obtain ⟨v', hv'⟩ := hd1
  obtain ⟨w', hw'⟩ := hd2
  rw [← hv']; rw [← hw'] at hadj
  exact not_adj_sum_inl_inr _ _ hadj

Depends on / 依赖: Set.range, exists_boundary_dart, not_adj_sum_inl_inr, p.exists_boundary_dart
-/
lemma not_reachable_sum_inl_inr (v w) : ¬(G oplusg H).Reachable (.inl v) (.inr w) := by
  rintro ⟨p⟩
  have hs : forall x : V oplus W, x ∉ Set.range .inl ↔ x in Set.range .inr := by simp
  obtain ⟨⟨d, hadj⟩, _, hd1, hd2⟩ := p.exists_boundary_dart (Set.range .inl) (by simp) (by simp)
  simp only [hs] at hadj hd1 hd2
  obtain ⟨v', hv'⟩ := hd1
  obtain ⟨w', hw'⟩ := hd2
  rw [← hv']; rw [← hw'] at hadj
  exact not_adj_sum_inl_inr _ _ hadj

/--
lemma `not_preconnected_sum` / 引理 `not_preconnected_sum`

English:
lemma not_preconnected_sum
  given: [Nonempty V] [Nonempty W]
  statement: ¬(G oplusg H).Preconnected
  proof: fun h => not_reachable_sum_inl_inr (Classical.arbitrary _) (Classical.arbitrary _) (h ..)

中文:
引理 not_preconnected_sum
  条件: [非空 V] [非空 W]
  结论: ¬(G oplusg H).预连通
  证明: fun h => not_reachable_sum_inl_inr (Classical.arbitrary _) (Classical.arbitrary _) (h ..)

Depends on / 依赖: Classical, Classical.arbitrary, arbitrary, not_reachable_sum_inl_inr
-/
lemma not_preconnected_sum [Nonempty V] [Nonempty W] : ¬(G oplusg H).Preconnected :=
  fun h => not_reachable_sum_inl_inr (Classical.arbitrary _) (Classical.arbitrary _) (h ..)

/--
lemma `not_connected_sum` / 引理 `not_connected_sum`

English:
lemma not_connected_sum
  given: [Nonempty V] [Nonempty W]
  statement: ¬(G oplusg H).Connected
  proof: by
  simp [connected_iff, not_preconnected_sum]

中文:
引理 not_connected_sum
  条件: [非空 V] [非空 W]
  结论: ¬(G oplusg H).连通
  证明: by
  simp [connected_iff, not_preconnected_sum]

Depends on / 依赖: connected_iff, not_preconnected_sum
-/
lemma not_connected_sum [Nonempty V] [Nonempty W] : ¬(G oplusg H).Connected := by
  simp [connected_iff, not_preconnected_sum]

/--
lemma `Reachable.sum_sup_edge` / 引理 `Reachable.sum_sup_edge`

English:
lemma Reachable.sum_sup_edge
  given: (hv : G.Reachable v v') (hw : H.Reachable w w')
  proof: ((hv.symm.map Embedding.sumInl.toHom).mono le_sup_left).trans .trans
(Adj.reachable <| by simp [edge]) (hw.map Embedding.sumInr.toHom).mono le_sup_left

中文:
引理 Reachable.sum_sup_edge
  条件: (hv : G.Reachable v v') (hw : H.Reachable w w')
  证明: ((hv.symm.map Embedding.sumInl.toHom).mono le_sup_left).trans .trans
(Adj.reachable <| by simp [edge]) (hw.map Embedding.sumInr.toHom).mono le_sup_left

Depends on / 依赖: Adj.reachable, Embedding, Embedding.sumInl.toHom, Embedding.sumInr.toHom, hv.symm.map, hw.map, le_sup_left, reachable, sumInl, sumInr
-/
lemma Reachable.sum_sup_edge (hv : G.Reachable v v') (hw : H.Reachable w w') :
    (G.sum H ⊔ edge (.inl v) (.inr w)).Reachable (.inl v') (.inr w') :=
((hv.symm.map Embedding.sumInl.toHom).mono le_sup_left).trans .trans
(Adj.reachable <| by simp [edge]) (hw.map Embedding.sumInr.toHom).mono le_sup_left

/--
lemma `Preconnected.sum_sup_edge` / 引理 `Preconnected.sum_sup_edge`

English:
lemma Preconnected.sum_sup_edge
  given: (hG : G.Preconnected) (hH : H.Preconnected)
  proof: by
  rintro (v₁ | w₁) (v₂ | w₂)
  · exact ((hG v₁ v₂).map Embedding.sumInl.toHom).mono le_sup_left
  · exact (hG ..).sum_sup_edge (hH ..)
  · exact ((hG ..).sum_sup_edge (hH ..)).symm
  · exact ((hH w₁ w₂).map Embedding.sumInr.toHom).mono le_sup_left

中文:
引理 预连通.sum_sup_edge
  条件: (hG : G.预连通) (hH : H.预连通)
  证明: by
  rintro (v₁ | w₁) (v₂ | w₂)
  · exact ((hG v₁ v₂).map Embedding.sumInl.toHom).mono le_sup_left
  · exact (hG ..).sum_sup_edge (hH ..)
  · exact ((hG ..).sum_sup_edge (hH ..)).symm
  · exact ((hH w₁ w₂).map Embedding.sumInr.toHom).mono le_sup_left

Depends on / 依赖: Embedding, Embedding.sumInl.toHom, Embedding.sumInr.toHom, le_sup_left, sumInl, sumInr, sum_sup_edge
-/
lemma Preconnected.sum_sup_edge (hG : G.Preconnected) (hH : H.Preconnected) :
    (G.sum H ⊔ edge (.inl v) (.inr w)).Preconnected := by
  rintro (v₁ | w₁) (v₂ | w₂)
  · exact ((hG v₁ v₂).map Embedding.sumInl.toHom).mono le_sup_left
  · exact (hG ..).sum_sup_edge (hH ..)
  · exact ((hG ..).sum_sup_edge (hH ..)).symm
  · exact ((hH w₁ w₂).map Embedding.sumInr.toHom).mono le_sup_left

/--
lemma `Connected.sum_sup_edge` / 引理 `Connected.sum_sup_edge`

English:
lemma Connected.sum_sup_edge
  given: (hG : G.Connected) (hH : H.Connected)
  proof: by
  obtain ⟨hG⟩ := hG; exact ⟨hG.sum_sup_edge hH.preconnected⟩

中文:
引理 连通.sum_sup_edge
  条件: (hG : G.连通) (hH : H.连通)
  证明: by
  obtain ⟨hG⟩ := hG; exact ⟨hG.sum_sup_edge hH.preconnected⟩

Depends on / 依赖: hG.sum_sup_edge, hH.preconnected, preconnected, sum_sup_edge
-/
lemma Connected.sum_sup_edge (hG : G.Connected) (hH : H.Connected) :
    (G.sum H ⊔ edge (.inl v) (.inr w)).Connected := by
  obtain ⟨hG⟩ := hG; exact ⟨hG.sum_sup_edge hH.preconnected⟩

/--
Definition of `Coloring.sum` / `Coloring.sum` 的定义

English:
definition Coloring.sum
  signature: (cG : G.Coloring γ) (cH : H.Coloring γ)
  body: Sum.elim cG cH
  map_rel' {u v} huv := by cases u <;> cases v <;> simp_all [cG.valid, cH.valid]

中文:
定义 染色.求和
  签名: (cG : G.染色 γ) (cH : H.染色 γ)
  定义体: Sum.elim cG cH
  map_rel' {u v} huv := by cases u <;> cases v <;> simp_all [cG.valid, cH.valid]

Depends on / 依赖: Sum.elim
-/
def Coloring.sum (cG : G.Coloring γ) (cH : H.Coloring γ) : (G oplusg H).Coloring γ where
  toFun := Sum.elim cG cH
  map_rel' {u v} huv := by cases u <;> cases v <;> simp_all [cG.valid, cH.valid]

/--
Definition of `Coloring.sumLeft` / `Coloring.sumLeft` 的定义

English:
definition Coloring.sumLeft
  signature: (c : (G oplusg H).Coloring γ)
  body: c.comp Embedding.sumInl.toHom

中文:
定义 染色.sumLeft
  签名: (c : (G oplusg H).染色 γ)
  定义体: c.comp Embedding.sumInl.toHom

Depends on / 依赖: Embedding, Embedding.sumInl.toHom, c.comp, sumInl
-/
def Coloring.sumLeft (c : (G oplusg H).Coloring γ) : G.Coloring γ := c.comp Embedding.sumInl.toHom

/--
Definition of `Coloring.sumRight` / `Coloring.sumRight` 的定义

English:
definition Coloring.sumRight
  signature: (c : (G oplusg H).Coloring γ)
  body: c.comp Embedding.sumInr.toHom

@[simp]

中文:
定义 染色.sumRight
  签名: (c : (G oplusg H).染色 γ)
  定义体: c.comp Embedding.sumInr.toHom

@[simp]

Depends on / 依赖: Embedding, Embedding.sumInr.toHom, c.comp, sumInr
-/
def Coloring.sumRight (c : (G oplusg H).Coloring γ) : H.Coloring γ := c.comp Embedding.sumInr.toHom

@[simp]
/--
theorem `Coloring.sumLeft_sum` / 定理 `Coloring.sumLeft_sum`

English:
theorem Coloring.sumLeft_sum
  given: (cG : G.Coloring γ) (cH : H.Coloring γ)
  statement: (cG.sum cH).sumLeft = cG
  proof: rfl

@[simp]

中文:
定理 染色.sumLeft_sum
  条件: (cG : G.染色 γ) (cH : H.染色 γ)
  结论: (cG.求和 cH).sumLeft = cG
  证明: rfl

@[simp]
-/
theorem Coloring.sumLeft_sum (cG : G.Coloring γ) (cH : H.Coloring γ) : (cG.sum cH).sumLeft = cG :=
  rfl

@[simp]
/--
theorem `Coloring.sumRight_sum` / 定理 `Coloring.sumRight_sum`

English:
theorem Coloring.sumRight_sum
  given: (cG : G.Coloring γ) (cH : H.Coloring γ)
  statement: (cG.sum cH).sumRight = cH
  proof: rfl

@[simp]

中文:
定理 染色.sumRight_sum
  条件: (cG : G.染色 γ) (cH : H.染色 γ)
  结论: (cG.求和 cH).sumRight = cH
  证明: rfl

@[simp]
-/
theorem Coloring.sumRight_sum (cG : G.Coloring γ) (cH : H.Coloring γ) : (cG.sum cH).sumRight = cH :=
  rfl

@[simp]
/--
theorem `Coloring.sum_sumLeft_sumRight` / 定理 `Coloring.sum_sumLeft_sumRight`

English:
theorem Coloring.sum_sumLeft_sumRight
  given: (c : (G oplusg H).Coloring γ)
  statement: c.sumLeft.sum c.sumRight = c
  proof: by
  ext (u | u) <;> rfl

中文:
定理 染色.sum_sumLeft_sumRight
  条件: (c : (G oplusg H).染色 γ)
  结论: c.sumLeft.求和 c.sumRight = c
  证明: by
  ext (u | u) <;> rfl
-/
theorem Coloring.sum_sumLeft_sumRight (c : (G oplusg H).Coloring γ) : c.sumLeft.sum c.sumRight = c := by
  ext (u | u) <;> rfl

/--
Definition of `Coloring.sumEquiv` / `Coloring.sumEquiv` 的定义

English:
definition Coloring.sumEquiv
  signature: : (G oplusg H).Coloring γ ≃ G.Coloring γ × H.Coloring γ where
  body: ⟨c.sumLeft, c.sumRight⟩
  invFun p := p.1.sum p.2
  left_inv c := by simp [sum_sumLeft_sumRight c]

中文:
定义 染色.sumEquiv
  签名: : (G oplusg H).染色 γ ≃ G.染色 γ × H.染色 γ where
  定义体: ⟨c.sumLeft, c.sumRight⟩
  invFun p := p.1.sum p.2
  left_inv c := by simp [sum_sumLeft_sumRight c]

Depends on / 依赖: c.sumLeft, c.sumRight, sumLeft, sumRight
-/
def Coloring.sumEquiv : (G oplusg H).Coloring γ ≃ G.Coloring γ × H.Coloring γ where
  toFun c := ⟨c.sumLeft, c.sumRight⟩
  invFun p := p.1.sum p.2
  left_inv c := by simp [sum_sumLeft_sumRight c]

/--
Definition of `Coloring.sumFin` / `Coloring.sumFin` 的定义

English:
definition Coloring.sumFin
  signature: {n m : Nat} (cG : G.Coloring (Fin n)) (cH : H.Coloring (Fin m))
  body: sum
  (G.recolorOfEmbedding (Fin.castLEEmb (n.le_max_left m)) cG)
  (H.recolorOfEmbedding (Fin.castLEEmb (n.le_max_right m)) cH)

中文:
定义 染色.sumFin
  签名: {n m : 自然数} (cG : G.染色 (有限集 n)) (cH : H.染色 (有限集 m))
  定义体: sum
  (G.recolorOfEmbedding (Fin.castLEEmb (n.le_max_left m)) cG)
  (H.recolorOfEmbedding (Fin.castLEEmb (n.le_max_right m)) cH)
-/
def Coloring.sumFin {n m : Nat} (cG : G.Coloring (Fin n)) (cH : H.Coloring (Fin m)) :
    (G oplusg H).Coloring (Fin (max n m)) := sum
  (G.recolorOfEmbedding (Fin.castLEEmb (n.le_max_left m)) cG)
  (H.recolorOfEmbedding (Fin.castLEEmb (n.le_max_right m)) cH)

/--
theorem `Colorable.sum_max` / 定理 `Colorable.sum_max`

English:
theorem Colorable.sum_max
  given: {n m : Nat} (hG : G.Colorable n) (hH : H.Colorable m)
  proof: Nonempty.intro (hG.some.sumFin hH.some)

中文:
定理 Colorable.sum_max
  条件: {n m : 自然数} (hG : G.Colorable n) (hH : H.Colorable m)
  证明: Nonempty.intro (hG.some.sumFin hH.some)

Depends on / 依赖: Nonempty, Nonempty.intro, hG.some.sumFin, hH.some, sumFin
-/
theorem Colorable.sum_max {n m : Nat} (hG : G.Colorable n) (hH : H.Colorable m) :
    (G oplusg H).Colorable (max n m) := Nonempty.intro (hG.some.sumFin hH.some)

/--
theorem `Colorable.of_sum_left` / 定理 `Colorable.of_sum_left`

English:
theorem Colorable.of_sum_left
  given: {n : Nat} (h : (G oplusg H).Colorable n)
  statement: G.Colorable n
  proof: Nonempty.intro (h.some.sumLeft)

中文:
定理 Colorable.of_sum_left
  条件: {n : 自然数} (h : (G oplusg H).Colorable n)
  结论: G.Colorable n
  证明: Nonempty.intro (h.some.sumLeft)

Depends on / 依赖: Nonempty, Nonempty.intro, h.some.sumLeft, sumLeft
-/
theorem Colorable.of_sum_left {n : Nat} (h : (G oplusg H).Colorable n) : G.Colorable n :=
  Nonempty.intro (h.some.sumLeft)

/--
theorem `Colorable.of_sum_right` / 定理 `Colorable.of_sum_right`

English:
theorem Colorable.of_sum_right
  given: {n : Nat} (h : (G oplusg H).Colorable n)
  statement: H.Colorable n
  proof: Nonempty.intro (h.some.sumRight)

@[simp]

中文:
定理 Colorable.of_sum_right
  条件: {n : 自然数} (h : (G oplusg H).Colorable n)
  结论: H.Colorable n
  证明: Nonempty.intro (h.some.sumRight)

@[simp]

Depends on / 依赖: Nonempty, Nonempty.intro, h.some.sumRight, sumRight
-/
theorem Colorable.of_sum_right {n : Nat} (h : (G oplusg H).Colorable n) : H.Colorable n :=
  Nonempty.intro (h.some.sumRight)

@[simp]
/--
theorem `colorable_sum` / 定理 `colorable_sum`

English:
theorem colorable_sum
  given: {n : Nat}
  statement: (G oplusg H).Colorable n ↔ G.Colorable n ∧ H.Colorable n
  proof: ⟨fun cGH => ⟨cGH.of_sum_left, cGH.of_sum_right⟩,
    fun ⟨cG, cH⟩ => by rw [← n.max_self]; exact cG.sum_max cH⟩

中文:
定理 colorable_sum
  条件: {n : 自然数}
  结论: (G oplusg H).Colorable n ↔ G.Colorable n ∧ H.Colorable n
  证明: ⟨fun cGH => ⟨cGH.of_sum_left, cGH.of_sum_right⟩,
    fun ⟨cG, cH⟩ => by rw [← n.max_self]; exact cG.sum_max cH⟩

Depends on / 依赖: cG.sum_max, cGH.of_sum_left, cGH.of_sum_right, max_self, n.max_self, of_sum_left, of_sum_right, sum_max
-/
theorem colorable_sum {n : Nat} : (G oplusg H).Colorable n ↔ G.Colorable n ∧ H.Colorable n :=
  ⟨fun cGH => ⟨cGH.of_sum_left, cGH.of_sum_right⟩,
    fun ⟨cG, cH⟩ => by rw [← n.max_self]; exact cG.sum_max cH⟩

/--
theorem `chromaticNumber_le_sum_left` / 定理 `chromaticNumber_le_sum_left`

English:
theorem chromaticNumber_le_sum_left
  statement: G.chromaticNumber <= (G oplusg H).chromaticNumber
  proof: chromaticNumber_le_of_forall_imp (fun _ h => h.of_sum_left)

中文:
定理 chromaticNumber_le_sum_left
  结论: G.chromaticNumber <= (G oplusg H).chromaticNumber
  证明: chromaticNumber_le_of_forall_imp (fun _ h => h.of_sum_left)

Depends on / 依赖: chromaticNumber_le_of_forall_imp, h.of_sum_left, of_sum_left
-/
theorem chromaticNumber_le_sum_left : G.chromaticNumber <= (G oplusg H).chromaticNumber :=
  chromaticNumber_le_of_forall_imp (fun _ h => h.of_sum_left)

/--
theorem `chromaticNumber_le_sum_right` / 定理 `chromaticNumber_le_sum_right`

English:
theorem chromaticNumber_le_sum_right
  statement: H.chromaticNumber <= (G oplusg H).chromaticNumber
  proof: chromaticNumber_le_of_forall_imp (fun _ h => h.of_sum_right)

@[simp]

中文:
定理 chromaticNumber_le_sum_right
  结论: H.chromaticNumber <= (G oplusg H).chromaticNumber
  证明: chromaticNumber_le_of_forall_imp (fun _ h => h.of_sum_right)

@[simp]

Depends on / 依赖: chromaticNumber_le_of_forall_imp, h.of_sum_right, of_sum_right
-/
theorem chromaticNumber_le_sum_right : H.chromaticNumber <= (G oplusg H).chromaticNumber :=
  chromaticNumber_le_of_forall_imp (fun _ h => h.of_sum_right)

@[simp]
/--
theorem `chromaticNumber_sum` / 定理 `chromaticNumber_sum`

English:
theorem chromaticNumber_sum
  proof: by
  refine eq_max chromaticNumber_le_sum_left chromaticNumber_le_sum_right fun {d} hG hH => ?_
  cases d with
  | top => simp
  | coe n =>
    let cG : G.Coloring (Fin n) := (chromaticNumber_le_iff_colorable.mp hG).some
    let cH : H.Coloring (Fin n) := (chromaticNumber_le_iff_colorable.mp hH).some
    exact chromaticNumber_le_iff_colorable.mpr (Nonempty.intro (cG.sum cH))

中文:
定理 chromaticNumber_sum
  证明: by
  refine eq_max chromaticNumber_le_sum_left chromaticNumber_le_sum_right fun {d} hG hH => ?_
  cases d with
  | top => simp
  | coe n =>
    let cG : G.Coloring (Fin n) := (chromaticNumber_le_iff_colorable.mp hG).some
    let cH : H.Coloring (Fin n) := (chromaticNumber_le_iff_colorable.mp hH).some
    exact chromaticNumber_le_iff_colorable.mpr (Nonempty.intro (cG.sum cH))

Depends on / 依赖: Coloring, G.Coloring, H.Coloring, Nonempty, Nonempty.intro, cG.sum, chromaticNumber_le_iff_colorable, chromaticNumber_le_iff_colorable.mp, chromaticNumber_le_iff_colorable.mpr, chromaticNumber_le_sum_left, chromaticNumber_le_sum_right, eq_max
-/
theorem chromaticNumber_sum :
    (G oplusg H).chromaticNumber = max G.chromaticNumber H.chromaticNumber := by
  refine eq_max chromaticNumber_le_sum_left chromaticNumber_le_sum_right fun {d} hG hH => ?_
  cases d with
  | top => simp
  | coe n =>
    let cG : G.Coloring (Fin n) := (chromaticNumber_le_iff_colorable.mp hG).some
    let cH : H.Coloring (Fin n) := (chromaticNumber_le_iff_colorable.mp hH).some
    exact chromaticNumber_le_iff_colorable.mpr (Nonempty.intro (cG.sum cH))

/--
lemma `neighborSet_sum_inl` / 引理 `neighborSet_sum_inl`

English:
lemma neighborSet_sum_inl
  given: (v : V)
  statement: (G oplusg H).neighborSet (.inl v) = Sum.inl '' G.neighborSet v
  proof: by
  ext (v' | w') <;> simp

中文:
引理 neighborSet_sum_inl
  条件: (v : V)
  结论: (G oplusg H).neighborSet (.inl v) = 和.inl '' G.neighborSet v
  证明: by
  ext (v' | w') <;> simp
-/
lemma neighborSet_sum_inl (v : V) : (G oplusg H).neighborSet (.inl v) = Sum.inl '' G.neighborSet v := by
  ext (v' | w') <;> simp

/--
lemma `neighborSet_sum_inr` / 引理 `neighborSet_sum_inr`

English:
lemma neighborSet_sum_inr
  given: (w : W)
  statement: (G oplusg H).neighborSet (.inr w) = Sum.inr '' H.neighborSet w
  proof: by
  ext (v' | w') <;> simp

中文:
引理 neighborSet_sum_inr
  条件: (w : W)
  结论: (G oplusg H).neighborSet (.inr w) = 和.inr '' H.neighborSet w
  证明: by
  ext (v' | w') <;> simp
-/
lemma neighborSet_sum_inr (w : W) : (G oplusg H).neighborSet (.inr w) = Sum.inr '' H.neighborSet w := by
  ext (v' | w') <;> simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: V] [DecidableEq W] [LocallyFinite G] [LocallyFinite H] :
  body: by
  rintro (v | w) <;> simp only [neighborSet_sum_inl, neighborSet_sum_inr] <;>
    infer_instance

中文:
实例 [DecidableEq
  签名: V] [DecidableEq W] [局部有限 G] [局部有限 H] :
  定义体: by
  rintro (v | w) <;> simp only [neighborSet_sum_inl, neighborSet_sum_inr] <;>
    infer_instance

Depends on / 依赖: infer_instance, neighborSet_sum_inl, neighborSet_sum_inr
-/
instance [DecidableEq V] [DecidableEq W] [LocallyFinite G] [LocallyFinite H] :
    LocallyFinite (G oplusg H) := by
  rintro (v | w) <;> simp only [neighborSet_sum_inl, neighborSet_sum_inr] <;>
    infer_instance

end SimpleGraph
