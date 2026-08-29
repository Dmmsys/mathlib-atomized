/-
Copyright (c) 2023 Yaël Dillies, Mitchell Horner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Mitchell Horner
-/
module

public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Combinatorics.SimpleGraph.Subgraph

/-!
# Containment of graphs

This file introduces the concept of one simple graph containing a copy of another.

For two simple graphs `G` and `H`, a *copy* of `G` in `H` is a (not necessarily induced) subgraph of
`H` isomorphic to `G`.

If there exists a copy of `G` in `H`, we say that `H` *contains* `G`. This is equivalent to saying
that there is an injective graph homomorphism `G → H` between them (this is **not** the same as a
graph embedding, as we do not require the subgraph to be induced).

If there exists an induced copy of `G` in `H`, we say that `H` *inducingly contains* `G`. This is
equivalent to saying that there is a graph embedding `G ↪ H`.

## Main declarations

Containment:
* `SimpleGraph.Copy G H` is the type of copies of `G` in `H`, implemented as the subtype of
  *injective* homomorphisms.
* `SimpleGraph.IsContained G H`, `G ⊑ H` is the relation that `H` contains a copy of `G`, that
  is, the type of copies of `G` in `H` is nonempty. This is equivalent to the existence of an
  isomorphism from `G` to a subgraph of `H`.
  This is similar to `SimpleGraph.IsSubgraph` except that the simple graphs here need not have the
  same underlying vertex type.
* `SimpleGraph.Free` is the predicate that `H` is `G`-free, that is, `H` does not contain a copy of
  `G`. This is the negation of `SimpleGraph.IsContained` implemented for convenience.
* `SimpleGraph.killCopies G H`: Subgraph of `G` that does not contain `H`. Obtained by arbitrarily
  removing an edge from each copy of `H` in `G`.
* `SimpleGraph.copyCount G H`: Number of copies of `H` in `G`, i.e. number of subgraphs of `G`
  isomorphic to `H`.
* `SimpleGraph.labelledCopyCount G H`: Number of labelled copies of `H` in `G`, i.e. number of
  graph embeddings from `H` to `G`.

Induced containment:
* Induced copies of `G` inside `H` are already defined as `G ↪g H`.
* `SimpleGraph.IsIndContained G H` : `G` is contained as an induced subgraph in `H`.

## Notation

The following notation is declared in scope `SimpleGraph`:
* `G ⊑ H` for `SimpleGraph.IsContained G H`.
* `G ⊴ H` for `SimpleGraph.IsIndContained G H`.

## TODO

* Relate `⊥ ⊴ H` to there being an independent set in `H`.
* Count induced copies of a graph inside another.
* Make `copyCount`/`labelledCopyCount` computable (not necessarily efficiently).
-/

@[expose] public section

open Finset Function
open Fintype (card)

namespace SimpleGraph
variable {V W X α β γ : Type*} {G G₁ G₂ G₃ : SimpleGraph V} {H : SimpleGraph W} {I : SimpleGraph X}
  {A : SimpleGraph α} {B : SimpleGraph β} {C : SimpleGraph γ}

/-!
### Copies

#### Not necessarily induced copies

A copy of a subgraph `G` inside a subgraph `H` is an embedding of the vertices of `G` into the
vertices of `H`, such that adjacency in `G` implies adjacency in `H`.

We capture this concept by injective graph homomorphisms.
-/

section Copy

/--
Definition of `Copy` / `Copy` 的定义

English:
structure Copy
  parameters: (A : SimpleGraph α) (B : SimpleGraph β)
  axioms and operations (2):
    - toHom : A ->g B
    - injective' : Injective toHom

中文:
结构 余py
  参数: (A : 简单图 α) (B : 简单图 β)
  公理与运算 (2 个):
    - toHom : A ->g B
    - injective' : 单射 toHom
-/
structure Copy (A : SimpleGraph α) (B : SimpleGraph β) where
  /-- A copy gives rise to a homomorphism. -/
  toHom : A ->g B
  injective' : Injective toHom

/--
Definition of `Hom.toCopy` / `Hom.toCopy` 的定义

English:
abbreviation Hom.toCopy
  signature: (f : A ->g B) (h : Injective f)
  body: .mk f h

中文:
缩写 态射.toCopy
  签名: (f : A ->g B) (h : 单射 f)
  定义体: .mk f h
-/
abbrev Hom.toCopy (f : A ->g B) (h : Injective f) : Copy A B := .mk f h

/--
Definition of `Embedding.toCopy` / `Embedding.toCopy` 的定义

English:
abbreviation Embedding.toCopy
  signature: (f : A ↪g B)
  body: f.toHom.toCopy f.injective

中文:
缩写 嵌入.toCopy
  签名: (f : A ↪g B)
  定义体: f.toHom.toCopy f.injective

Depends on / 依赖: f.injective, f.toHom.toCopy, injective, toCopy
-/
abbrev Embedding.toCopy (f : A ↪g B) : Copy A B := f.toHom.toCopy f.injective

/--
Definition of `Iso.toCopy` / `Iso.toCopy` 的定义

English:
abbreviation Iso.toCopy
  signature: (f : A ≃g B)
  body: f.toEmbedding.toCopy

中文:
缩写 同构.toCopy
  签名: (f : A ≃g B)
  定义体: f.toEmbedding.toCopy

Depends on / 依赖: f.toEmbedding.toCopy, toCopy, toEmbedding
-/
abbrev Iso.toCopy (f : A ≃g B) : Copy A B := f.toEmbedding.toCopy

namespace Copy

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (Copy A B) α β
  body: DFunLike.coe f.toHom
  coe_injective f g h := by obtain ⟨⟨_, _⟩, _⟩ := f; congr!

中文:
实例 :
  签名: 函数状 (余py A B) α β
  定义体: DFunLike.coe f.toHom
  coe_injective f g h := by obtain ⟨⟨_, _⟩, _⟩ := f; congr!

Depends on / 依赖: DFunLike, DFunLike.coe, f.toHom
-/
instance : FunLike (Copy A B) α β where
  coe f := DFunLike.coe f.toHom
  coe_injective f g h := by obtain ⟨⟨_, _⟩, _⟩ := f; congr!

/--
lemma `injective` / 引理 `injective`

English:
lemma injective
  given: (f : Copy A B)
  statement: Injective f.toHom
  proof: f.injective'

中文:
引理 injective
  条件: (f : 余py A B)
  结论: 单射 f.toHom
  证明: f.injective'

Depends on / 依赖: f.injective, injective
-/
lemma injective (f : Copy A B) : Injective f.toHom := f.injective'

/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {f g : Copy A B}
  statement: (forall a, f a = g a) -> f = g
  proof: DFunLike.ext _ _

中文:
引理 ext
  条件: {f g : 余py A B}
  结论: (对任意 a, f a = g a) -> f = g
  证明: DFunLike.ext _ _
-/
@[ext] lemma ext {f g : Copy A B} : (forall a, f a = g a) -> f = g := DFunLike.ext _ _

/--
lemma `coe_toHom` / 引理 `coe_toHom`

English:
lemma coe_toHom
  given: (f : Copy A B)
  statement: ⇑f.toHom = f
  proof: rfl

中文:
引理 coe_toHom
  条件: (f : 余py A B)
  结论: ⇑f.toHom = f
  证明: rfl
-/
@[simp] lemma coe_toHom (f : Copy A B) : ⇑f.toHom = f := rfl
/--
lemma `toHom_apply` / 引理 `toHom_apply`

English:
lemma toHom_apply
  given: (f : Copy A B) (a : α)
  statement: ⇑f.toHom a = f a
  proof: rfl

中文:
引理 toHom_apply
  条件: (f : 余py A B) (a : α)
  结论: ⇑f.toHom a = f a
  证明: rfl
-/
@[simp] lemma toHom_apply (f : Copy A B) (a : α) : ⇑f.toHom a = f a := rfl

/--
lemma `coe_mk` / 引理 `coe_mk`

English:
lemma coe_mk
  given: (f : A ->g B) (hf)
  statement: ⇑(.mk f hf : Copy A B) = f
  proof: rfl

中文:
引理 coe_mk
  条件: (f : A ->g B) (hf)
  结论: ⇑(.mk f hf : 余py A B) = f
  证明: rfl
-/
@[simp] lemma coe_mk (f : A ->g B) (hf) : ⇑(.mk f hf : Copy A B) = f := rfl

/--
Definition of `mapEdgeSet` / `mapEdgeSet` 的定义

English:
definition mapEdgeSet
  signature: (f : Copy A B)
  body: f.toHom.mapEdgeSet
  inj' := Hom.mapEdgeSet.injective f.toHom f.injective

中文:
定义 mapEdgeSet
  签名: (f : 余py A B)
  定义体: f.toHom.mapEdgeSet
  inj' := Hom.mapEdgeSet.injective f.toHom f.injective

Depends on / 依赖: f.toHom.mapEdgeSet, mapEdgeSet
-/
def mapEdgeSet (f : Copy A B) : A.edgeSet ↪ B.edgeSet where
  toFun := f.toHom.mapEdgeSet
  inj' := Hom.mapEdgeSet.injective f.toHom f.injective

/--
Definition of `mapNeighborSet` / `mapNeighborSet` 的定义

English:
definition mapNeighborSet
  signature: (f : Copy A B) (a : α)
  body: ⟨f v, f.toHom.apply_mem_neighborSet v.prop⟩
  inj' _ _ h := by
    rw [Subtype.mk_eq_mk] at h ⊢
    exact f.injective h

中文:
定义 mapNeighborSet
  签名: (f : 余py A B) (a : α)
  定义体: ⟨f v, f.toHom.apply_mem_neighborSet v.prop⟩
  inj' _ _ h := by
    rw [Subtype.mk_eq_mk] at h ⊢
    exact f.injective h

Depends on / 依赖: apply_mem_neighborSet, f.toHom.apply_mem_neighborSet, v.prop
-/
def mapNeighborSet (f : Copy A B) (a : α) :
    A.neighborSet a ↪ B.neighborSet (f a) where
  toFun v := ⟨f v, f.toHom.apply_mem_neighborSet v.prop⟩
  inj' _ _ h := by
    rw [Subtype.mk_eq_mk] at h ⊢
    exact f.injective h

/--
Definition of `toEmbedding` / `toEmbedding` 的定义

English:
definition toEmbedding
  signature: (f : Copy A B)
  body: ⟨f, f.injective⟩

中文:
定义 toEmbedding
  签名: (f : 余py A B)
  定义体: ⟨f, f.injective⟩

Depends on / 依赖: f.injective, injective
-/
def toEmbedding (f : Copy A B) : α ↪ β := ⟨f, f.injective⟩

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: (G : SimpleGraph V)
  body: ⟨Hom.id, Function.injective_id⟩

中文:
定义 id
  签名: (G : 简单图 V)
  定义体: ⟨Hom.id, Function.injective_id⟩
-/
@[refl] def id (G : SimpleGraph V) : Copy G G := ⟨Hom.id, Function.injective_id⟩

/--
lemma `coe_id` / 引理 `coe_id`

English:
lemma coe_id
  statement: ⇑(id G) = _root_.id
  proof: rfl

中文:
引理 coe_id
  结论: ⇑(id G) = _root_.id
  证明: rfl
-/
@[simp, norm_cast] lemma coe_id : ⇑(id G) = _root_.id := rfl

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (g : Copy B C) (f : Copy A B)
  body: by
  use g.toHom.comp f.toHom
  rw [Hom.coe_comp]
  exact g.injective.comp f.injective

@[simp]

中文:
定义 comp
  签名: (g : 余py B C) (f : 余py A B)
  定义体: by
  use g.toHom.comp f.toHom
  rw [Hom.coe_comp]
  exact g.injective.comp f.injective

@[simp]

Depends on / 依赖: Hom.coe_comp, coe_comp, f.injective, f.toHom, g.injective.comp, g.toHom.comp, injective
-/
def comp (g : Copy B C) (f : Copy A B) : Copy A C := by
  use g.toHom.comp f.toHom
  rw [Hom.coe_comp]
  exact g.injective.comp f.injective

@[simp]
/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: (g : Copy B C) (f : Copy A B) (a : α)
  statement: g.comp f a = g (f a)
  proof: RelHom.comp_apply g.toHom f.toHom a

中文:
定理 comp_apply
  条件: (g : 余py B C) (f : 余py A B) (a : α)
  结论: g.comp f a = g (f a)
  证明: RelHom.comp_apply g.toHom f.toHom a

Depends on / 依赖: RelHom, RelHom.comp_apply, comp_apply, f.toHom, g.toHom
-/
theorem comp_apply (g : Copy B C) (f : Copy A B) (a : α) : g.comp f a = g (f a) :=
  RelHom.comp_apply g.toHom f.toHom a

/--
Definition of `ofLE` / `ofLE` 的定义

English:
definition ofLE
  signature: (G₁ G₂ : SimpleGraph V) (h : G₁ <= G₂)
  body: ⟨Hom.ofLE h, Function.injective_id⟩

@[simp, norm_cast]

中文:
定义 ofLE
  签名: (G₁ G₂ : 简单图 V) (h : G₁ <= G₂)
  定义体: ⟨Hom.ofLE h, Function.injective_id⟩

@[simp, norm_cast]

Depends on / 依赖: Function, Function.injective_id, Hom.ofLE, injective_id
-/
def ofLE (G₁ G₂ : SimpleGraph V) (h : G₁ <= G₂) : Copy G₁ G₂ := ⟨Hom.ofLE h, Function.injective_id⟩

@[simp, norm_cast]
/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  given: (g : Copy B C) (f : Copy A B)
  statement: ⇑(g.comp f) = g ∘ f
  proof: by ext; simp

中文:
定理 coe_comp
  条件: (g : 余py B C) (f : 余py A B)
  结论: ⇑(g.comp f) = g ∘ f
  证明: by ext; simp
-/
theorem coe_comp (g : Copy B C) (f : Copy A B) : ⇑(g.comp f) = g ∘ f := by ext; simp

/--
lemma `coe_ofLE` / 引理 `coe_ofLE`

English:
lemma coe_ofLE
  given: (h : G₁ <= G₂)
  statement: ⇑(ofLE G₁ G₂ h) = _root_.id
  proof: rfl

中文:
引理 coe_ofLE
  条件: (h : G₁ <= G₂)
  结论: ⇑(ofLE G₁ G₂ h) = _root_.id
  证明: rfl
-/
@[simp, norm_cast] lemma coe_ofLE (h : G₁ <= G₂) : ⇑(ofLE G₁ G₂ h) = _root_.id := rfl

/--
theorem `ofLE_refl` / 定理 `ofLE_refl`

English:
theorem ofLE_refl
  statement: ofLE G G le_rfl = id G
  proof: by ext; simp

@[simp]

中文:
定理 ofLE_refl
  结论: ofLE G G le_rfl = id G
  证明: by ext; simp

@[simp]
-/
@[simp] theorem ofLE_refl : ofLE G G le_rfl = id G := by ext; simp

@[simp]
/--
theorem `ofLE_comp` / 定理 `ofLE_comp`

English:
theorem ofLE_comp
  given: (h₁₂ : G₁ <= G₂) (h₂₃ : G₂ <= G₃)
  proof: by ext; simp

中文:
定理 ofLE_comp
  条件: (h₁₂ : G₁ <= G₂) (h₂₃ : G₂ <= G₃)
  证明: by ext; simp
-/
theorem ofLE_comp (h₁₂ : G₁ <= G₂) (h₂₃ : G₂ <= G₃) :
    (ofLE _ _ h₂₃).comp (ofLE _ _ h₁₂) = ofLE _ _ (h₁₂.trans h₂₃) := by ext; simp

/--
Definition of `induce` / `induce` 的定义

English:
definition induce
  signature: (G : SimpleGraph V) (s : Set V)
  body: (Embedding.induce s).toCopy

中文:
定义 induce
  签名: (G : 简单图 V) (s : 集合 V)
  定义体: (Embedding.induce s).toCopy

Depends on / 依赖: Embedding, Embedding.induce, induce, toCopy
-/
def induce (G : SimpleGraph V) (s : Set V) : Copy (G.induce s) G := (Embedding.induce s).toCopy

/--
Definition of `bot` / `bot` 的定义

English:
definition bot
  signature: (f : α ↪ β)
  body: ⟨⟨f, False.elim⟩, f.injective⟩

中文:
定义 bot
  签名: (f : α ↪ β)
  定义体: ⟨⟨f, False.elim⟩, f.injective⟩
-/
protected def bot (f : α ↪ β) : Copy (⊥ : SimpleGraph α) B := ⟨⟨f, False.elim⟩, f.injective⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isoSubgraphMap` / `isoSubgraphMap` 的定义

English:
definition isoSubgraphMap
  signature: (f : Copy A B) (A' : A.Subgraph)
  body: by
  use Equiv.Set.image f.toHom _ f.injective
  simp_rw [Subgraph.map_verts, Equiv.Set.image_apply, Subgraph.coe_adj, Subgraph.map_adj,
    Relation.map_apply, f.injective.eq_iff, exists_eq_right_right, exists_eq_right, forall_true_iff]

中文:
定义 isoSubgraphMap
  签名: (f : 余py A B) (A' : A.子图)
  定义体: by
  use Equiv.Set.image f.toHom _ f.injective
  simp_rw [Subgraph.map_verts, Equiv.Set.image_apply, Subgraph.coe_adj, Subgraph.map_adj,
    Relation.map_apply, f.injective.eq_iff, exists_eq_right_right, exists_eq_right, forall_true_iff]

Depends on / 依赖: Equiv.Set.image, Equiv.Set.image_apply, Relation, Relation.map_apply, Subgraph, Subgraph.coe_adj, Subgraph.map_adj, Subgraph.map_verts, coe_adj, eq_iff, exists_eq_right, exists_eq_right_right, f.injective, f.injective.eq_iff, f.toHom, forall_true_iff, image_apply, injective, map_adj, map_apply
-/
noncomputable def isoSubgraphMap (f : Copy A B) (A' : A.Subgraph) :
    A'.coe ≃g (A'.map f.toHom).coe := by
  use Equiv.Set.image f.toHom _ f.injective
  simp_rw [Subgraph.map_verts, Equiv.Set.image_apply, Subgraph.coe_adj, Subgraph.map_adj,
    Relation.map_apply, f.injective.eq_iff, exists_eq_right_right, exists_eq_right, forall_true_iff]

/--
Definition of `toSubgraph` / `toSubgraph` 的定义

English:
abbreviation toSubgraph
  signature: (f : Copy A B)
  body: .map f.toHom ⊤

中文:
缩写 toSubgraph
  签名: (f : 余py A B)
  定义体: .map f.toHom ⊤

Depends on / 依赖: f.toHom
-/
abbrev toSubgraph (f : Copy A B) : B.Subgraph := .map f.toHom ⊤

/--
Definition of `isoToSubgraph` / `isoToSubgraph` 的定义

English:
definition isoToSubgraph
  signature: (f : Copy A B)
  body: (f.isoSubgraphMap ⊤).comp Subgraph.topIso.symm

中文:
定义 isoToSubgraph
  签名: (f : 余py A B)
  定义体: (f.isoSubgraphMap ⊤).comp Subgraph.topIso.symm

Depends on / 依赖: Subgraph, Subgraph.topIso.symm, f.isoSubgraphMap, isoSubgraphMap, topIso
-/
noncomputable def isoToSubgraph (f : Copy A B) : A ≃g f.toSubgraph.coe :=
  (f.isoSubgraphMap ⊤).comp Subgraph.topIso.symm

/--
lemma `range_toSubgraph` / 引理 `range_toSubgraph`

English:
lemma range_toSubgraph
  proof: by
  ext H'
  constructor
  · rintro ⟨f, hf, rfl⟩
    simpa [toSubgraph] using ⟨f.isoToSubgraph⟩
  · rintro ⟨e⟩
    refine ⟨⟨H'.hom.comp e.toHom, Subgraph.hom_injective.comp e.injective⟩, ?_⟩
    simp [toSubgraph, Subgraph.map_comp]

中文:
引理 range_toSubgraph
  证明: by
  ext H'
  constructor
  · rintro ⟨f, hf, rfl⟩
    simpa [toSubgraph] using ⟨f.isoToSubgraph⟩
  · rintro ⟨e⟩
    refine ⟨⟨H'.hom.comp e.toHom, Subgraph.hom_injective.comp e.injective⟩, ?_⟩
    simp [toSubgraph, Subgraph.map_comp]
-/
@[simp] lemma range_toSubgraph :
    .range (toSubgraph (A := A)) = {B' : B.Subgraph | Nonempty (A ≃g B'.coe)} := by
  ext H'
  constructor
  · rintro ⟨f, hf, rfl⟩
    simpa [toSubgraph] using ⟨f.isoToSubgraph⟩
  · rintro ⟨e⟩
    refine ⟨⟨H'.hom.comp e.toHom, Subgraph.hom_injective.comp e.injective⟩, ?_⟩
    simp [toSubgraph, Subgraph.map_comp]

/--
lemma `toSubgraph_surjOn` / 引理 `toSubgraph_surjOn`

English:
lemma toSubgraph_surjOn
  proof: fun H' hH' => by simpa

中文:
引理 toSubgraph_surjOn
  证明: fun H' hH' => by simpa

Depends on / 依赖: B.Subgraph, Nonempty, Subgraph
-/
lemma toSubgraph_surjOn :
    Set.SurjOn (toSubgraph (A := A)) .univ {B' : B.Subgraph | Nonempty (A ≃g B'.coe)} :=
  fun H' hH' => by simpa

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Subsingleton
  signature: (V -> W)] : Subsingleton (G.Copy H)
  body: DFunLike.coe_injective.subsingleton

中文:
实例 [子单例
  签名: (V -> W)] : 子单例 (G.余py H)
  定义体: DFunLike.coe_injective.subsingleton

Depends on / 依赖: DFunLike, DFunLike.coe_injective.subsingleton, coe_injective, subsingleton
-/
instance [Subsingleton (V -> W)] : Subsingleton (G.Copy H) := DFunLike.coe_injective.subsingleton

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Fintype
  signature: {f : G ->g H // Injective f}] : Fintype (G.Copy H)
  body: .ofEquiv {f : G ->g H // Injective f} {
    toFun f := ⟨f.1, f.2⟩
    invFun f := ⟨f.1, f.2⟩
  }

中文:
实例 [有限类型
  签名: {f : G ->g H // 单射 f}] : 有限类型 (G.余py H)
  定义体: .ofEquiv {f : G ->g H // Injective f} {
    toFun f := ⟨f.1, f.2⟩
    invFun f := ⟨f.1, f.2⟩
  }

Depends on / 依赖: Injective, invFun, ofEquiv
-/
instance [Fintype {f : G ->g H // Injective f}] : Fintype (G.Copy H) :=
  .ofEquiv {f : G ->g H // Injective f} {
    toFun f := ⟨f.1, f.2⟩
    invFun f := ⟨f.1, f.2⟩
  }

/-- A copy of `⊤` gives rise to an embedding of `⊤`. -/
@[simps!]
/--
Definition of `topEmbedding` / `topEmbedding` 的定义

English:
definition topEmbedding
  signature: (f : Copy (⊤ : SimpleGraph α) G)
  body: { f.toEmbedding with
    map_rel_iff' := fun {v w} => ⟨fun h => by simpa using h.ne, f.toHom.map_adj⟩}

中文:
定义 topEmbedding
  签名: (f : 余py (⊤ : 简单图 α) G)
  定义体: { f.toEmbedding with
    map_rel_iff' := fun {v w} => ⟨fun h => by simpa using h.ne, f.toHom.map_adj⟩}

Depends on / 依赖: f.toEmbedding, f.toHom.map_adj, h.ne, map_adj, map_rel_iff, toEmbedding
-/
def topEmbedding (f : Copy (⊤ : SimpleGraph α) G) : (⊤ : SimpleGraph α) ↪g G :=
  { f.toEmbedding with
    map_rel_iff' := fun {v w} => ⟨fun h => by simpa using h.ne, f.toHom.map_adj⟩}

end Copy

/--
Definition of `Subgraph.coeCopy` / `Subgraph.coeCopy` 的定义

English:
definition Subgraph.coeCopy
  signature: (G' : G.Subgraph)
  body: G'.hom.toCopy hom_injective

中文:
定义 子图.coeCopy
  签名: (G' : G.子图)
  定义体: G'.hom.toCopy hom_injective

Depends on / 依赖: hom.toCopy, hom_injective, toCopy
-/
def Subgraph.coeCopy (G' : G.Subgraph) : Copy G'.coe G := G'.hom.toCopy hom_injective

end Copy

/-!
#### Induced copies

An induced copy of a graph `G` inside a graph `H` is an embedding from the vertices of
`G` into the vertices of `H` which preserves the adjacency relation.

This is already captured by the notion of graph embeddings, defined as `G ↪g H`.

### Containment

#### Not necessarily induced containment

A graph `H` *contains* a graph `G` if there is some copy `f : Copy G H` of `G` inside `H`. This
amounts to `H` having a subgraph isomorphic to `G`.

We denote "`G` is contained in `H`" by `G ⊑ H` (`\squb`).
-/

section IsContained

/--
Definition of `IsContained` / `IsContained` 的定义

English:
abbreviation IsContained
  signature: (A : SimpleGraph α) (B : SimpleGraph β)
  body: Nonempty (Copy A B)

@[inherit_doc] scoped infixl:50 " ⊑ " => SimpleGraph.IsContained

中文:
缩写 IsContained
  签名: (A : 简单图 α) (B : 简单图 β)
  定义体: Nonempty (Copy A B)

@[inherit_doc] scoped infixl:50 " ⊑ " => SimpleGraph.IsContained

Depends on / 依赖: Nonempty
-/
abbrev IsContained (A : SimpleGraph α) (B : SimpleGraph β) := Nonempty (Copy A B)

@[inherit_doc] scoped infixl:50 " ⊑ " => SimpleGraph.IsContained

/--
theorem `IsContained.refl` / 定理 `IsContained.refl`

English:
theorem IsContained.refl
  given: (G : SimpleGraph V)
  statement: G ⊑ G
  proof: ⟨.id G⟩

中文:
定理 IsContained.refl
  条件: (G : 简单图 V)
  结论: G ⊑ G
  证明: ⟨.id G⟩
-/
@[refl] protected theorem IsContained.refl (G : SimpleGraph V) : G ⊑ G := ⟨.id G⟩

/--
theorem `IsContained.rfl` / 定理 `IsContained.rfl`

English:
theorem IsContained.rfl
  statement: G ⊑ G
  proof: IsContained.refl G

中文:
定理 IsContained.rfl
  结论: G ⊑ G
  证明: IsContained.refl G
-/
protected theorem IsContained.rfl : G ⊑ G := IsContained.refl G

/--
theorem `IsContained.of_le` / 定理 `IsContained.of_le`

English:
theorem IsContained.of_le
  given: (h : G₁ <= G₂)
  statement: G₁ ⊑ G₂
  proof: ⟨.ofLE G₁ G₂ h⟩

中文:
定理 IsContained.of_le
  条件: (h : G₁ <= G₂)
  结论: G₁ ⊑ G₂
  证明: ⟨.ofLE G₁ G₂ h⟩
-/
theorem IsContained.of_le (h : G₁ <= G₂) : G₁ ⊑ G₂ := ⟨.ofLE G₁ G₂ h⟩

/--
theorem `IsContained.trans` / 定理 `IsContained.trans`

English:
theorem IsContained.trans
  statement: A ⊑ B -> B ⊑ C -> A ⊑ C
  proof: fun ⟨f⟩ ⟨g⟩ => ⟨g.comp f⟩

中文:
定理 IsContained.trans
  结论: A ⊑ B -> B ⊑ C -> A ⊑ C
  证明: fun ⟨f⟩ ⟨g⟩ => ⟨g.comp f⟩

Depends on / 依赖: g.comp
-/
theorem IsContained.trans : A ⊑ B -> B ⊑ C -> A ⊑ C := fun ⟨f⟩ ⟨g⟩ => ⟨g.comp f⟩

/--
theorem `IsContained.trans'` / 定理 `IsContained.trans'`

English:
theorem IsContained.trans'
  statement: B ⊑ C -> A ⊑ B -> A ⊑ C
  proof: flip IsContained.trans

@[gcongr]

中文:
定理 IsContained.trans'
  结论: B ⊑ C -> A ⊑ B -> A ⊑ C
  证明: flip IsContained.trans

@[gcongr]

Depends on / 依赖: IsContained, IsContained.trans
-/
theorem IsContained.trans' : B ⊑ C -> A ⊑ B -> A ⊑ C := flip IsContained.trans

@[gcongr]
/--
lemma `IsContained.mono_right` / 引理 `IsContained.mono_right`

English:
lemma IsContained.mono_right
  given: {B' : SimpleGraph β} (h_isub : A ⊑ B) (h_sub : B <= B')
  statement: A ⊑ B'
  proof: h_isub.trans IsContained.of_le h_sub

alias IsContained.trans_le := IsContained.mono_right

@[gcongr]

中文:
引理 IsContained.mono_right
  条件: {B' : 简单图 β} (h_isub : A ⊑ B) (h_sub : B <= B')
  结论: A ⊑ B'
  证明: h_isub.trans IsContained.of_le h_sub

alias IsContained.trans_le := IsContained.mono_right

@[gcongr]

Depends on / 依赖: IsContained, IsContained.of_le, h_isub, h_isub.trans, h_sub, of_le
-/
lemma IsContained.mono_right {B' : SimpleGraph β} (h_isub : A ⊑ B) (h_sub : B <= B') : A ⊑ B' :=
h_isub.trans IsContained.of_le h_sub

alias IsContained.trans_le := IsContained.mono_right

@[gcongr]
/--
lemma `IsContained.mono_left` / 引理 `IsContained.mono_left`

English:
lemma IsContained.mono_left
  given: {A' : SimpleGraph α} (h_sub : A <= A') (h_isub : A' ⊑ B)
  statement: A ⊑ B
  proof: (IsContained.of_le h_sub).trans h_isub

alias IsContained.trans_le' := IsContained.mono_left

中文:
引理 IsContained.mono_left
  条件: {A' : 简单图 α} (h_sub : A <= A') (h_isub : A' ⊑ B)
  结论: A ⊑ B
  证明: (IsContained.of_le h_sub).trans h_isub

alias IsContained.trans_le' := IsContained.mono_left

Depends on / 依赖: IsContained, IsContained.of_le, h_isub, h_sub, of_le
-/
lemma IsContained.mono_left {A' : SimpleGraph α} (h_sub : A <= A') (h_isub : A' ⊑ B) : A ⊑ B :=
  (IsContained.of_le h_sub).trans h_isub

alias IsContained.trans_le' := IsContained.mono_left

/--
theorem `isContained_congr` / 定理 `isContained_congr`

English:
theorem isContained_congr
  given: (e₁ : A ≃g H) (e₂ : B ≃g G)
  statement: A ⊑ B ↔ H ⊑ G
  proof: ⟨.trans' ⟨e₂.toCopy⟩ ∘ .trans ⟨e₁.symm.toCopy⟩, .trans' ⟨e₂.symm.toCopy⟩ ∘ .trans ⟨e₁.toCopy⟩⟩

中文:
定理 isContained_congr
  条件: (e₁ : A ≃g H) (e₂ : B ≃g G)
  结论: A ⊑ B ↔ H ⊑ G
  证明: ⟨.trans' ⟨e₂.toCopy⟩ ∘ .trans ⟨e₁.symm.toCopy⟩, .trans' ⟨e₂.symm.toCopy⟩ ∘ .trans ⟨e₁.toCopy⟩⟩

Depends on / 依赖: symm.toCopy, toCopy
-/
theorem isContained_congr (e₁ : A ≃g H) (e₂ : B ≃g G) : A ⊑ B ↔ H ⊑ G :=
  ⟨.trans' ⟨e₂.toCopy⟩ ∘ .trans ⟨e₁.symm.toCopy⟩, .trans' ⟨e₂.symm.toCopy⟩ ∘ .trans ⟨e₁.toCopy⟩⟩

/--
lemma `isContained_congr_left` / 引理 `isContained_congr_left`

English:
lemma isContained_congr_left
  given: (e₁ : A ≃g B)
  statement: A ⊑ C ↔ B ⊑ C
  proof: isContained_congr e₁ .refl

alias ⟨_, IsContained.congr_left⟩ := isContained_congr_left

中文:
引理 isContained_congr_left
  条件: (e₁ : A ≃g B)
  结论: A ⊑ C ↔ B ⊑ C
  证明: isContained_congr e₁ .refl

alias ⟨_, IsContained.congr_left⟩ := isContained_congr_left

Depends on / 依赖: isContained_congr
-/
lemma isContained_congr_left (e₁ : A ≃g B) : A ⊑ C ↔ B ⊑ C := isContained_congr e₁ .refl

alias ⟨_, IsContained.congr_left⟩ := isContained_congr_left

/--
lemma `isContained_congr_right` / 引理 `isContained_congr_right`

English:
lemma isContained_congr_right
  given: (e₂ : B ≃g C)
  statement: A ⊑ B ↔ A ⊑ C
  proof: isContained_congr .refl e₂

alias ⟨_, IsContained.congr_right⟩ := isContained_congr_right

中文:
引理 isContained_congr_right
  条件: (e₂ : B ≃g C)
  结论: A ⊑ B ↔ A ⊑ C
  证明: isContained_congr .refl e₂

alias ⟨_, IsContained.congr_right⟩ := isContained_congr_right

Depends on / 依赖: isContained_congr
-/
lemma isContained_congr_right (e₂ : B ≃g C) : A ⊑ B ↔ A ⊑ C := isContained_congr .refl e₂

alias ⟨_, IsContained.congr_right⟩ := isContained_congr_right

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsPreorder (SimpleGraph α) IsContained
  body: .refl
  trans _ _ _ := .trans

中文:
实例 :
  签名: 是预序 (简单图 α) IsContained
  定义体: .refl
  trans _ _ _ := .trans
-/
instance : IsPreorder (SimpleGraph α) IsContained where
  refl := .refl
  trans _ _ _ := .trans

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  body: .trans

中文:
实例 :
  定义体: .trans

Depends on / 依赖: SimpleGraph
-/
instance :
    Trans (α := SimpleGraph α) (β := SimpleGraph β) (γ := SimpleGraph γ)
      IsContained IsContained IsContained where
  trans := .trans

/--
lemma `IsContained.of_isEmpty` / 引理 `IsContained.of_isEmpty`

English:
lemma IsContained.of_isEmpty
  given: [IsEmpty α]
  statement: A ⊑ B
  proof: ⟨⟨isEmptyElim, fun {a} => isEmptyElim a⟩, isEmptyElim⟩

中文:
引理 IsContained.of_isEmpty
  条件: [是空 α]
  结论: A ⊑ B
  证明: ⟨⟨isEmptyElim, fun {a} => isEmptyElim a⟩, isEmptyElim⟩

Depends on / 依赖: isEmptyElim
-/
lemma IsContained.of_isEmpty [IsEmpty α] : A ⊑ B :=
  ⟨⟨isEmptyElim, fun {a} => isEmptyElim a⟩, isEmptyElim⟩

/--
lemma `bot_isContained_iff_card_le` / 引理 `bot_isContained_iff_card_le`

English:
lemma bot_isContained_iff_card_le
  given: [Fintype α] [Fintype β]
  proof: ⟨fun ⟨f⟩ => Fintype.card_le_of_embedding f.toEmbedding,
    fun h => ⟨Copy.bot (Function.Embedding.nonempty_of_card_le h).some⟩⟩

protected alias IsContained.bot := bot_isContained_iff_card_le

中文:
引理 bot_isContained_iff_card_le
  条件: [有限类型 α] [有限类型 β]
  证明: ⟨fun ⟨f⟩ => Fintype.card_le_of_embedding f.toEmbedding,
    fun h => ⟨Copy.bot (Function.Embedding.nonempty_of_card_le h).some⟩⟩

protected alias IsContained.bot := bot_isContained_iff_card_le

Depends on / 依赖: Copy.bot, Embedding, Fintype, Fintype.card_le_of_embedding, Function, Function.Embedding.nonempty_of_card_le, card_le_of_embedding, f.toEmbedding, nonempty_of_card_le, toEmbedding
-/
lemma bot_isContained_iff_card_le [Fintype α] [Fintype β] :
    (⊥ : SimpleGraph α) ⊑ B ↔ Fintype.card α <= Fintype.card β :=
  ⟨fun ⟨f⟩ => Fintype.card_le_of_embedding f.toEmbedding,
    fun h => ⟨Copy.bot (Function.Embedding.nonempty_of_card_le h).some⟩⟩

protected alias IsContained.bot := bot_isContained_iff_card_le

/--
lemma `Subgraph.coe_isContained` / 引理 `Subgraph.coe_isContained`

English:
lemma Subgraph.coe_isContained
  given: (G' : G.Subgraph)
  statement: G'.coe ⊑ G
  proof: ⟨G'.coeCopy⟩

中文:
引理 子图.coe_isContained
  条件: (G' : G.子图)
  结论: G'.coe ⊑ G
  证明: ⟨G'.coeCopy⟩

Depends on / 依赖: coeCopy
-/
lemma Subgraph.coe_isContained (G' : G.Subgraph) : G'.coe ⊑ G := ⟨G'.coeCopy⟩

/--
theorem `isContained_iff_exists_iso_subgraph` / 定理 `isContained_iff_exists_iso_subgraph`

English:
theorem isContained_iff_exists_iso_subgraph
  proof: fun ⟨f⟩ => ⟨.map f.toHom ⊤, ⟨f.isoToSubgraph⟩⟩
  mpr := fun ⟨B', ⟨e⟩⟩ => B'.coe_isContained.trans' ⟨e.toCopy⟩

alias ⟨IsContained.exists_iso_subgraph, IsContained.of_exists_iso_subgraph⟩ :=
  isContained_iff_exists_iso_subgraph

中文:
定理 isContained_iff_存在_iso_subgraph
  证明: fun ⟨f⟩ => ⟨.map f.toHom ⊤, ⟨f.isoToSubgraph⟩⟩
  mpr := fun ⟨B', ⟨e⟩⟩ => B'.coe_isContained.trans' ⟨e.toCopy⟩

alias ⟨IsContained.exists_iso_subgraph, IsContained.of_exists_iso_subgraph⟩ :=
  isContained_iff_exists_iso_subgraph

Depends on / 依赖: f.isoToSubgraph, f.toHom, isoToSubgraph
-/
theorem isContained_iff_exists_iso_subgraph :
    A ⊑ B ↔ exists B' : B.Subgraph, Nonempty (A ≃g B'.coe) where
  mp := fun ⟨f⟩ => ⟨.map f.toHom ⊤, ⟨f.isoToSubgraph⟩⟩
  mpr := fun ⟨B', ⟨e⟩⟩ => B'.coe_isContained.trans' ⟨e.toCopy⟩

alias ⟨IsContained.exists_iso_subgraph, IsContained.of_exists_iso_subgraph⟩ :=
  isContained_iff_exists_iso_subgraph

/--
theorem `Copy.degree_le` / 定理 `Copy.degree_le`

English:
theorem Copy.degree_le
  statement: (f : Copy G H) (v : V) [Fintype <| G.neighborSet v]
  proof: by
  simpa [card_neighborSet_eq_degree] using
    Fintype.card_le_of_injective _ (f.mapNeighborSet v).injective

中文:
定理 余py.degree_le
  结论: (f : 余py G H) (v : V) [有限类型 <| G.neighborSet v]
  证明: by
  simpa [card_neighborSet_eq_degree] using
    Fintype.card_le_of_injective _ (f.mapNeighborSet v).injective

Depends on / 依赖: Fintype, Fintype.card_le_of_injective, card_le_of_injective, card_neighborSet_eq_degree, f.mapNeighborSet, injective, mapNeighborSet
-/
theorem Copy.degree_le (f : Copy G H) (v : V) [Fintype <| G.neighborSet v]
    [Fintype <| H.neighborSet (f v)] : G.degree v <= H.degree (f v) := by
  simpa [card_neighborSet_eq_degree] using
    Fintype.card_le_of_injective _ (f.mapNeighborSet v).injective

/--
theorem `Copy.maxDegree_mono` / 定理 `Copy.maxDegree_mono`

English:
theorem Copy.maxDegree_mono
  statement: [Fintype V] [Fintype W] [DecidableRel G.Adj] [DecidableRel H.Adj]
  proof: by
  cases isEmpty_or_nonempty V
  · simp
  obtain ⟨v, h⟩ := exists_maximal_degree_vertex G
  grind [degree_le_maxDegree H (f v), f.degree_le v]

@[deprecated (since := "2026-05-20")] alias Copy.max_degree_le := Copy.maxDegree_mono

中文:
定理 余py.maxDegree_mono
  结论: [有限类型 V] [有限类型 W] [DecidableRel G.伴随] [DecidableRel H.伴随]
  证明: by
  cases isEmpty_or_nonempty V
  · simp
  obtain ⟨v, h⟩ := exists_maximal_degree_vertex G
  grind [degree_le_maxDegree H (f v), f.degree_le v]

@[deprecated (since := "2026-05-20")] alias Copy.max_degree_le := Copy.maxDegree_mono

Depends on / 依赖: degree_le, degree_le_maxDegree, exists_maximal_degree_vertex, f.degree_le, isEmpty_or_nonempty
-/
theorem Copy.maxDegree_mono [Fintype V] [Fintype W] [DecidableRel G.Adj] [DecidableRel H.Adj]
    (f : Copy G H) : G.maxDegree <= H.maxDegree := by
  cases isEmpty_or_nonempty V
  · simp
  obtain ⟨v, h⟩ := exists_maximal_degree_vertex G
  grind [degree_le_maxDegree H (f v), f.degree_le v]

@[deprecated (since := "2026-05-20")] alias Copy.max_degree_le := Copy.maxDegree_mono

/--
theorem `IsContained.maxDegree_mono` / 定理 `IsContained.maxDegree_mono`

English:
theorem IsContained.maxDegree_mono
  statement: [Fintype V] [Fintype W] [DecidableRel G.Adj] [DecidableRel H.Adj]
  proof: by
  have ⟨f⟩ := h
  exact f.maxDegree_mono

@[deprecated (since := "2026-05-20")] alias IsContained.max_degree_le := IsContained.maxDegree_mono

@[gcongr]

中文:
定理 IsContained.maxDegree_mono
  结论: [有限类型 V] [有限类型 W] [DecidableRel G.伴随] [DecidableRel H.伴随]
  证明: by
  have ⟨f⟩ := h
  exact f.maxDegree_mono

@[deprecated (since := "2026-05-20")] alias IsContained.max_degree_le := IsContained.maxDegree_mono

@[gcongr]

Depends on / 依赖: f.maxDegree_mono, maxDegree_mono
-/
theorem IsContained.maxDegree_mono [Fintype V] [Fintype W] [DecidableRel G.Adj] [DecidableRel H.Adj]
    (h : G ⊑ H) : G.maxDegree <= H.maxDegree := by
  have ⟨f⟩ := h
  exact f.maxDegree_mono

@[deprecated (since := "2026-05-20")] alias IsContained.max_degree_le := IsContained.maxDegree_mono

@[gcongr]
/--
lemma `maxDegree_mono` / 引理 `maxDegree_mono`

English:
lemma maxDegree_mono
  statement: {H : SimpleGraph V} [Fintype V] [DecidableRel G.Adj] [DecidableRel H.Adj]
  proof: .maxDegree_mono IsContained.of_le hle

中文:
引理 maxDegree_mono
  结论: {H : 简单图 V} [有限类型 V] [DecidableRel G.伴随] [DecidableRel H.伴随]
  证明: .maxDegree_mono IsContained.of_le hle

Depends on / 依赖: IsContained, IsContained.of_le, maxDegree_mono, of_le
-/
lemma maxDegree_mono {H : SimpleGraph V} [Fintype V] [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hle : G <= H) : G.maxDegree <= H.maxDegree :=
.maxDegree_mono IsContained.of_le hle

/--
theorem `Copy.minDegree_mono` / 定理 `Copy.minDegree_mono`

English:
theorem Copy.minDegree_mono
  statement: [Fintype V] [Fintype W] [DecidableRel G.Adj] [DecidableRel H.Adj]
  proof: by
  cases isEmpty_or_nonempty W
  · have := Function.isEmpty f
    simp
  refine H.le_minDegree_of_forall_le_degree _ fun w => ?_
  obtain ⟨v, rfl⟩ := hf w
  grw [← f.degree_le, ← minDegree_le_degree]

@[deprecated (since := "2026-05-20")] alias Copy.minDegree_le := Copy.minDegree_mono

中文:
定理 余py.minDegree_mono
  结论: [有限类型 V] [有限类型 W] [DecidableRel G.伴随] [DecidableRel H.伴随]
  证明: by
  cases isEmpty_or_nonempty W
  · have := Function.isEmpty f
    simp
  refine H.le_minDegree_of_forall_le_degree _ fun w => ?_
  obtain ⟨v, rfl⟩ := hf w
  grw [← f.degree_le, ← minDegree_le_degree]

@[deprecated (since := "2026-05-20")] alias Copy.minDegree_le := Copy.minDegree_mono

Depends on / 依赖: Function, Function.isEmpty, H.le_minDegree_of_forall_le_degree, degree_le, f.degree_le, isEmpty, isEmpty_or_nonempty, le_minDegree_of_forall_le_degree, minDegree_le_degree
-/
theorem Copy.minDegree_mono [Fintype V] [Fintype W] [DecidableRel G.Adj] [DecidableRel H.Adj]
    {f : Copy G H} (hf : Function.Surjective f) : G.minDegree <= H.minDegree := by
  cases isEmpty_or_nonempty W
  · have := Function.isEmpty f
    simp
  refine H.le_minDegree_of_forall_le_degree _ fun w => ?_
  obtain ⟨v, rfl⟩ := hf w
  grw [← f.degree_le, ← minDegree_le_degree]

@[deprecated (since := "2026-05-20")] alias Copy.minDegree_le := Copy.minDegree_mono

/--
theorem `Hom.minDegree_mono` / 定理 `Hom.minDegree_mono`

English:
theorem Hom.minDegree_mono
  statement: [Fintype V] [Fintype W] [DecidableRel G.Adj] [DecidableRel H.Adj]
  proof: Copy.minDegree_mono (f := ⟨f, hf.injective⟩) hf.surjective

@[deprecated (since := "2026-05-20")] alias Hom.minDegree_le := Hom.minDegree_mono

中文:
定理 态射.minDegree_mono
  结论: [有限类型 V] [有限类型 W] [DecidableRel G.伴随] [DecidableRel H.伴随]
  证明: Copy.minDegree_mono (f := ⟨f, hf.injective⟩) hf.surjective

@[deprecated (since := "2026-05-20")] alias Hom.minDegree_le := Hom.minDegree_mono

Depends on / 依赖: Copy.minDegree_mono, hf.injective, hf.surjective, injective, minDegree_mono, surjective
-/
theorem Hom.minDegree_mono [Fintype V] [Fintype W] [DecidableRel G.Adj] [DecidableRel H.Adj]
    {f : G ->g H} (hf : Function.Bijective f) : G.minDegree <= H.minDegree :=
  Copy.minDegree_mono (f := ⟨f, hf.injective⟩) hf.surjective

@[deprecated (since := "2026-05-20")] alias Hom.minDegree_le := Hom.minDegree_mono

/--
theorem `maxDegree_induce_of_support_subset` / 定理 `maxDegree_induce_of_support_subset`

English:
theorem maxDegree_induce_of_support_subset
  statement: [Fintype V] [DecidableRel G.Adj] {s : Set V}
  proof: by
apply le_antisymm Copy.maxDegree_mono .toCopy Embedding.induce s
  refine G.maxDegree_le_of_forall_degree_le _ fun v => ?_
  by_cases hv : G.IsIsolated v
  · simp [hv]
  grw [← degree_le_maxDegree _ ⟨v, h <| G.mem_support_iff_not_isIsolated.mpr hv⟩,
degree_induce_of_neighborSet_subset .trans h] G.neighborSet_subset_support v

中文:
定理 maxDegree_induce_of_support_subset
  结论: [有限类型 V] [DecidableRel G.伴随] {s : 集合 V}
  证明: by
apply le_antisymm Copy.maxDegree_mono .toCopy Embedding.induce s
  refine G.maxDegree_le_of_forall_degree_le _ fun v => ?_
  by_cases hv : G.IsIsolated v
  · simp [hv]
  grw [← degree_le_maxDegree _ ⟨v, h <| G.mem_support_iff_not_isIsolated.mpr hv⟩,
degree_induce_of_neighborSet_subset .trans h] G.neighborSet_subset_support v

Depends on / 依赖: Copy.maxDegree_mono, Embedding, Embedding.induce, G.IsIsolated, G.maxDegree_le_of_forall_degree_le, G.mem_support_iff_not_isIsolated.mpr, G.neighborSet_subset_support, IsIsolated, degree_induce_of_neighborSet_subset, degree_le_maxDegree, induce, le_antisymm, maxDegree_le_of_forall_degree_le, maxDegree_mono, mem_support_iff_not_isIsolated, neighborSet_subset_support, toCopy
-/
theorem maxDegree_induce_of_support_subset [Fintype V] [DecidableRel G.Adj] {s : Set V}
    [DecidablePred (· in s)] (h : G.support subseteq s) : (G.induce s).maxDegree = G.maxDegree := by
apply le_antisymm Copy.maxDegree_mono .toCopy Embedding.induce s
  refine G.maxDegree_le_of_forall_degree_le _ fun v => ?_
  by_cases hv : G.IsIsolated v
  · simp [hv]
  grw [← degree_le_maxDegree _ ⟨v, h <| G.mem_support_iff_not_isIsolated.mpr hv⟩,
degree_induce_of_neighborSet_subset .trans h] G.neighborSet_subset_support v

end IsContained

section Free

/--
Definition of `Free` / `Free` 的定义

English:
abbreviation Free
  signature: (A : SimpleGraph α) (B : SimpleGraph β)
  body: ¬A ⊑ B

中文:
缩写 自由
  签名: (A : 简单图 α) (B : 简单图 β)
  定义体: ¬A ⊑ B
-/
abbrev Free (A : SimpleGraph α) (B : SimpleGraph β) := ¬A ⊑ B

/--
lemma `not_free` / 引理 `not_free`

English:
lemma not_free
  statement: ¬A.Free B ↔ A ⊑ B
  proof: not_not

中文:
引理 not_free
  结论: ¬A.自由 B ↔ A ⊑ B
  证明: not_not

Depends on / 依赖: not_not
-/
lemma not_free : ¬A.Free B ↔ A ⊑ B := not_not

/--
theorem `free_congr` / 定理 `free_congr`

English:
theorem free_congr
  given: (e₁ : A ≃g H) (e₂ : B ≃g G)
  statement: A.Free B ↔ H.Free G
  proof: (isContained_congr e₁ e₂).not

中文:
定理 free_congr
  条件: (e₁ : A ≃g H) (e₂ : B ≃g G)
  结论: A.自由 B ↔ H.自由 G
  证明: (isContained_congr e₁ e₂).not

Depends on / 依赖: isContained_congr
-/
theorem free_congr (e₁ : A ≃g H) (e₂ : B ≃g G) : A.Free B ↔ H.Free G :=
  (isContained_congr e₁ e₂).not

/--
lemma `free_congr_left` / 引理 `free_congr_left`

English:
lemma free_congr_left
  given: (e₁ : A ≃g B)
  statement: A.Free C ↔ B.Free C
  proof: free_congr e₁ .refl

alias ⟨_, Free.congr_left⟩ := free_congr_left

中文:
引理 free_congr_left
  条件: (e₁ : A ≃g B)
  结论: A.自由 C ↔ B.自由 C
  证明: free_congr e₁ .refl

alias ⟨_, Free.congr_left⟩ := free_congr_left

Depends on / 依赖: free_congr
-/
lemma free_congr_left (e₁ : A ≃g B) : A.Free C ↔ B.Free C := free_congr e₁ .refl

alias ⟨_, Free.congr_left⟩ := free_congr_left

/--
lemma `free_congr_right` / 引理 `free_congr_right`

English:
lemma free_congr_right
  given: (e₂ : B ≃g C)
  statement: A.Free B ↔ A.Free C
  proof: free_congr .refl e₂

alias ⟨_, Free.congr_right⟩ := free_congr_right

中文:
引理 free_congr_right
  条件: (e₂ : B ≃g C)
  结论: A.自由 B ↔ A.自由 C
  证明: free_congr .refl e₂

alias ⟨_, Free.congr_right⟩ := free_congr_right

Depends on / 依赖: free_congr
-/
lemma free_congr_right (e₂ : B ≃g C) : A.Free B ↔ A.Free C := free_congr .refl e₂

alias ⟨_, Free.congr_right⟩ := free_congr_right

/--
lemma `free_bot` / 引理 `free_bot`

English:
lemma free_bot
  given: (h : A != ⊥)
  statement: A.Free (⊥ : SimpleGraph β)
  proof: by
  rw [← edgeSet_nonempty] at h
  intro ⟨f, hf⟩
  absurd f.map_mem_edgeSet h.choose_spec
  rw [edgeSet_bot]
  exact Set.notMem_empty (h.choose.map f)

中文:
引理 free_bot
  条件: (h : A != ⊥)
  结论: A.自由 (⊥ : 简单图 β)
  证明: by
  rw [← edgeSet_nonempty] at h
  intro ⟨f, hf⟩
  absurd f.map_mem_edgeSet h.choose_spec
  rw [edgeSet_bot]
  exact Set.notMem_empty (h.choose.map f)

Depends on / 依赖: Set.notMem_empty, absurd, choose_spec, edgeSet_bot, edgeSet_nonempty, f.map_mem_edgeSet, h.choose.map, h.choose_spec, map_mem_edgeSet, notMem_empty
-/
lemma free_bot (h : A != ⊥) : A.Free (⊥ : SimpleGraph β) := by
  rw [← edgeSet_nonempty] at h
  intro ⟨f, hf⟩
  absurd f.map_mem_edgeSet h.choose_spec
  rw [edgeSet_bot]
  exact Set.notMem_empty (h.choose.map f)

end Free

/-!
#### Induced containment

A graph `H` *inducingly contains* a graph `G` if there is some graph embedding `G ↪ H`. This amounts
to `H` having an induced subgraph isomorphic to `G`.

We denote "`G` is inducingly contained in `H`" by `G ⊴ H` (`\trianglelefteq`).
-/

/--
Definition of `IsIndContained` / `IsIndContained` 的定义

English:
definition IsIndContained
  signature: (G : SimpleGraph V) (H : SimpleGraph W)
  body: Nonempty (G ↪g H)

@[inherit_doc] scoped infixl:50 " ⊴ " => SimpleGraph.IsIndContained

中文:
定义 IsIndContained
  签名: (G : 简单图 V) (H : 简单图 W)
  定义体: Nonempty (G ↪g H)

@[inherit_doc] scoped infixl:50 " ⊴ " => SimpleGraph.IsIndContained

Depends on / 依赖: Nonempty
-/
def IsIndContained (G : SimpleGraph V) (H : SimpleGraph W) : Prop := Nonempty (G ↪g H)

@[inherit_doc] scoped infixl:50 " ⊴ " => SimpleGraph.IsIndContained

/--
lemma `Copy.isContained` / 引理 `Copy.isContained`

English:
lemma Copy.isContained
  given: (f : Copy G H)
  statement: G ⊑ H
  proof: ⟨f⟩

中文:
引理 余py.isContained
  条件: (f : 余py G H)
  结论: G ⊑ H
  证明: ⟨f⟩
-/
protected lemma Copy.isContained (f : Copy G H) : G ⊑ H := ⟨f⟩

/--
lemma `Embedding.isIndContained` / 引理 `Embedding.isIndContained`

English:
lemma Embedding.isIndContained
  given: (f : G ↪g H)
  statement: G ⊴ H
  proof: ⟨f⟩

中文:
引理 嵌入.isIndContained
  条件: (f : G ↪g H)
  结论: G ⊴ H
  证明: ⟨f⟩
-/
protected lemma Embedding.isIndContained (f : G ↪g H) : G ⊴ H := ⟨f⟩

/--
lemma `Embedding.isContained` / 引理 `Embedding.isContained`

English:
lemma Embedding.isContained
  given: (f : G ↪g H)
  statement: G ⊑ H
  proof: f.toCopy.isContained

中文:
引理 嵌入.isContained
  条件: (f : G ↪g H)
  结论: G ⊑ H
  证明: f.toCopy.isContained
-/
protected lemma Embedding.isContained (f : G ↪g H) : G ⊑ H := f.toCopy.isContained

/--
lemma `IsIndContained.isContained` / 引理 `IsIndContained.isContained`

English:
lemma IsIndContained.isContained
  statement: G ⊴ H -> G ⊑ H
  proof: fun ⟨f⟩ => f.isContained

中文:
引理 IsIndContained.isContained
  结论: G ⊴ H -> G ⊑ H
  证明: fun ⟨f⟩ => f.isContained
-/
protected lemma IsIndContained.isContained : G ⊴ H -> G ⊑ H := fun ⟨f⟩ => f.isContained

/--
lemma `Iso.isContained` / 引理 `Iso.isContained`

English:
lemma Iso.isContained
  given: (e : G ≃g H)
  statement: G ⊑ H
  proof: e.toCopy.isContained

中文:
引理 同构.isContained
  条件: (e : G ≃g H)
  结论: G ⊑ H
  证明: e.toCopy.isContained
-/
protected lemma Iso.isContained (e : G ≃g H) : G ⊑ H := e.toCopy.isContained

/--
lemma `Iso.isContained'` / 引理 `Iso.isContained'`

English:
lemma Iso.isContained'
  given: (e : G ≃g H)
  statement: H ⊑ G
  proof: e.symm.isContained

中文:
引理 同构.isContained'
  条件: (e : G ≃g H)
  结论: H ⊑ G
  证明: e.symm.isContained
-/
protected lemma Iso.isContained' (e : G ≃g H) : H ⊑ G := e.symm.isContained

/--
lemma `Iso.isIndContained` / 引理 `Iso.isIndContained`

English:
lemma Iso.isIndContained
  given: (e : G ≃g H)
  statement: G ⊴ H
  proof: e.toEmbedding.isIndContained

中文:
引理 同构.isIndContained
  条件: (e : G ≃g H)
  结论: G ⊴ H
  证明: e.toEmbedding.isIndContained
-/
protected lemma Iso.isIndContained (e : G ≃g H) : G ⊴ H := e.toEmbedding.isIndContained

/--
lemma `Iso.isIndContained'` / 引理 `Iso.isIndContained'`

English:
lemma Iso.isIndContained'
  given: (e : G ≃g H)
  statement: H ⊴ G
  proof: e.symm.isIndContained

中文:
引理 同构.isIndContained'
  条件: (e : G ≃g H)
  结论: H ⊴ G
  证明: e.symm.isIndContained
-/
protected lemma Iso.isIndContained' (e : G ≃g H) : H ⊴ G := e.symm.isIndContained

/--
lemma `Subgraph.IsInduced.isIndContained` / 引理 `Subgraph.IsInduced.isIndContained`

English:
lemma Subgraph.IsInduced.isIndContained
  given: {G' : G.Subgraph} (hG' : G'.IsInduced)
  proof: ⟨{ toFun := (↑)
     inj' := Subtype.coe_injective
     map_rel_iff' := hG'.adj.symm }⟩

中文:
引理 子图.是Induced.isIndContained
  条件: {G' : G.子图} (hG' : G'.是Induced)
  证明: ⟨{ toFun := (↑)
     inj' := Subtype.coe_injective
     map_rel_iff' := hG'.adj.symm }⟩
-/
protected lemma Subgraph.IsInduced.isIndContained {G' : G.Subgraph} (hG' : G'.IsInduced) :
    G'.coe ⊴ G :=
  ⟨{ toFun := (↑)
     inj' := Subtype.coe_injective
     map_rel_iff' := hG'.adj.symm }⟩

/--
lemma `IsIndContained.refl` / 引理 `IsIndContained.refl`

English:
lemma IsIndContained.refl
  given: (G : SimpleGraph V)
  statement: G ⊴ G
  proof: ⟨Embedding.refl⟩

中文:
引理 IsIndContained.refl
  条件: (G : 简单图 V)
  结论: G ⊴ G
  证明: ⟨Embedding.refl⟩
-/
@[refl] lemma IsIndContained.refl (G : SimpleGraph V) : G ⊴ G := ⟨Embedding.refl⟩
/--
lemma `IsIndContained.rfl` / 引理 `IsIndContained.rfl`

English:
lemma IsIndContained.rfl
  statement: G ⊴ G
  proof: .refl _

中文:
引理 IsIndContained.rfl
  结论: G ⊴ G
  证明: .refl _
-/
lemma IsIndContained.rfl : G ⊴ G := .refl _
/--
lemma `IsIndContained.trans` / 引理 `IsIndContained.trans`

English:
lemma IsIndContained.trans
  statement: G ⊴ H -> H ⊴ I -> G ⊴ I
  proof: fun ⟨f⟩ ⟨g⟩ => ⟨g.comp f⟩

中文:
引理 IsIndContained.trans
  结论: G ⊴ H -> H ⊴ I -> G ⊴ I
  证明: fun ⟨f⟩ ⟨g⟩ => ⟨g.comp f⟩
-/
@[trans] lemma IsIndContained.trans : G ⊴ H -> H ⊴ I -> G ⊴ I := fun ⟨f⟩ ⟨g⟩ => ⟨g.comp f⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsPreorder (SimpleGraph α) IsIndContained
  body: .refl
  trans _ _ _ := .trans

中文:
实例 :
  签名: 是预序 (简单图 α) IsIndContained
  定义体: .refl
  trans _ _ _ := .trans
-/
instance : IsPreorder (SimpleGraph α) IsIndContained where
  refl := .refl
  trans _ _ _ := .trans

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  body: .trans

中文:
实例 :
  定义体: .trans

Depends on / 依赖: SimpleGraph
-/
instance :
    Trans (α := SimpleGraph α) (β := SimpleGraph β) (γ := SimpleGraph γ)
      IsIndContained IsIndContained IsIndContained where
  trans := .trans

/--
lemma `IsIndContained.of_isEmpty` / 引理 `IsIndContained.of_isEmpty`

English:
lemma IsIndContained.of_isEmpty
  given: [IsEmpty V]
  statement: G ⊴ H
  proof: ⟨{ toFun := isEmptyElim
     inj' := isEmptyElim
     map_rel_iff' := fun {a} => isEmptyElim a }⟩

中文:
引理 IsIndContained.of_isEmpty
  条件: [是空 V]
  结论: G ⊴ H
  证明: ⟨{ toFun := isEmptyElim
     inj' := isEmptyElim
     map_rel_iff' := fun {a} => isEmptyElim a }⟩

Depends on / 依赖: isEmptyElim, map_rel_iff
-/
lemma IsIndContained.of_isEmpty [IsEmpty V] : G ⊴ H :=
  ⟨{ toFun := isEmptyElim
     inj' := isEmptyElim
     map_rel_iff' := fun {a} => isEmptyElim a }⟩

/--
lemma `isIndContained_iff_exists_iso_subgraph` / 引理 `isIndContained_iff_exists_iso_subgraph`

English:
lemma isIndContained_iff_exists_iso_subgraph
  proof: by
  constructor
  · rintro ⟨f⟩
    refine ⟨f.toCopy.toSubgraph, f.toCopy.isoToSubgraph, ?_⟩
    simp [Subgraph.IsInduced, Relation.map_apply_apply, f.injective]
  · rintro ⟨H', e, hH'⟩
    exact e.isIndContained.trans hH'.isIndContained

alias ⟨IsIndContained.exists_iso_subgraph, IsIndContained.of_exists_iso_subgraph⟩ :=
  isIndContained_iff_exists_iso_subgraph

中文:
引理 isIndContained_iff_存在_iso_subgraph
  证明: by
  constructor
  · rintro ⟨f⟩
    refine ⟨f.toCopy.toSubgraph, f.toCopy.isoToSubgraph, ?_⟩
    simp [Subgraph.IsInduced, Relation.map_apply_apply, f.injective]
  · rintro ⟨H', e, hH'⟩
    exact e.isIndContained.trans hH'.isIndContained

alias ⟨IsIndContained.exists_iso_subgraph, IsIndContained.of_exists_iso_subgraph⟩ :=
  isIndContained_iff_exists_iso_subgraph

Depends on / 依赖: IsInduced, Relation, Relation.map_apply_apply, Subgraph, Subgraph.IsInduced, e.isIndContained.trans, f.injective, f.toCopy.isoToSubgraph, f.toCopy.toSubgraph, injective, isIndContained, isoToSubgraph, map_apply_apply, toCopy, toSubgraph
-/
lemma isIndContained_iff_exists_iso_subgraph :
    G ⊴ H ↔ exists (H' : H.Subgraph) (_e : G ≃g H'.coe), H'.IsInduced := by
  constructor
  · rintro ⟨f⟩
    refine ⟨f.toCopy.toSubgraph, f.toCopy.isoToSubgraph, ?_⟩
    simp [Subgraph.IsInduced, Relation.map_apply_apply, f.injective]
  · rintro ⟨H', e, hH'⟩
    exact e.isIndContained.trans hH'.isIndContained

alias ⟨IsIndContained.exists_iso_subgraph, IsIndContained.of_exists_iso_subgraph⟩ :=
  isIndContained_iff_exists_iso_subgraph

/--
theorem `isIndContained_iff_exists_iso_induce` / 定理 `isIndContained_iff_exists_iso_induce`

English:
theorem isIndContained_iff_exists_iso_induce
  statement: G ⊴ H ↔ exists s, Nonempty (G ≃g H.induce s)
  proof: ⟨fun ⟨f⟩ => ⟨Set.range f, ⟨f.isoInduceRange⟩⟩, fun ⟨s, ⟨f⟩⟩ => ⟨.comp (.induce s) f⟩⟩

中文:
定理 isIndContained_iff_存在_iso_induce
  结论: G ⊴ H ↔ 存在 s, 非空 (G ≃g H.induce s)
  证明: ⟨fun ⟨f⟩ => ⟨Set.range f, ⟨f.isoInduceRange⟩⟩, fun ⟨s, ⟨f⟩⟩ => ⟨.comp (.induce s) f⟩⟩

Depends on / 依赖: Set.range, f.isoInduceRange, induce, isoInduceRange
-/
theorem isIndContained_iff_exists_iso_induce : G ⊴ H ↔ exists s, Nonempty (G ≃g H.induce s) :=
  ⟨fun ⟨f⟩ => ⟨Set.range f, ⟨f.isoInduceRange⟩⟩, fun ⟨s, ⟨f⟩⟩ => ⟨.comp (.induce s) f⟩⟩

/--
lemma `top_isIndContained_iff_top_isContained` / 引理 `top_isIndContained_iff_top_isContained`

English:
lemma top_isIndContained_iff_top_isContained
  proof: ⟨IsIndContained.isContained, fun ⟨f⟩ => ⟨f.topEmbedding⟩⟩

中文:
引理 top_isIndContained_iff_top_isContained
  证明: ⟨IsIndContained.isContained, fun ⟨f⟩ => ⟨f.topEmbedding⟩⟩
-/
@[simp] lemma top_isIndContained_iff_top_isContained :
    (⊤ : SimpleGraph V) ⊴ H ↔ (⊤ : SimpleGraph V) ⊑ H :=
  ⟨IsIndContained.isContained, fun ⟨f⟩ => ⟨f.topEmbedding⟩⟩

/--
theorem `isContained_top_iff` / 定理 `isContained_top_iff`

English:
theorem isContained_top_iff
  given: {G : SimpleGraph V}
  statement: G ⊑ completeGraph W ↔ Nonempty (V ↪ W)
  proof: ⟨(⟨·.some.toEmbedding⟩), (.trans (.of_le le_top) ⟨Embedding.completeGraph ·.some |>.toCopy⟩)⟩

中文:
定理 isContained_top_iff
  条件: {G : 简单图 V}
  结论: G ⊑ completeGraph W ↔ 非空 (V ↪ W)
  证明: ⟨(⟨·.some.toEmbedding⟩), (.trans (.of_le le_top) ⟨Embedding.completeGraph ·.some |>.toCopy⟩)⟩

Depends on / 依赖: Embedding, Embedding.completeGraph, completeGraph, le_top, of_le, some.toEmbedding, toCopy, toEmbedding
-/
theorem isContained_top_iff {G : SimpleGraph V} : G ⊑ completeGraph W ↔ Nonempty (V ↪ W) :=
  ⟨(⟨·.some.toEmbedding⟩), (.trans (.of_le le_top) ⟨Embedding.completeGraph ·.some |>.toCopy⟩)⟩

/--
theorem `top_isIndContained_top_iff` / 定理 `top_isIndContained_top_iff`

English:
theorem top_isIndContained_top_iff
  statement: completeGraph V ⊴ completeGraph W ↔ Nonempty (V ↪ W)
  proof: ⟨(⟨·.some.toEmbedding⟩), (⟨.completeGraph ·.some⟩)⟩

中文:
定理 top_isIndContained_top_iff
  结论: completeGraph V ⊴ completeGraph W ↔ 非空 (V ↪ W)
  证明: ⟨(⟨·.some.toEmbedding⟩), (⟨.completeGraph ·.some⟩)⟩

Depends on / 依赖: completeGraph, some.toEmbedding, toEmbedding
-/
theorem top_isIndContained_top_iff : completeGraph V ⊴ completeGraph W ↔ Nonempty (V ↪ W) :=
  ⟨(⟨·.some.toEmbedding⟩), (⟨.completeGraph ·.some⟩)⟩

/--
theorem `eq_top_of_isIndContained_top` / 定理 `eq_top_of_isIndContained_top`

English:
theorem eq_top_of_isIndContained_top
  given: (h : G ⊴ completeGraph W)
  statement: G = ⊤
  proof: h.some.comap_eq ▸ comap_top h.some.injective

中文:
定理 eq_top_of_isIndContained_top
  条件: (h : G ⊴ completeGraph W)
  结论: G = ⊤
  证明: h.some.comap_eq ▸ comap_top h.some.injective

Depends on / 依赖: comap_eq, comap_top, h.some.comap_eq, h.some.injective, injective
-/
theorem eq_top_of_isIndContained_top (h : G ⊴ completeGraph W) : G = ⊤ :=
  h.some.comap_eq ▸ comap_top h.some.injective

/--
lemma `compl_isIndContained_compl` / 引理 `compl_isIndContained_compl`

English:
lemma compl_isIndContained_compl
  statement: Gᶜ ⊴ Hᶜ ↔ G ⊴ H
  proof: Embedding.complEquiv.symm.nonempty_congr

protected alias ⟨IsIndContained.of_compl, IsIndContained.compl⟩ := compl_isIndContained_compl

中文:
引理 compl_isIndContained_compl
  结论: Gᶜ ⊴ Hᶜ ↔ G ⊴ H
  证明: Embedding.complEquiv.symm.nonempty_congr

protected alias ⟨IsIndContained.of_compl, IsIndContained.compl⟩ := compl_isIndContained_compl
-/
@[simp] lemma compl_isIndContained_compl : Gᶜ ⊴ Hᶜ ↔ G ⊴ H :=
  Embedding.complEquiv.symm.nonempty_congr

protected alias ⟨IsIndContained.of_compl, IsIndContained.compl⟩ := compl_isIndContained_compl

/--
theorem `isContained_iff_exists_le_comap` / 定理 `isContained_iff_exists_le_comap`

English:
theorem isContained_iff_exists_le_comap
  statement: H ⊑ G ↔ exists (f : W ↪ V), H <= G.comap f
  proof: ⟨fun ⟨f⟩ => ⟨f.toEmbedding, f.toHom.le_comap⟩, fun ⟨f, h⟩ => ⟨⟨f, (h ·)⟩, f.injective⟩⟩

中文:
定理 isContained_iff_存在_le_comap
  结论: H ⊑ G ↔ 存在 (f : W ↪ V), H <= G.comap f
  证明: ⟨fun ⟨f⟩ => ⟨f.toEmbedding, f.toHom.le_comap⟩, fun ⟨f, h⟩ => ⟨⟨f, (h ·)⟩, f.injective⟩⟩

Depends on / 依赖: f.injective, f.toEmbedding, f.toHom.le_comap, injective, le_comap, toEmbedding
-/
theorem isContained_iff_exists_le_comap : H ⊑ G ↔ exists (f : W ↪ V), H <= G.comap f :=
  ⟨fun ⟨f⟩ => ⟨f.toEmbedding, f.toHom.le_comap⟩, fun ⟨f, h⟩ => ⟨⟨f, (h ·)⟩, f.injective⟩⟩

/--
theorem `isIndContained_iff_exists_comap_eq` / 定理 `isIndContained_iff_exists_comap_eq`

English:
theorem isIndContained_iff_exists_comap_eq
  statement: H ⊴ G ↔ exists (f : W ↪ V), G.comap f = H
  proof: ⟨fun ⟨f⟩ => ⟨f.toEmbedding, f.comap_eq⟩, fun ⟨f, h⟩ => ⟨f, h ▸ .rfl⟩⟩

中文:
定理 isIndContained_iff_存在_comap_eq
  结论: H ⊴ G ↔ 存在 (f : W ↪ V), G.comap f = H
  证明: ⟨fun ⟨f⟩ => ⟨f.toEmbedding, f.comap_eq⟩, fun ⟨f, h⟩ => ⟨f, h ▸ .rfl⟩⟩

Depends on / 依赖: comap_eq, f.comap_eq, f.toEmbedding, toEmbedding
-/
theorem isIndContained_iff_exists_comap_eq : H ⊴ G ↔ exists (f : W ↪ V), G.comap f = H :=
  ⟨fun ⟨f⟩ => ⟨f.toEmbedding, f.comap_eq⟩, fun ⟨f, h⟩ => ⟨f, h ▸ .rfl⟩⟩

/-!
### Counting the copies

If `G` and `H` are finite graphs, we can count the number of unlabelled and labelled copies of `G`
in `H`.

#### Not necessarily induced copies
-/

section LabelledCopyCount
variable [Fintype V] [Fintype W]

/--
Definition of `labelledCopyCount` / `labelledCopyCount` 的定义

English:
definition labelledCopyCount
  signature: (G : SimpleGraph V) (H : SimpleGraph W)
  body: by
  classical exact Fintype.card (Copy H G)

中文:
定义 labelledCopyCount
  签名: (G : 简单图 V) (H : 简单图 W)
  定义体: by
  classical exact Fintype.card (Copy H G)

Depends on / 依赖: Fintype, Fintype.card, classical
-/
noncomputable def labelledCopyCount (G : SimpleGraph V) (H : SimpleGraph W) : Nat := by
  classical exact Fintype.card (Copy H G)

/--
lemma `labelledCopyCount_of_isEmpty` / 引理 `labelledCopyCount_of_isEmpty`

English:
lemma labelledCopyCount_of_isEmpty
  given: [IsEmpty W] (G : SimpleGraph V) (H : SimpleGraph W)
  proof: by
  convert! Fintype.card_unique
  exact { default := ⟨default, isEmptyElim⟩, uniq := fun _ => Subsingleton.elim _ _ }

中文:
引理 labelledCopyCount_of_isEmpty
  条件: [是空 W] (G : 简单图 V) (H : 简单图 W)
  证明: by
  convert! Fintype.card_unique
  exact { default := ⟨default, isEmptyElim⟩, uniq := fun _ => Subsingleton.elim _ _ }
-/
@[simp] lemma labelledCopyCount_of_isEmpty [IsEmpty W] (G : SimpleGraph V) (H : SimpleGraph W) :
    G.labelledCopyCount H = 1 := by
  convert! Fintype.card_unique
  exact { default := ⟨default, isEmptyElim⟩, uniq := fun _ => Subsingleton.elim _ _ }

/--
lemma `labelledCopyCount_eq_zero` / 引理 `labelledCopyCount_eq_zero`

English:
lemma labelledCopyCount_eq_zero
  statement: G.labelledCopyCount H = 0 ↔ H.Free G
  proof: by
  simp [labelledCopyCount, Fintype.card_eq_zero_iff]

中文:
引理 labelledCopyCount_eq_zero
  结论: G.labelledCopyCount H = 0 ↔ H.自由 G
  证明: by
  simp [labelledCopyCount, Fintype.card_eq_zero_iff]
-/
@[simp] lemma labelledCopyCount_eq_zero : G.labelledCopyCount H = 0 ↔ H.Free G := by
  simp [labelledCopyCount, Fintype.card_eq_zero_iff]

/--
lemma `labelledCopyCount_pos` / 引理 `labelledCopyCount_pos`

English:
lemma labelledCopyCount_pos
  statement: 0 < G.labelledCopyCount H ↔ H ⊑ G
  proof: by
  simp [labelledCopyCount, IsContained, Fintype.card_pos_iff]

中文:
引理 labelledCopyCount_pos
  结论: 0 < G.labelledCopyCount H ↔ H ⊑ G
  证明: by
  simp [labelledCopyCount, IsContained, Fintype.card_pos_iff]
-/
@[simp] lemma labelledCopyCount_pos : 0 < G.labelledCopyCount H ↔ H ⊑ G := by
  simp [labelledCopyCount, IsContained, Fintype.card_pos_iff]

end LabelledCopyCount

section CopyCount
variable [Fintype V]

/--
Definition of `copyCount` / `copyCount` 的定义

English:
definition copyCount
  signature: (G : SimpleGraph V) (H : SimpleGraph W)
  body: by
  classical exact #{G' : G.Subgraph | Nonempty (H ≃g G'.coe)}

中文:
定义 copyCount
  签名: (G : 简单图 V) (H : 简单图 W)
  定义体: by
  classical exact #{G' : G.Subgraph | Nonempty (H ≃g G'.coe)}

Depends on / 依赖: G.Subgraph, Nonempty, Subgraph, classical
-/
noncomputable def copyCount (G : SimpleGraph V) (H : SimpleGraph W) : Nat := by
  classical exact #{G' : G.Subgraph | Nonempty (H ≃g G'.coe)}

/--
lemma `copyCount_eq_card_image_copyToSubgraph` / 引理 `copyCount_eq_card_image_copyToSubgraph`

English:
lemma copyCount_eq_card_image_copyToSubgraph
  statement: [Fintype {f : H ->g G // Injective f}]
  proof: by
  rw [copyCount]
  congr
  refine Finset.coe_injective ?_
  simpa [-Copy.range_toSubgraph] using Copy.range_toSubgraph.symm

中文:
引理 copyCount_eq_card_image_copyToSubgraph
  结论: [有限类型 {f : H ->g G // 单射 f}]
  证明: by
  rw [copyCount]
  congr
  refine Finset.coe_injective ?_
  simpa [-Copy.range_toSubgraph] using Copy.range_toSubgraph.symm

Depends on / 依赖: Copy.range_toSubgraph, Copy.range_toSubgraph.symm, Finset, Finset.coe_injective, coe_injective, copyCount, range_toSubgraph
-/
lemma copyCount_eq_card_image_copyToSubgraph [Fintype {f : H ->g G // Injective f}]
    [DecidableEq G.Subgraph] :
    copyCount G H = #((Finset.univ : Finset (H.Copy G)).image Copy.toSubgraph) := by
  rw [copyCount]
  congr
  refine Finset.coe_injective ?_
  simpa [-Copy.range_toSubgraph] using Copy.range_toSubgraph.symm

/--
lemma `copyCount_eq_zero` / 引理 `copyCount_eq_zero`

English:
lemma copyCount_eq_zero
  statement: G.copyCount H = 0 ↔ H.Free G
  proof: by
  simp [copyCount, Free, -nonempty_subtype, isContained_iff_exists_iso_subgraph,
    filter_eq_empty_iff]

中文:
引理 copyCount_eq_zero
  结论: G.copyCount H = 0 ↔ H.自由 G
  证明: by
  simp [copyCount, Free, -nonempty_subtype, isContained_iff_exists_iso_subgraph,
    filter_eq_empty_iff]
-/
@[simp] lemma copyCount_eq_zero : G.copyCount H = 0 ↔ H.Free G := by
  simp [copyCount, Free, -nonempty_subtype, isContained_iff_exists_iso_subgraph,
    filter_eq_empty_iff]

/--
lemma `copyCount_pos` / 引理 `copyCount_pos`

English:
lemma copyCount_pos
  statement: 0 < G.copyCount H ↔ H ⊑ G
  proof: by
  simp [copyCount, -nonempty_subtype, isContained_iff_exists_iso_subgraph, card_pos,
    filter_nonempty_iff]

中文:
引理 copyCount_pos
  结论: 0 < G.copyCount H ↔ H ⊑ G
  证明: by
  simp [copyCount, -nonempty_subtype, isContained_iff_exists_iso_subgraph, card_pos,
    filter_nonempty_iff]
-/
@[simp] lemma copyCount_pos : 0 < G.copyCount H ↔ H ⊑ G := by
  simp [copyCount, -nonempty_subtype, isContained_iff_exists_iso_subgraph, card_pos,
    filter_nonempty_iff]

/--
lemma `copyCount_le_labelledCopyCount` / 引理 `copyCount_le_labelledCopyCount`

English:
lemma copyCount_le_labelledCopyCount
  given: [Fintype W]
  statement: G.copyCount H <= G.labelledCopyCount H
  proof: by
  classical rw [copyCount_eq_card_image_copyToSubgraph]; exact card_image_le

中文:
引理 copyCount_le_labelledCopyCount
  条件: [有限类型 W]
  结论: G.copyCount H <= G.labelledCopyCount H
  证明: by
  classical rw [copyCount_eq_card_image_copyToSubgraph]; exact card_image_le

Depends on / 依赖: card_image_le, classical, copyCount_eq_card_image_copyToSubgraph
-/
lemma copyCount_le_labelledCopyCount [Fintype W] : G.copyCount H <= G.labelledCopyCount H := by
  classical rw [copyCount_eq_card_image_copyToSubgraph]; exact card_image_le

/--
lemma `copyCount_bot` / 引理 `copyCount_bot`

English:
lemma copyCount_bot
  given: (G : SimpleGraph V)
  statement: copyCount G (⊥ : SimpleGraph V) = 1
  proof: by
  classical
  rw [copyCount]
  convert!
    card_singleton (α := G.Subgraph)
      { verts := .univ
        Adj := ⊥
        adj_sub := False.elim
        edge_vert := False.elim }
  simp only [eq_singleton_iff_unique_mem, mem_filter_univ, Nonempty.forall]
  refine ⟨⟨⟨(Equiv.Set.univ _).symm, by simp⟩⟩, fun H' e =>
    Subgraph.ext ((set_fintype_card_eq_univ_iff _).1 <| Fintype.card_congr e.toEquiv.symm) ?_⟩
  ext a b
  simp only [Prop.bot_eq_false, Pi.bot_apply, iff_false]
  exact fun hab => e.symm.map_rel_iff.2 hab.coe

中文:
引理 copyCount_bot
  条件: (G : 简单图 V)
  结论: copyCount G (⊥ : 简单图 V) = 1
  证明: by
  classical
  rw [copyCount]
  convert!
    card_singleton (α := G.Subgraph)
      { verts := .univ
        Adj := ⊥
        adj_sub := False.elim
        edge_vert := False.elim }
  simp only [eq_singleton_iff_unique_mem, mem_filter_univ, Nonempty.forall]
  refine ⟨⟨⟨(Equiv.Set.univ _).symm, by simp⟩⟩, fun H' e =>
    Subgraph.ext ((set_fintype_card_eq_univ_iff _).1 <| Fintype.card_congr e.toEquiv.symm) ?_⟩
  ext a b
  simp only [Prop.bot_eq_false, Pi.bot_apply, iff_false]
  exact fun hab => e.symm.map_rel_iff.2 hab.coe
-/
@[simp] lemma copyCount_bot (G : SimpleGraph V) : copyCount G (⊥ : SimpleGraph V) = 1 := by
  classical
  rw [copyCount]
  convert!
    card_singleton (α := G.Subgraph)
      { verts := .univ
        Adj := ⊥
        adj_sub := False.elim
        edge_vert := False.elim }
  simp only [eq_singleton_iff_unique_mem, mem_filter_univ, Nonempty.forall]
  refine ⟨⟨⟨(Equiv.Set.univ _).symm, by simp⟩⟩, fun H' e =>
    Subgraph.ext ((set_fintype_card_eq_univ_iff _).1 <| Fintype.card_congr e.toEquiv.symm) ?_⟩
  ext a b
  simp only [Prop.bot_eq_false, Pi.bot_apply, iff_false]
  exact fun hab => e.symm.map_rel_iff.2 hab.coe

/--
lemma `copyCount_of_isEmpty` / 引理 `copyCount_of_isEmpty`

English:
lemma copyCount_of_isEmpty
  given: [IsEmpty W] (G : SimpleGraph V) (H : SimpleGraph W)
  proof: by
  cases nonempty_fintype W
exact (copyCount_le_labelledCopyCount.trans_eq <| labelledCopyCount_of_isEmpty ..).antisymm
copyCount_pos.2 .of_isEmpty

中文:
引理 copyCount_of_isEmpty
  条件: [是空 W] (G : 简单图 V) (H : 简单图 W)
  证明: by
  cases nonempty_fintype W
exact (copyCount_le_labelledCopyCount.trans_eq <| labelledCopyCount_of_isEmpty ..).antisymm
copyCount_pos.2 .of_isEmpty
-/
@[simp] lemma copyCount_of_isEmpty [IsEmpty W] (G : SimpleGraph V) (H : SimpleGraph W) :
    G.copyCount H = 1 := by
  cases nonempty_fintype W
exact (copyCount_le_labelledCopyCount.trans_eq <| labelledCopyCount_of_isEmpty ..).antisymm
copyCount_pos.2 .of_isEmpty

end CopyCount

/-!
#### Induced copies

TODO

### Killing a subgraph

An important aspect of graph containment is that we can remove not too many edges from a graph `H`
to get a graph `H'` that doesn't contain `G`.

#### Killing not necessarily induced copies

`SimpleGraph.killCopies G H` is a subgraph of `G` where an edge was removed from each copy of `H` in
`G`. By construction, it doesn't contain `H` and has at most the number of copies of `H` edges less
than `G`.
-/

set_option backward.privateInPublic true in
/--
lemma `aux` / 引理 `aux`

English:
lemma aux
  given: (hH : H != ⊥) {G' : G.Subgraph}
  proof: by
  obtain ⟨e, he⟩ := edgeSet_nonempty.2 hH
  rw [← Subgraph.image_coe_edgeSet_coe]
  exact fun ⟨f⟩ => Set.Nonempty.image _ ⟨_, f.map_mem_edgeSet_iff.2 he⟩

中文:
引理 aux
  条件: (hH : H != ⊥) {G' : G.子图}
  证明: by
  obtain ⟨e, he⟩ := edgeSet_nonempty.2 hH
  rw [← Subgraph.image_coe_edgeSet_coe]
  exact fun ⟨f⟩ => Set.Nonempty.image _ ⟨_, f.map_mem_edgeSet_iff.2 he⟩
-/
private lemma aux (hH : H != ⊥) {G' : G.Subgraph} :
    Nonempty (H ≃g G'.coe) -> G'.edgeSet.Nonempty := by
  obtain ⟨e, he⟩ := edgeSet_nonempty.2 hH
  rw [← Subgraph.image_coe_edgeSet_coe]
  exact fun ⟨f⟩ => Set.Nonempty.image _ ⟨_, f.map_mem_edgeSet_iff.2 he⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- `G.killCopies H` is a subgraph of `G` where an *arbitrary* edge was removed from each copy of
`H` in `G`. By construction, it doesn't contain `H` (unless `H` had no edges) and has at most the
number of copies of `H` edges less than `G`. See `free_killCopies` and
`le_card_edgeFinset_killCopies` for these two properties. -/
noncomputable irreducible_def killCopies (G : SimpleGraph V) (H : SimpleGraph W) :
    SimpleGraph V := by
  classical exact
  if hH : H = ⊥ then G
else G.deleteEdges ⋃ (G' : G.Subgraph) (hG' : Nonempty (H ≃g G'.coe)), {(aux hH hG').some}

/--
lemma `killCopies_le_left` / 引理 `killCopies_le_left`

English:
lemma killCopies_le_left
  statement: G.killCopies H <= G
  proof: by
  rw [killCopies]; split_ifs; exacts [le_rfl, deleteEdges_le _]

中文:
引理 killCopies_le_left
  结论: G.killCopies H <= G
  证明: by
  rw [killCopies]; split_ifs; exacts [le_rfl, deleteEdges_le _]

Depends on / 依赖: deleteEdges_le, exacts, killCopies, le_rfl, split_ifs
-/
lemma killCopies_le_left : G.killCopies H <= G := by
  rw [killCopies]; split_ifs; exacts [le_rfl, deleteEdges_le _]

/--
lemma `killCopies_bot` / 引理 `killCopies_bot`

English:
lemma killCopies_bot
  given: (G : SimpleGraph V)
  statement: G.killCopies (⊥ : SimpleGraph W) = G
  proof: by
  rw [killCopies]; exact dif_pos rfl

中文:
引理 killCopies_bot
  条件: (G : 简单图 V)
  结论: G.killCopies (⊥ : 简单图 W) = G
  证明: by
  rw [killCopies]; exact dif_pos rfl
-/
@[simp] lemma killCopies_bot (G : SimpleGraph V) : G.killCopies (⊥ : SimpleGraph W) = G := by
  rw [killCopies]; exact dif_pos rfl

/--
lemma `killCopies_of_ne_bot` / 引理 `killCopies_of_ne_bot`

English:
lemma killCopies_of_ne_bot
  given: (hH : H != ⊥) (G : SimpleGraph V)
  proof: by
  rw [killCopies]; exact dif_neg hH

中文:
引理 killCopies_of_ne_bot
  条件: (hH : H != ⊥) (G : 简单图 V)
  证明: by
  rw [killCopies]; exact dif_neg hH
-/
private lemma killCopies_of_ne_bot (hH : H != ⊥) (G : SimpleGraph V) :
    G.killCopies H =
      G.deleteEdges (⋃ (G' : G.Subgraph) (hG' : Nonempty (H ≃g G'.coe)), {(aux hH hG').some}) := by
  rw [killCopies]; exact dif_neg hH

/--
lemma `killCopies_eq_left` / 引理 `killCopies_eq_left`

English:
lemma killCopies_eq_left
  given: (hH : H != ⊥)
  statement: G.killCopies H = G ↔ H.Free G
  proof: by
  simp only [killCopies_of_ne_bot hH, Set.disjoint_left, isContained_iff_exists_iso_subgraph,
    @forall_comm _ G.Subgraph, deleteEdges_eq_self, Set.mem_iUnion,
    not_exists, not_nonempty_iff, Nonempty.forall, Free]
  exact forall_congr' fun G' => ⟨fun h => ⟨fun f => h _
    (Subgraph.edgeSet_subset _ <| (aux hH ⟨f⟩).choose_spec) f rfl⟩, fun h _ _ => h.elim⟩

中文:
引理 killCopies_eq_left
  条件: (hH : H != ⊥)
  结论: G.killCopies H = G ↔ H.自由 G
  证明: by
  simp only [killCopies_of_ne_bot hH, Set.disjoint_left, isContained_iff_exists_iso_subgraph,
    @forall_comm _ G.Subgraph, deleteEdges_eq_self, Set.mem_iUnion,
    not_exists, not_nonempty_iff, Nonempty.forall, Free]
  exact forall_congr' fun G' => ⟨fun h => ⟨fun f => h _
    (Subgraph.edgeSet_subset _ <| (aux hH ⟨f⟩).choose_spec) f rfl⟩, fun h _ _ => h.elim⟩

Depends on / 依赖: G.Subgraph, Nonempty, Nonempty.forall, Set.disjoint_left, Set.mem_iUnion, Subgraph, Subgraph.edgeSet_subset, choose_spec, deleteEdges_eq_self, disjoint_left, edgeSet_subset, forall_comm, forall_congr, h.elim, isContained_iff_exists_iso_subgraph, killCopies_of_ne_bot, mem_iUnion, not_exists, not_nonempty_iff
-/
lemma killCopies_eq_left (hH : H != ⊥) : G.killCopies H = G ↔ H.Free G := by
  simp only [killCopies_of_ne_bot hH, Set.disjoint_left, isContained_iff_exists_iso_subgraph,
    @forall_comm _ G.Subgraph, deleteEdges_eq_self, Set.mem_iUnion,
    not_exists, not_nonempty_iff, Nonempty.forall, Free]
  exact forall_congr' fun G' => ⟨fun h => ⟨fun f => h _
    (Subgraph.edgeSet_subset _ <| (aux hH ⟨f⟩).choose_spec) f rfl⟩, fun h _ _ => h.elim⟩

/--
lemma `Free.killCopies_eq_left` / 引理 `Free.killCopies_eq_left`

English:
lemma Free.killCopies_eq_left
  given: (hHG : H.Free G)
  statement: G.killCopies H = G
  proof: by
  obtain rfl | hH := eq_or_ne H ⊥
  · exact killCopies_bot _
  · exact (killCopies_eq_left hH).2 hHG

中文:
引理 自由.killCopies_eq_left
  条件: (hHG : H.自由 G)
  结论: G.killCopies H = G
  证明: by
  obtain rfl | hH := eq_or_ne H ⊥
  · exact killCopies_bot _
  · exact (killCopies_eq_left hH).2 hHG
-/
protected lemma Free.killCopies_eq_left (hHG : H.Free G) : G.killCopies H = G := by
  obtain rfl | hH := eq_or_ne H ⊥
  · exact killCopies_bot _
  · exact (killCopies_eq_left hH).2 hHG

set_option backward.isDefEq.respectTransparency false in
/--
lemma `free_killCopies` / 引理 `free_killCopies`

English:
lemma free_killCopies
  given: (hH : H != ⊥)
  statement: H.Free (G.killCopies H)
  proof: by
  rw [killCopies_of_ne_bot hH]; rw [deleteEdges]; rw [Free]; rw [isContained_iff_exists_iso_subgraph]
  rintro ⟨G', hHG'⟩
  have hG' : (G'.map <| .ofLE (sdiff_le : G \ _ <= G)).edgeSet.Nonempty := by
    rw [Subgraph.edgeSet_map]
    exact (aux hH hHG').image _
  set e := hG'.some with he
  have : e in _ := hG'.some_mem
  clear_value e
  rw [← Subgraph.image_coe_edgeSet_coe] at this
  subst he
  obtain ⟨e, he₀, he₁⟩ := this
  let e' : Sym2 G'.verts := Sym2.map (Copy.isoSubgraphMap (.ofLE _ _ _) _).symm e
  have he' : e' in G'.coe.edgeSet := (Iso.map_mem_edgeSet_iff _).2 he₀
  rw [Subgraph.edgeSet_coe] at he'
  have := Subgraph.edgeSet_subset _ he'
  simp only [edgeSet_sdiff, edgeSet_fromEdgeSet, edgeSet_sdiff_sdiff_isDiag, Set.mem_sdiff,
    Set.mem_iUnion, not_exists] at this
  refine this.2 (G'.map <| .ofLE sdiff_le) ⟨((Copy.ofLE _ _ _).isoSubgraphMap _).comp hHG'.some⟩ ?_
  rw [Sym2.map_map]; rw [Set.mem_singleton_iff]; rw [← he₁]
  congr 1 with x
  exact congr_arg _ (Equiv.Set.image_symm_apply _ _ injective_id _ _)

中文:
引理 free_killCopies
  条件: (hH : H != ⊥)
  结论: H.自由 (G.killCopies H)
  证明: by
  rw [killCopies_of_ne_bot hH]; rw [deleteEdges]; rw [Free]; rw [isContained_iff_exists_iso_subgraph]
  rintro ⟨G', hHG'⟩
  have hG' : (G'.map <| .ofLE (sdiff_le : G \ _ <= G)).edgeSet.Nonempty := by
    rw [Subgraph.edgeSet_map]
    exact (aux hH hHG').image _
  set e := hG'.some with he
  have : e in _ := hG'.some_mem
  clear_value e
  rw [← Subgraph.image_coe_edgeSet_coe] at this
  subst he
  obtain ⟨e, he₀, he₁⟩ := this
  let e' : Sym2 G'.verts := Sym2.map (Copy.isoSubgraphMap (.ofLE _ _ _) _).symm e
  have he' : e' in G'.coe.edgeSet := (Iso.map_mem_edgeSet_iff _).2 he₀
  rw [Subgraph.edgeSet_coe] at he'
  have := Subgraph.edgeSet_subset _ he'
  simp only [edgeSet_sdiff, edgeSet_fromEdgeSet, edgeSet_sdiff_sdiff_isDiag, Set.mem_sdiff,
    Set.mem_iUnion, not_exists] at this
  refine this.2 (G'.map <| .ofLE sdiff_le) ⟨((Copy.ofLE _ _ _).isoSubgraphMap _).comp hHG'.some⟩ ?_
  rw [Sym2.map_map]; rw [Set.mem_singleton_iff]; rw [← he₁]
  congr 1 with x
  exact congr_arg _ (Equiv.Set.image_symm_apply _ _ injective_id _ _)

Depends on / 依赖: Copy.isoSubgraphMap, Nonempty, Subgraph, Subgraph.edgeSet_map, Subgraph.image_coe_edgeSet_coe, Sym2.map, clear_value, deleteEdges, edgeSet, edgeSet.Nonempty, edgeSet_map, image_coe_edgeSet_coe, isContained_iff_exists_iso_subgraph, isoSubgraphMap, killCopies_of_ne_bot, sdiff_le, some_mem
-/
lemma free_killCopies (hH : H != ⊥) : H.Free (G.killCopies H) := by
  rw [killCopies_of_ne_bot hH]; rw [deleteEdges]; rw [Free]; rw [isContained_iff_exists_iso_subgraph]
  rintro ⟨G', hHG'⟩
  have hG' : (G'.map <| .ofLE (sdiff_le : G \ _ <= G)).edgeSet.Nonempty := by
    rw [Subgraph.edgeSet_map]
    exact (aux hH hHG').image _
  set e := hG'.some with he
  have : e in _ := hG'.some_mem
  clear_value e
  rw [← Subgraph.image_coe_edgeSet_coe] at this
  subst he
  obtain ⟨e, he₀, he₁⟩ := this
  let e' : Sym2 G'.verts := Sym2.map (Copy.isoSubgraphMap (.ofLE _ _ _) _).symm e
  have he' : e' in G'.coe.edgeSet := (Iso.map_mem_edgeSet_iff _).2 he₀
  rw [Subgraph.edgeSet_coe] at he'
  have := Subgraph.edgeSet_subset _ he'
  simp only [edgeSet_sdiff, edgeSet_fromEdgeSet, edgeSet_sdiff_sdiff_isDiag, Set.mem_sdiff,
    Set.mem_iUnion, not_exists] at this
  refine this.2 (G'.map <| .ofLE sdiff_le) ⟨((Copy.ofLE _ _ _).isoSubgraphMap _).comp hHG'.some⟩ ?_
  rw [Sym2.map_map]; rw [Set.mem_singleton_iff]; rw [← he₁]
  congr 1 with x
  exact congr_arg _ (Equiv.Set.image_symm_apply _ _ injective_id _ _)

variable [Fintype G.edgeSet]

/--
Instance `killCopies.edgeSet.instFintype` / 实例 `killCopies.edgeSet.instFintype`

English:
instance killCopies.edgeSet.instFintype
  signature: : Fintype (G.killCopies H).edgeSet
  body: .ofInjective (Set.inclusion <| edgeSet_mono killCopies_le_left) Set.inclusion_injective _

中文:
实例 killCopies.edgeSet.instFintype
  签名: : 有限类型 (G.killCopies H).edgeSet
  定义体: .ofInjective (Set.inclusion <| edgeSet_mono killCopies_le_left) Set.inclusion_injective _

Depends on / 依赖: Set.inclusion, Set.inclusion_injective, edgeSet_mono, inclusion, inclusion_injective, killCopies_le_left, ofInjective
-/
noncomputable instance killCopies.edgeSet.instFintype : Fintype (G.killCopies H).edgeSet :=
.ofInjective (Set.inclusion <| edgeSet_mono killCopies_le_left) Set.inclusion_injective _

/--
lemma `le_card_edgeFinset_killCopies` / 引理 `le_card_edgeFinset_killCopies`

English:
lemma le_card_edgeFinset_killCopies
  given: [Fintype V]
  proof: by
  classical
  obtain rfl | hH := eq_or_ne H ⊥
  · simp [← card_edgeSet]
  let f (G' : {G' : G.Subgraph // Nonempty (H ≃g G'.coe)}) := (aux hH G'.2).some
  calc
    _ = #G.edgeFinset - card {G' : G.Subgraph // Nonempty (H ≃g G'.coe)} := ?_
    _ <= #G.edgeFinset - #(univ.image f) := Nat.sub_le_sub_left card_image_le _
    _ = #G.edgeFinset - #(Set.range f).toFinset := by rw [Set.toFinset_range]
    _ <= #(G.edgeFinset \ (Set.range f).toFinset) := le_card_sdiff ..
    _ = #(G.killCopies H).edgeFinset := ?_
  · simp only [edgeFinset, Set.toFinset_card]
    rw [← Set.toFinset_card]; rw [← edgeFinset]; rw [copyCount]; rw [← card_subtype]; rw [subtype_univ]; rw [card_univ]
  congr 1
  ext e
  induction e using Sym2.inductionOn with | hf v w
  simp [mem_edgeSet, killCopies_of_ne_bot hH, f, eq_comm]

中文:
引理 le_card_edgeFinset_killCopies
  条件: [有限类型 V]
  证明: by
  classical
  obtain rfl | hH := eq_or_ne H ⊥
  · simp [← card_edgeSet]
  let f (G' : {G' : G.Subgraph // Nonempty (H ≃g G'.coe)}) := (aux hH G'.2).some
  calc
    _ = #G.edgeFinset - card {G' : G.Subgraph // Nonempty (H ≃g G'.coe)} := ?_
    _ <= #G.edgeFinset - #(univ.image f) := Nat.sub_le_sub_left card_image_le _
    _ = #G.edgeFinset - #(Set.range f).toFinset := by rw [Set.toFinset_range]
    _ <= #(G.edgeFinset \ (Set.range f).toFinset) := le_card_sdiff ..
    _ = #(G.killCopies H).edgeFinset := ?_
  · simp only [edgeFinset, Set.toFinset_card]
    rw [← Set.toFinset_card]; rw [← edgeFinset]; rw [copyCount]; rw [← card_subtype]; rw [subtype_univ]; rw [card_univ]
  congr 1
  ext e
  induction e using Sym2.inductionOn with | hf v w
  simp [mem_edgeSet, killCopies_of_ne_bot hH, f, eq_comm]

Depends on / 依赖: G.Subgraph, G.edgeFinset, G.killCopies, Nat.sub_le_sub_left, Nonempty, Set.range, Set.toFinset_range, Subgraph, card_edgeSet, card_image_le, classical, edgeFinset, eq_or_ne, killCopies, le_card_sdiff, sub_le_sub_left, toFinset, toFinset_range, univ.image
-/
lemma le_card_edgeFinset_killCopies [Fintype V] :
    #G.edgeFinset - G.copyCount H <= #(G.killCopies H).edgeFinset := by
  classical
  obtain rfl | hH := eq_or_ne H ⊥
  · simp [← card_edgeSet]
  let f (G' : {G' : G.Subgraph // Nonempty (H ≃g G'.coe)}) := (aux hH G'.2).some
  calc
    _ = #G.edgeFinset - card {G' : G.Subgraph // Nonempty (H ≃g G'.coe)} := ?_
    _ <= #G.edgeFinset - #(univ.image f) := Nat.sub_le_sub_left card_image_le _
    _ = #G.edgeFinset - #(Set.range f).toFinset := by rw [Set.toFinset_range]
    _ <= #(G.edgeFinset \ (Set.range f).toFinset) := le_card_sdiff ..
    _ = #(G.killCopies H).edgeFinset := ?_
  · simp only [edgeFinset, Set.toFinset_card]
    rw [← Set.toFinset_card]; rw [← edgeFinset]; rw [copyCount]; rw [← card_subtype]; rw [subtype_univ]; rw [card_univ]
  congr 1
  ext e
  induction e using Sym2.inductionOn with | hf v w
  simp [mem_edgeSet, killCopies_of_ne_bot hH, f, eq_comm]

/--
lemma `le_card_edgeFinset_killCopies_add_copyCount` / 引理 `le_card_edgeFinset_killCopies_add_copyCount`

English:
lemma le_card_edgeFinset_killCopies_add_copyCount
  given: [Fintype V]
  proof: tsub_le_iff_right.1 le_card_edgeFinset_killCopies

中文:
引理 le_card_edgeFinset_killCopies_add_copyCount
  条件: [有限类型 V]
  证明: tsub_le_iff_right.1 le_card_edgeFinset_killCopies

Depends on / 依赖: le_card_edgeFinset_killCopies, tsub_le_iff_right
-/
lemma le_card_edgeFinset_killCopies_add_copyCount [Fintype V] :
    #G.edgeFinset <= #(G.killCopies H).edgeFinset + G.copyCount H :=
  tsub_le_iff_right.1 le_card_edgeFinset_killCopies

/-!
#### Killing induced copies

TODO
-/

end SimpleGraph
