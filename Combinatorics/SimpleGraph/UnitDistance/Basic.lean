/-
Copyright (c) 2025 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Topology.MetricSpace.Defs

/-!
# Unit-distance graph embeddings

An embedding of a graph into some metric space is _unit-distance_ if the distance between any two
adjacent vertices is 1. The space in question is usually the Euclidean plane, but can also be
higher-dimensional Euclidean space or the sphere (cf. [Frankl_2020]). We do not require nonadjacent
vertices to not be distance 1 apart as [hong2014] does.

## Main definitions

* `G.UnitDistEmbedding E` is a unit-distance embedding of `G` into `E`.
* `UnitDistEmbedding.copy`, `UnitDistEmbedding.embed`, `UnitDistEmbedding.iso`: transfer a
  unit-distance embedding down a `Copy`, graph embedding or graph isomorphism respectively.
-/

@[expose] public section

namespace SimpleGraph

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {E : Type*} [MetricSpace E]

variable (G E) in
/--
Definition of `UnitDistEmbedding` / `UnitDistEmbedding` 的定义

English:
structure UnitDistEmbedding
  parameters: where
  axioms and operations (2):
    - p : V ↪ E
    - unit_dist({u v} (ha : G.Adj u v)) : dist (p u) (p v) = 1

中文:
结构 UnitDistEmbedding
  参数: where
  公理与运算 (2 个):
    - p : V ↪ E
    - unit_dist({u v} (ha : G.Adj u v)) : dist (p u) (p v) = 1
-/
structure UnitDistEmbedding where
  /-- The embedding itself (position of vertices) -/
  p : V ↪ E
  /-- The distance between any two adjacent vertices is 1. -/
  unit_dist {u v} (ha : G.Adj u v) : dist (p u) (p v) = 1

namespace UnitDistEmbedding

/-- An injection into the metric space provides a unit-distance embedding of the empty graph. -/
@[simps]
/--
Definition of `bot` / `bot` 的定义

English:
definition bot
  signature: (p : V ↪ E)
  body: ⟨p, by simp⟩

中文:
定义 bot
  签名: (p : V ↪ E)
  定义体: ⟨p, by simp⟩
-/
def bot (p : V ↪ E) : (⊥ : SimpleGraph V).UnitDistEmbedding E :=
  ⟨p, by simp⟩

variable (G) in
/-- Any graph on a subsingleton vertex type has a unit-distance embedding, provided the metric space
is nonempty. -/
@[simps]
/--
Definition of `subsingleton` / `subsingleton` 的定义

English:
definition subsingleton
  signature: [Subsingleton V] (x : E)
  body: ⟨fun _ => x, Function.injective_of_subsingleton _⟩
  unit_dist {u v} ha := by
    have := Subsingleton.elim u v ▸ ha
    simp at this

中文:
定义 subsingleton
  签名: [Subsingleton V] (x : E)
  定义体: ⟨fun _ => x, Function.injective_of_subsingleton _⟩
  unit_dist {u v} ha := by
    have := Subsingleton.elim u v ▸ ha
    simp at this

Depends on / 依赖: Function, Function.injective_of_subsingleton, injective_of_subsingleton
-/
def subsingleton [Subsingleton V] (x : E) : G.UnitDistEmbedding E where
  p := ⟨fun _ => x, Function.injective_of_subsingleton _⟩
  unit_dist {u v} ha := by
    have := Subsingleton.elim u v ▸ ha
    simp at this

variable (U : G.UnitDistEmbedding E)

/-- Derive a unit-distance embedding of `H` from a unit-distance embedding of `G` containing `H`. -/
@[simps!]
/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (f : H.Copy G)
  body: f.toEmbedding.trans U.p
  unit_dist ha := U.unit_dist (f.toHom.map_adj ha)

中文:
定义 copy
  签名: (f : H.Copy G)
  定义体: f.toEmbedding.trans U.p
  unit_dist ha := U.unit_dist (f.toHom.map_adj ha)

Depends on / 依赖: f.toEmbedding.trans, toEmbedding
-/
def copy (f : H.Copy G) : H.UnitDistEmbedding E where
  p := f.toEmbedding.trans U.p
  unit_dist ha := U.unit_dist (f.toHom.map_adj ha)

/-- `U.copy` specialised to graph embeddings. -/
@[simps!]
/--
Definition of `embed` / `embed` 的定义

English:
definition embed
  signature: (f : H ↪g G)
  body: U.copy f.toCopy

中文:
定义 embed
  签名: (f : H ↪g G)
  定义体: U.copy f.toCopy

Depends on / 依赖: U.copy, f.toCopy, toCopy
-/
def embed (f : H ↪g G) : H.UnitDistEmbedding E :=
  U.copy f.toCopy

/-- Transfer a unit-distance embedding across a graph isomorphism. -/
@[simps!]
/--
Definition of `iso` / `iso` 的定义

English:
definition iso
  signature: (e : G ≃g H)
  body: U.copy e.symm.toCopy

中文:
定义 iso
  签名: (e : G ≃g H)
  定义体: U.copy e.symm.toCopy

Depends on / 依赖: U.copy, e.symm.toCopy, toCopy
-/
def iso (e : G ≃g H) : H.UnitDistEmbedding E :=
  U.copy e.symm.toCopy

end UnitDistEmbedding

end SimpleGraph
