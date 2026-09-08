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
/-- A unit-distance embedding of a graph into a metric space is a vertex embedding
such that adjacent vertices are at distance 1 from each other. -/
/-
**SimpleGraph.UnitDistEmbedding** 是 Mathlib 中的一个归纳类型，位于命名空间 `SimpleGraph`。
形式化陈述：{V : Type u_1} → SimpleGraph V → (E : Type u_3) → [MetricSpace E] → Type (
max u_1 u_3)
参数：E : Type u_3；max u_1 u_3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A unit-distance embedding of a graph into a metric space is a vertex embedding
such that adjacent vertices are at distance 1 from each other.
-/
structure UnitDistEmbedding where
  /-- The embedding itself (position of vertices) -/
  p : V ↪ E
  /-- The distance between any two adjacent vertices is 1. -/
  unit_dist {u v} (ha : G.Adj u v) : dist (p u) (p v) = 1

namespace UnitDistEmbedding

/-- An injection into the metric space provides a unit-distance embedding of the empty graph. -/
@[simps]
/-
**SimpleGraph.UnitDistEmbedding.bot** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.UnitD
istEmbedding`。
形式化陈述：bot (p : V ↪ E) : (⊥ : SimpleGraph V).UnitDistEmbedding E
参数：p : V ↪ E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An injection into the metric space provides a unit-distance embedding of the emp
ty graph.
-/
def bot (p : V ↪ E) : (⊥ : SimpleGraph V).UnitDistEmbedding E :=
  ⟨p, by simp⟩

variable (G) in
/-- Any graph on a subsingleton vertex type has a unit-distance embedding, provided the metric space
is nonempty. -/
@[simps]
/-
**SimpleGraph.UnitDistEmbedding.subsingleton** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGr
aph.UnitDistEmbedding`。
形式化陈述：subsingleton [Subsingleton V] (x : E) : G.UnitDistEmbedding E where p
参数：x : E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any graph on a subsingleton vertex type has a unit-distance embedding, provided 
the metric space
is nonempty.
-/
def subsingleton [Subsingleton V] (x : E) : G.UnitDistEmbedding E where
  p := ⟨fun _ ↦ x, Function.injective_of_subsingleton _⟩
  unit_dist {u v} ha := by
    have := Subsingleton.elim u v ▸ ha
    simp at this

variable (U : G.UnitDistEmbedding E)

/-- Derive a unit-distance embedding of `H` from a unit-distance embedding of `G` containing `H`. -/
@[simps!]
/-
**SimpleGraph.UnitDistEmbedding.copy** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Unit
DistEmbedding`。
形式化陈述：copy (f : H.Copy G) : H.UnitDistEmbedding E where p
参数：f : H.Copy G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Derive a unit-distance embedding of `H` from a unit-distance embedding of `G` co
ntaining `H`.
-/
def copy (f : H.Copy G) : H.UnitDistEmbedding E where
  p := f.toEmbedding.trans U.p
  unit_dist ha := U.unit_dist (f.toHom.map_adj ha)

/-- `U.copy` specialised to graph embeddings. -/
@[simps!]
/-
**SimpleGraph.UnitDistEmbedding.embed** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Uni
tDistEmbedding`。
形式化陈述：embed (f : H ↪g G) : H.UnitDistEmbedding E
参数：f : H ↪g G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`U.copy` specialised to graph embeddings.
-/
def embed (f : H ↪g G) : H.UnitDistEmbedding E :=
  U.copy f.toCopy

/-- Transfer a unit-distance embedding across a graph isomorphism. -/
@[simps!]
/-
**SimpleGraph.UnitDistEmbedding.iso** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.UnitD
istEmbedding`。
形式化陈述：iso (e : G ≃g H) : H.UnitDistEmbedding E
参数：e : G ≃g H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transfer a unit-distance embedding across a graph isomorphism.
-/
def iso (e : G ≃g H) : H.UnitDistEmbedding E :=
  U.copy e.symm.toCopy

end UnitDistEmbedding

end SimpleGraph

