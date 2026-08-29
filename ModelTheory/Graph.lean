/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.ModelTheory.Satisfiability
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# First-Order Structures in Graph Theory

This file defines first-order languages, structures, and theories in graph theory.

## Main Definitions

- `FirstOrder.Language.graph` is the language consisting of a single relation representing
  adjacency.
- `SimpleGraph.structure` is the first-order structure corresponding to a given simple graph.
- `FirstOrder.Language.Theory.simpleGraph` is the theory of simple graphs.
- `FirstOrder.Language.simpleGraphOfStructure` gives the simple graph corresponding to a model
  of the theory of simple graphs.
-/

@[expose] public section

universe u

namespace FirstOrder

namespace Language

open FirstOrder

open Structure

variable {V : Type u} {n : Nat}

/-! ### Simple Graphs -/

/--
Inductive type `graphRel` / 归纳类型 `graphRel`

English:
inductive graphRel
  parameters: : Nat -> Type
  constructors (1):
    - adj: graphRel 2

中文:
归纳类型 graphRel
  参数: : 自然数 -> 类型
  构造子 (1 个):
    - adj: graphRel 2

Depends on / 依赖: graphRel
-/
inductive graphRel : Nat -> Type
  | adj : graphRel 2
  deriving DecidableEq

/--
Definition of `graph` / `graph` 的定义

English:
definition graph
  signature: : Language
  body: ⟨fun _ => Empty, graphRel⟩
  deriving IsRelational

中文:
定义 graph
  签名: : Language
  定义体: ⟨fun _ => Empty, graphRel⟩
  deriving IsRelational
-/
protected def graph : Language := ⟨fun _ => Empty, graphRel⟩
  deriving IsRelational

/--
Definition of `adj` / `adj` 的定义

English:
abbreviation adj
  signature: : Language.graph.Relations 2
  body: .adj

中文:
缩写 adj
  签名: : Language.graph.关系 2
  定义体: .adj
-/
abbrev adj : Language.graph.Relations 2 := .adj

/-- Any simple graph can be thought of as a structure in the language of graphs. -/
@[instance_reducible]
/--
Definition of `_root_.SimpleGraph.structure` / `_root_.SimpleGraph.structure` 的定义

English:
definition _root_.SimpleGraph.structure
  signature: (G : SimpleGraph V)

中文:
定义 _root_.简单图.structure
  签名: (G : 简单图 V)
-/
def _root_.SimpleGraph.structure (G : SimpleGraph V) : Language.graph.Structure V where
  RelMap | .adj => (fun x => G.Adj (x 0) (x 1))

namespace graph

/--
Instance `instSubsingleton` / 实例 `instSubsingleton`

English:
instance instSubsingleton
  signature: : Subsingleton (Language.graph.Relations n)
  body: ⟨by rintro ⟨⟩ ⟨⟩; rfl⟩

中文:
实例 instSubsingleton
  签名: : 子单例 (Language.graph.关系 n)
  定义体: ⟨by rintro ⟨⟩ ⟨⟩; rfl⟩
-/
instance instSubsingleton : Subsingleton (Language.graph.Relations n) :=
  ⟨by rintro ⟨⟩ ⟨⟩; rfl⟩

end graph

/--
Definition of `Theory.simpleGraph` / `Theory.simpleGraph` 的定义

English:
definition Theory.simpleGraph
  signature: : Language.graph.Theory
  body: {adj.irreflexive, adj.symmetric}

@[simp]

中文:
定义 Theory.simpleGraph
  签名: : Language.graph.Theory
  定义体: {adj.irreflexive, adj.symmetric}

@[simp]
-/
protected def Theory.simpleGraph : Language.graph.Theory :=
  {adj.irreflexive, adj.symmetric}

@[simp]
/--
theorem `Theory.simpleGraph_model_iff` / 定理 `Theory.simpleGraph_model_iff`

English:
theorem Theory.simpleGraph_model_iff
  given: [Language.graph.Structure V]
  proof: by
  simp [Theory.simpleGraph]

中文:
定理 Theory.simpleGraph_model_iff
  条件: [Language.graph.结构 V]
  证明: by
  simp [Theory.simpleGraph]

Depends on / 依赖: Theory, Theory.simpleGraph, simpleGraph
-/
theorem Theory.simpleGraph_model_iff [Language.graph.Structure V] :
    V ⊨ Theory.simpleGraph ↔
      (Std.Irrefl fun x y : V => RelMap adj ![x, y]) ∧
        Std.Symm fun x y : V => RelMap adj ![x, y] := by
  simp [Theory.simpleGraph]

/--
Instance `simpleGraph_model` / 实例 `simpleGraph_model`

English:
instance simpleGraph_model
  signature: (G : SimpleGraph V)
  body: by
  let := G.structure
  rw [Theory.simpleGraph_model_iff]
  exact ⟨G.loopless, G.symm⟩

中文:
实例 simpleGraph_model
  签名: (G : 简单图 V)
  定义体: by
  let := G.structure
  rw [Theory.simpleGraph_model_iff]
  exact ⟨G.loopless, G.symm⟩

Depends on / 依赖: G.loopless, G.structure, G.symm, Theory, Theory.simpleGraph_model_iff, loopless, simpleGraph_model_iff, structure
-/
instance simpleGraph_model (G : SimpleGraph V) :
    @Theory.Model _ V G.structure Theory.simpleGraph := by
  let := G.structure
  rw [Theory.simpleGraph_model_iff]
  exact ⟨G.loopless, G.symm⟩

variable (V) in
/-- Any model of the theory of simple graphs represents a simple graph. -/
@[simps]
/--
Definition of `simpleGraphOfStructure` / `simpleGraphOfStructure` 的定义

English:
definition simpleGraphOfStructure
  signature: [Language.graph.Structure V] [V ⊨ Theory.simpleGraph]
  body: RelMap adj ![x, y]

@[simp]

中文:
定义 simpleGraphOfStructure
  签名: [Language.graph.结构 V] [V ⊨ Theory.simpleGraph]
  定义体: RelMap adj ![x, y]

@[simp]

Depends on / 依赖: RelMap
-/
def simpleGraphOfStructure [Language.graph.Structure V] [V ⊨ Theory.simpleGraph] :
    SimpleGraph V where
  Adj x y := RelMap adj ![x, y]

@[simp]
/--
theorem `_root_.SimpleGraph.simpleGraphOfStructure` / 定理 `_root_.SimpleGraph.simpleGraphOfStructure`

English:
theorem _root_.SimpleGraph.simpleGraphOfStructure
  given: (G : SimpleGraph V)
  proof: by
  ext
  rfl

@[simp]

中文:
定理 _root_.简单图.simpleGraphOfStructure
  条件: (G : 简单图 V)
  证明: by
  ext
  rfl

@[simp]
-/
theorem _root_.SimpleGraph.simpleGraphOfStructure (G : SimpleGraph V) :
    @simpleGraphOfStructure V G.structure _ = G := by
  ext
  rfl

@[simp]
/--
theorem `structure_simpleGraphOfStructure` / 定理 `structure_simpleGraphOfStructure`

English:
theorem structure_simpleGraphOfStructure
  given: [S : Language.graph.Structure V] [V ⊨ Theory.simpleGraph]
  proof: by
  ext
  case funMap n f xs =>
    exact isEmptyElim f
  case RelMap n r xs =>
    match n, r with
    | 2, .adj =>
      rw [iff_eq_eq]
      change RelMap adj ![xs 0, xs 1] = _
      refine congr rfl (funext ?_)
      simp [Fin.forall_fin_two]

中文:
定理 structure_simpleGraphOfStructure
  条件: [S : Language.graph.结构 V] [V ⊨ Theory.simpleGraph]
  证明: by
  ext
  case funMap n f xs =>
    exact isEmptyElim f
  case RelMap n r xs =>
    match n, r with
    | 2, .adj =>
      rw [iff_eq_eq]
      change RelMap adj ![xs 0, xs 1] = _
      refine congr rfl (funext ?_)
      simp [Fin.forall_fin_two]

Depends on / 依赖: Fin.forall_fin_two, RelMap, forall_fin_two, funMap, iff_eq_eq, isEmptyElim
-/
theorem structure_simpleGraphOfStructure [S : Language.graph.Structure V] [V ⊨ Theory.simpleGraph] :
    (simpleGraphOfStructure V).structure = S := by
  ext
  case funMap n f xs =>
    exact isEmptyElim f
  case RelMap n r xs =>
    match n, r with
    | 2, .adj =>
      rw [iff_eq_eq]
      change RelMap adj ![xs 0, xs 1] = _
      refine congr rfl (funext ?_)
      simp [Fin.forall_fin_two]

/--
theorem `Theory.simpleGraph_isSatisfiable` / 定理 `Theory.simpleGraph_isSatisfiable`

English:
theorem Theory.simpleGraph_isSatisfiable
  statement: Theory.IsSatisfiable Theory.simpleGraph
  proof: ⟨@Theory.ModelType.of _ _ Unit (SimpleGraph.structure ⊥) _ _⟩

中文:
定理 Theory.simpleGraph_isSatisfiable
  结论: Theory.IsSatisfiable Theory.simpleGraph
  证明: ⟨@Theory.ModelType.of _ _ Unit (SimpleGraph.structure ⊥) _ _⟩

Depends on / 依赖: ModelType, SimpleGraph, SimpleGraph.structure, Theory, Theory.ModelType.of, structure
-/
theorem Theory.simpleGraph_isSatisfiable : Theory.IsSatisfiable Theory.simpleGraph :=
  ⟨@Theory.ModelType.of _ _ Unit (SimpleGraph.structure ⊥) _ _⟩

end Language

end FirstOrder
