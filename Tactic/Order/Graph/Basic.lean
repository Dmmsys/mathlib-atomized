/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Tactic.Order.CollectFacts
public meta import Mathlib.Util.AtomM

/-!
# Graphs for the `order` tactic

This module defines the `Graph` structure and basic operations on it. The `order` tactic uses
`≤`-graphs, where the vertices represent atoms, and an edge `(x, y)` exists if `x ≤ y`.
-/

public meta section

namespace Mathlib.Tactic.Order

open Lean Expr Meta

/-- An edge in a graph. In the `order` tactic, the `proof` field stores the of
`atoms[src] ≤ atoms[dst]`. -/
/-
**Mathlib.Tactic.Order.Edge** 是 Mathlib 中的一个归纳类型，位于命名空间 `Mathlib.Tactic.Order`。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An edge in a graph. In the `order` tactic, the `proof` field stores the of
`atoms[src] ≤ atoms[dst]`.
-/
structure Edge where
  /-- Source of the edge. -/
  src : Nat
  /-- Destination of the edge. -/
  dst : Nat
  /-- Proof of `atoms[src] ≤ atoms[dst]`. -/
  proof : Expr

-- For debugging purposes.
/-
**Mathlib.Tactic.Order.** 是 Mathlib 中的一个实例，位于命名空间 `Mathlib.Tactic.Order`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ToString Edge where
  toString e := s!"{e.src} ⟶ {e.dst}"

/-- If `g` is a `Graph`, then for a vertex with index `v`, `g[v]` is an array containing
the edges starting from this vertex. -/
/-
**Mathlib.Tactic.Order.Graph** 是 Mathlib 中的一个缩写定义，位于命名空间 `Mathlib.Tactic.Order`。
形式化陈述：Graph
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `g` is a `Graph`, then for a vertex with index `v`, `g[v]` is an array contai
ning
the edges starting from this vertex.
-/
abbrev Graph := Std.HashMap Nat (Array Edge)

namespace Graph

/-- Adds an `edge` to the graph. -/
/-
**Mathlib.Tactic.Order.Graph.addEdge** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.O
rder.Graph`。
形式化陈述：addEdge (g : Graph) (edge : Edge) : Graph
参数：g : Graph；edge : Edge。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Adds an `edge` to the graph.
-/
def addEdge (g : Graph) (edge : Edge) : Graph :=
  g.alter edge.src fun | none => #[edge] | some edges => edges.push edge

/-- Constructs a directed `Graph` using `≤` facts. It ignores all other facts. -/
/-
**Mathlib.Tactic.Order.Graph.constructLeGraph** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib
.Tactic.Order.Graph`。
形式化陈述：constructLeGraph (facts : Array AtomicFact) : MetaM Graph
参数：facts : Array AtomicFact。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructs a directed `Graph` using `≤` facts. It ignores all other facts.
-/
def constructLeGraph (facts : Array AtomicFact) : MetaM Graph := do
  let mut res : Graph := ∅
  for fact in facts do
    if let .le lhs rhs proof := fact then
      res := res.addEdge ⟨lhs, rhs, proof⟩
  return res

/-- State for the DFS algorithm. -/
/-
**Mathlib.Tactic.Order.Graph.DFSState** 是 Mathlib 中的一个结构，位于命名空间 `Mathlib.Tactic.
Order.Graph`。
形式化陈述：DFSState where /-- `visited.contains v` if and only if the algorithm has a
lready entered vertex `v`. -/ visited : Std.HashSet Nat  /-- DFS algorithm for c
onstructing a proof that `x ≤ y` by finding a path from `x` to `y` in the `≤`-gr
aph. -/ partial def buildTransitiveLeProofDFS (g : Graph) (v t : Nat) (tExpr : E
xpr) : StateT DFSState MetaM (Option Expr)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
State for the DFS algorithm.
-/
structure DFSState where
  /-- `visited.contains v` if and only if the algorithm has already entered vertex `v`. -/
  visited : Std.HashSet Nat

/-- DFS algorithm for constructing a proof that `x ≤ y` by finding a path from `x` to `y` in the
`≤`-graph. -/
/-
**Mathlib.Tactic.Order.Graph.buildTransitiveLeProofDFS** 是 Mathlib 中的一个不透明定义，位于命
名空间 `Mathlib.Tactic.Order.Graph`。
形式化陈述：Mathlib.Tactic.Order.Graph → ℕ → ℕ → Expr → StateT Mathlib.Tactic.Order.Gr
aph.DFSState MetaM (Option Expr)
参数：Option Expr。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
DFS algorithm for constructing a proof that `x ≤ y` by finding a path from `x` t
o `y` in the
`≤`-graph.
-/
partial def buildTransitiveLeProofDFS (g : Graph) (v t : Nat) (tExpr : Expr) :
    StateT DFSState MetaM (Option Expr) := do
  modify fun s => {s with visited := s.visited.insert v}
  if v == t then
    return ← mkAppM ``le_refl #[tExpr]
  if !g.contains v then
    return none
  for edge in g[v]! do
    let u := edge.dst
    if !(← get).visited.contains u then
      match ← buildTransitiveLeProofDFS g u t tExpr with
      | some pf => return some <| ← mkAppM ``le_trans #[edge.proof, pf]
      | none => continue
  return none

/-- Given a `≤`-graph `g`, finds a proof of `s ≤ t` using transitivity. -/
/-
**Mathlib.Tactic.Order.Graph.buildTransitiveLeProof** 是 Mathlib 中的一个定义，位于命名空间 `M
athlib.Tactic.Order.Graph`。
形式化陈述：buildTransitiveLeProof (g : Graph) (s t : Nat) : AtomM (Option Expr)
参数：g : Graph；s t : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a `≤`-graph `g`, finds a proof of `s ≤ t` using transitivity.
-/
def buildTransitiveLeProof (g : Graph) (s t : Nat) :
    AtomM (Option Expr) := do
  let state : DFSState := ⟨∅⟩
  (buildTransitiveLeProofDFS g s t ((← get).atoms[t]!)).run' state

end Graph

end Mathlib.Tactic.Order

