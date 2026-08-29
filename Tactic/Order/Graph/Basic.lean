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

/--
Definition of `Edge` / `Edge` 的定义

English:
structure Edge
  parameters: where
  axioms and operations (3):
    - src : Nat
    - dst : Nat
    - proof : Expr

中文:
结构 Edge
  参数: where
  公理与运算 (3 个):
    - src : 自然数
    - dst : 自然数
    - proof : Expr
-/
structure Edge where
  /-- Source of the edge. -/
  src : Nat
  /-- Destination of the edge. -/
  dst : Nat
  /-- Proof of `atoms[src] ≤ atoms[dst]`. -/
  proof : Expr

-- For debugging purposes.
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ToString Edge
  body: s!"{e.src} ⟶ {e.dst}"

中文:
实例 :
  签名: ToString Edge
  定义体: s!"{e.src} ⟶ {e.dst}"

Depends on / 依赖: e.dst, e.src
-/
instance : ToString Edge where
  toString e := s!"{e.src} ⟶ {e.dst}"

/--
Definition of `Graph` / `Graph` 的定义

English:
abbreviation Graph
  body: Std.HashMap Nat (Array Edge)

中文:
缩写 Graph
  定义体: Std.HashMap Nat (Array Edge)

Depends on / 依赖: HashMap, Std.HashMap
-/
abbrev Graph := Std.HashMap Nat (Array Edge)

namespace Graph

/--
Definition of `addEdge` / `addEdge` 的定义

English:
definition addEdge
  signature: (g : Graph) (edge : Edge)
  body: g.alter edge.src fun | none => #[edge] | some edges => edges.push edge

中文:
定义 addEdge
  签名: (g : Graph) (edge : Edge)
  定义体: g.alter edge.src fun | none => #[edge] | some edges => edges.push edge

Depends on / 依赖: edge.src, edges.push, g.alter
-/
def addEdge (g : Graph) (edge : Edge) : Graph :=
  g.alter edge.src fun | none => #[edge] | some edges => edges.push edge

/--
Definition of `constructLeGraph` / `constructLeGraph` 的定义

English:
definition constructLeGraph
  signature: (facts : Array AtomicFact)
  body: do
  let mut res : Graph := ∅
  for fact in facts do
    if let .le lhs rhs proof := fact then
      res := res.addEdge ⟨lhs, rhs, proof⟩
  return res

中文:
定义 constructLeGraph
  签名: (facts : Array AtomicFact)
  定义体: do
  let mut res : Graph := ∅
  for fact in facts do
    if let .le lhs rhs proof := fact then
      res := res.addEdge ⟨lhs, rhs, proof⟩
  return res
-/
def constructLeGraph (facts : Array AtomicFact) : MetaM Graph := do
  let mut res : Graph := ∅
  for fact in facts do
    if let .le lhs rhs proof := fact then
      res := res.addEdge ⟨lhs, rhs, proof⟩
  return res

/--
Definition of `DFSState` / `DFSState` 的定义

English:
structure DFSState
  parameters: where
  axioms and operations (1):
    - visited : Std.HashSet Nat

中文:
结构 DFSState
  参数: where
  公理与运算 (1 个):
    - visited : Std.HashSet 自然数
-/
structure DFSState where
  /-- `visited.contains v` if and only if the algorithm has already entered vertex `v`. -/
  visited : Std.HashSet Nat

/--
Definition of `buildTransitiveLeProofDFS` / `buildTransitiveLeProofDFS` 的定义

English:
definition buildTransitiveLeProofDFS
  signature: (g : Graph) (v t : Nat) (tExpr : Expr)
  body: do
  modify fun s => {s with visited := s.visited.insert v}
  if v == t then
    return ← mkAppM ``le_refl #[tExpr]
  if !g.contains v then
    return none
  for edge in g[v]! do
    let u := edge.dst
    if !(← get).visited.contains u then
      match ← buildTransitiveLeProofDFS g u t tExpr with
| 

中文:
定义 buildTransitiveLeProofDFS
  签名: (g : Graph) (v t : 自然数) (tExpr : Expr)
  定义体: do
  modify fun s => {s with visited := s.visited.insert v}
  if v == t then
    return ← mkAppM ``le_refl #[tExpr]
  if !g.contains v then
    return none
  for edge in g[v]! do
    let u := edge.dst
    if !(← get).visited.contains u then
      match ← buildTransitiveLeProofDFS g u t tExpr with
| 
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
| some pf => return some ← mkAppM ``le_trans #[edge.proof, pf]
      | none => continue
  return none

/--
Definition of `buildTransitiveLeProof` / `buildTransitiveLeProof` 的定义

English:
definition buildTransitiveLeProof
  signature: (g : Graph) (s t : Nat)
  body: do
  let state : DFSState := ⟨∅⟩
  (buildTransitiveLeProofDFS g s t ((← get).atoms[t]!)).run' state

中文:
定义 buildTransitiveLeProof
  签名: (g : Graph) (s t : 自然数)
  定义体: do
  let state : DFSState := ⟨∅⟩
  (buildTransitiveLeProofDFS g s t ((← get).atoms[t]!)).run' state
-/
def buildTransitiveLeProof (g : Graph) (s t : Nat) :
    AtomM (Option Expr) := do
  let state : DFSState := ⟨∅⟩
  (buildTransitiveLeProofDFS g s t ((← get).atoms[t]!)).run' state

end Graph

end Mathlib.Tactic.Order
