/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public meta import Mathlib.Tactic.Order.Graph.Basic
public import Mathlib.Tactic.Order.Graph.Basic

/-!
# Tarjan's Algorithm

This file implements Tarjan's algorithm for finding the strongly connected components (SCCs) of
a graph.
-/

public meta section

namespace Mathlib.Tactic.Order.Graph

/--
Definition of `TarjanState` / `TarjanState` 的定义

English:
structure TarjanState
  parameters: extends DFSState
  extends: DFSState
  axioms and operations (5):
    - id : Std.HashMap Nat Nat
    - lowlink : Std.HashMap Nat Nat
    - stack : Array Nat
    - onStack : Std.HashSet Nat
    - time : Nat

中文:
结构 TarjanState
  参数: extends DFSState
  继承: DFSState
  公理与运算 (5 个):
    - id : Std.HashMap 自然数 自然数
    - lowlink : Std.HashMap 自然数 自然数
    - stack : 数组 自然数
    - onStack : Std.HashSet 自然数
    - time : 自然数
-/
structure TarjanState extends DFSState where
  /-- `id[v]` is the index of the vertex `v` in the DFS traversal. -/
  id : Std.HashMap Nat Nat
  /-- `lowlink[v]` is the smallest index of any node on the stack that is reachable from `v`
  through `v`'s DFS subtree. -/
  lowlink : Std.HashMap Nat Nat
  /-- The stack of visited vertices used in Tarjan's algorithm. -/
  stack : Array Nat
  /-- `onStack.contains v` iff `v` is in `stack`. The structure is used to check it efficiently. -/
  onStack : Std.HashSet Nat
  /-- A time counter that increments each time the algorithm visits an unvisited vertex. -/
  time : Nat

/--
Definition of `tarjanDFS` / `tarjanDFS` 的定义

English:
definition tarjanDFS
  signature: (g : Graph) (v : Nat)
  body: do
  modify fun s => {
    visited := s.visited.insert v,
    id := s.id.insert v s.time,
    lowlink := s.lowlink.insert v s.time,
    stack := s.stack.push v,
    onStack := s.onStack.insert v,
    time := s.time + 1
  }

  if g.contains v then
    for edge in g[v]! do
      let u := edge.dst
    

中文:
定义 tarjanDFS
  签名: (g : 图) (v : 自然数)
  定义体: do
  modify fun s => {
    visited := s.visited.insert v,
    id := s.id.insert v s.time,
    lowlink := s.lowlink.insert v s.time,
    stack := s.stack.push v,
    onStack := s.onStack.insert v,
    time := s.time + 1
  }

  if g.contains v then
    for edge in g[v]! do
      let u := edge.dst
    
-/
partial def tarjanDFS (g : Graph) (v : Nat) : StateM TarjanState Unit := do
  modify fun s => {
    visited := s.visited.insert v,
    id := s.id.insert v s.time,
    lowlink := s.lowlink.insert v s.time,
    stack := s.stack.push v,
    onStack := s.onStack.insert v,
    time := s.time + 1
  }

  if g.contains v then
    for edge in g[v]! do
      let u := edge.dst
      if !(← get).visited.contains u then
        tarjanDFS g u
        modify fun s => {s with
          lowlink := s.lowlink.insert v (min s.lowlink[v]! s.lowlink[u]!),
        }
      else if (← get).onStack.contains u then
        modify fun s => {s with
          lowlink := s.lowlink.insert v (min s.lowlink[v]! s.id[u]!),
        }

  if (← get).id[v]! = (← get).lowlink[v]! then
    let mut w := 0
    while true do
      w := (← get).stack.back!
      modify fun s => {s with
        stack := s.stack.pop
        onStack := s.onStack.erase w
        lowlink := s.lowlink.insert w s.lowlink[v]!
      }
      if w = v then
        break

/--
Definition of `findSCCsImp` / `findSCCsImp` 的定义

English:
definition findSCCsImp
  signature: (g : Graph)
  body: do
  for (v, _) in g do
    if !(← get).visited.contains v then
      tarjanDFS g v

中文:
定义 findSCCsImp
  签名: (g : 图)
  定义体: do
  for (v, _) in g do
    if !(← get).visited.contains v then
      tarjanDFS g v
-/
def findSCCsImp (g : Graph) : StateM TarjanState Unit := do
  for (v, _) in g do
    if !(← get).visited.contains v then
      tarjanDFS g v

/--
Definition of `findSCCs` / `findSCCs` 的定义

English:
definition findSCCs
  signature: (g : Graph)
  body: let s : TarjanState := {
    visited := ∅
    id := ∅
    lowlink := ∅
    stack := #[]
    onStack := ∅
    time := 0
  }
.snd.lowlink (findSCCsImp g).run s

中文:
定义 findSCCs
  签名: (g : 图)
  定义体: let s : TarjanState := {
    visited := ∅
    id := ∅
    lowlink := ∅
    stack := #[]
    onStack := ∅
    time := 0
  }
.snd.lowlink (findSCCsImp g).run s

Depends on / 依赖: TarjanState, findSCCsImp, lowlink, onStack, snd.lowlink, visited
-/
def findSCCs (g : Graph) : Std.HashMap Nat Nat :=
  let s : TarjanState := {
    visited := ∅
    id := ∅
    lowlink := ∅
    stack := #[]
    onStack := ∅
    time := 0
  }
.snd.lowlink (findSCCsImp g).run s

end Mathlib.Tactic.Order.Graph
