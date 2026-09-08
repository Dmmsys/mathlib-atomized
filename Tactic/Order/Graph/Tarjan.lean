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

/-- State for Tarjan's algorithm. -/
/-
**Mathlib.Tactic.Order.Graph.TarjanState** 是 Mathlib 中的一个结构，位于命名空间 `Mathlib.Tact
ic.Order.Graph`。
形式化陈述：TarjanState extends DFSState where /-- `id[v]` is the index of the vertex 
`v` in the DFS traversal. -/ id : Std.HashMap Nat Nat /-- `lowlink[v]` is the sm
allest index of any node on the stack that is reachable from `v` through `v`'s D
FS subtree. -/ lowlink : Std.HashMap Nat Nat /-- The stack of visited vertices u
sed in Tarjan's algorithm. -/ stack : Array Nat /-- `onStack.contains v` iff `v`
 is in `stack`. The structure is used to check it efficiently. -/ onStack : Std.
HashSet Nat /-- A time cou
继承自：DFSState。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
State for Tarjan's algorithm. -/
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

/-- The Tarjan's algorithm.
See [Wikipedia](https://en.wikipedia.org/wiki/Tarjan%27s_strongly_connected_components_algorithm). -/
/-
**Mathlib.Tactic.Order.Graph.tarjanDFS** 是 Mathlib 中的一个不透明定义，位于命名空间 `Mathlib.Tac
tic.Order.Graph`。
形式化陈述：Mathlib.Tactic.Order.Graph → ℕ → StateM Mathlib.Tactic.Order.Graph.TarjanS
tate Unit
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Tarjan's algorithm.
See [Wikipedia](https://en.wikipedia.org/wiki/Tarjan%27s_strongly_connected_comp
onents_algorithm).
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

/-- Implementation of `findSCCs` in the `StateM TarjanState` monad. -/
/-
**Mathlib.Tactic.Order.Graph.findSCCsImp** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tact
ic.Order.Graph`。
形式化陈述：findSCCsImp (g : Graph) : StateM TarjanState Unit
参数：g : Graph。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Implementation of `findSCCs` in the `StateM TarjanState` monad.
-/
def findSCCsImp (g : Graph) : StateM TarjanState Unit := do
  for (v, _) in g do
    if !(← get).visited.contains v then
      tarjanDFS g v

/-- Finds the strongly connected components of the graph `g`. Returns a hashmap where the value at
key `v` represents the SCC number containing vertex `v`. The numbering of SCCs is arbitrary. -/
/-
**Mathlib.Tactic.Order.Graph.findSCCs** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.
Order.Graph`。
形式化陈述：findSCCs (g : Graph) : Std.HashMap Nat Nat
参数：g : Graph。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Finds the strongly connected components of the graph `g`. Returns a hashmap wher
e the value at
key `v` represents the SCC number containing vertex `v`. The numbering of SCCs i
s arbitrary.
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
  (findSCCsImp g).run s |>.snd.lowlink

end Mathlib.Tactic.Order.Graph

