/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Peter Nelson
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Dart

/-!
# Walks

In a simple graph, a *walk* is a finite sequence of adjacent vertices, and can be
thought of equally well as a sequence of directed edges.

**Warning:** graph theorists mean something different by "path" than
do homotopy theorists. A "walk" in graph theory is a "path" in
homotopy theory. Another warning: some graph theorists use "path" and
"simple path" for "walk" and "path."

Some definitions and theorems have inspiration from multigraph
counterparts in [Chou1994].

## Main definitions

* `SimpleGraph.Walk` (with accompanying pattern definitions
  `SimpleGraph.Walk.nil'` and `SimpleGraph.Walk.cons'`)
* `SimpleGraph.Walk.Nil`: A predicate for the empty walk
* `SimpleGraph.Walk.length`: The length of a walk
* `SimpleGraph.Walk.support`: The list of vertices a walk visits in order
* `SimpleGraph.Walk.darts`: The list of darts a walk visits in order
* `SimpleGraph.Walk.edges`: The list of edges a walk visits in order
* `SimpleGraph.Walk.edgeSet`: The set of edges of a walk visits

## Tags
walks
-/

@[expose] public section

namespace SimpleGraph

universe u
variable {V : Type u} (G : SimpleGraph V) {u v w : V}

/--
Inductive type `Walk` / 归纳类型 `Walk`

English:
inductive Walk
  parameters: : V -> V -> Type u
  constructors (2):
    - nil: {u : V} : Walk u u
    - cons: {u v w : V} (h : G.Adj u v) (p : Walk v w) : Walk u w

中文:
归纳类型 Walk
  参数: : V -> V -> 类型u
  构造子 (2 个):
    - nil: {u : V} : Walk u u
    - cons: {u v w : V} (h : G.Adj u v) (p : Walk v w) : Walk u w
-/
inductive Walk : V -> V -> Type u
  | nil {u : V} : Walk u u
  | cons {u v w : V} (h : G.Adj u v) (p : Walk v w) : Walk u w
  deriving DecidableEq

attribute [refl] Walk.nil

@[simps]
/--
Instance `Walk.instInhabited` / 实例 `Walk.instInhabited`

English:
instance Walk.instInhabited
  signature: (v : V)
  body: ⟨Walk.nil⟩

中文:
实例 Walk.instInhabited
  签名: (v : V)
  定义体: ⟨Walk.nil⟩

Depends on / 依赖: Walk.nil
-/
instance Walk.instInhabited (v : V) : Inhabited (G.Walk v v) := ⟨Walk.nil⟩

/-- The one-edge walk associated to a pair of adjacent vertices. -/
@[match_pattern, reducible]
/--
Definition of `Adj.toWalk` / `Adj.toWalk` 的定义

English:
definition Adj.toWalk
  signature: {G : SimpleGraph V} {u v : V} (h : G.Adj u v)
  body: Walk.cons h Walk.nil

中文:
定义 Adj.toWalk
  签名: {G : SimpleGraph V} {u v : V} (h : G.Adj u v)
  定义体: Walk.cons h Walk.nil

Depends on / 依赖: Walk.cons, Walk.nil
-/
def Adj.toWalk {G : SimpleGraph V} {u v : V} (h : G.Adj u v) : G.Walk u v :=
  Walk.cons h Walk.nil

namespace Walk

variable {G}

/-- Pattern to get `Walk.nil` with the vertex as an explicit argument. -/
@[match_pattern]
/--
Definition of `nil'` / `nil'` 的定义

English:
abbreviation nil'
  signature: (u : V)
  body: Walk.nil

中文:
缩写 nil'
  签名: (u : V)
  定义体: Walk.nil

Depends on / 依赖: Walk.nil
-/
abbrev nil' (u : V) : G.Walk u u := Walk.nil

/-- Pattern to get `Walk.cons` with the vertices as explicit arguments. -/
@[match_pattern]
/--
Definition of `cons'` / `cons'` 的定义

English:
abbreviation cons'
  signature: (u v w : V) (h : G.Adj u v) (p : G.Walk v w)
  body: Walk.cons h p

中文:
缩写 cons'
  签名: (u v w : V) (h : G.Adj u v) (p : G.Walk v w)
  定义体: Walk.cons h p

Depends on / 依赖: Walk.cons
-/
abbrev cons' (u v w : V) (h : G.Adj u v) (p : G.Walk v w) : G.Walk u w := Walk.cons h p

/--
theorem `exists_eq_cons_of_ne` / 定理 `exists_eq_cons_of_ne`

English:
theorem exists_eq_cons_of_ne
  given: {u v : V} (hne : u != v)

中文:
定理 exists_eq_cons_of_ne
  条件: {u v : V} (hne : u != v)
-/
theorem exists_eq_cons_of_ne {u v : V} (hne : u != v) :
    forall (p : G.Walk u v), exists (w : V) (h : G.Adj u w) (p' : G.Walk w v), p = cons h p'
  | nil => (hne rfl).elim
  | cons h p' => ⟨_, h, p', rfl⟩

/--
Definition of `length` / `length` 的定义

English:
definition length
  signature: {u v : V}

中文:
定义 length
  签名: {u v : V}
-/
def length {u v : V} : G.Walk u v -> Nat
  | nil => 0
  | cons _ q => q.length.succ

@[simp]
/--
theorem `length_nil` / 定理 `length_nil`

English:
theorem length_nil
  given: {u : V}
  statement: (nil : G.Walk u u).length = 0
  proof: rfl

@[simp]

中文:
定理 length_nil
  条件: {u : V}
  结论: (nil : G.Walk u u).length = 0
  证明: rfl

@[simp]
-/
theorem length_nil {u : V} : (nil : G.Walk u u).length = 0 := rfl

@[simp]
/--
theorem `length_cons` / 定理 `length_cons`

English:
theorem length_cons
  given: {u v w : V} (h : G.Adj u v) (p : G.Walk v w)
  proof: rfl

中文:
定理 length_cons
  条件: {u v w : V} (h : G.Adj u v) (p : G.Walk v w)
  证明: rfl
-/
theorem length_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (cons h p).length = p.length + 1 := rfl

/--
theorem `_root_.SimpleGraph.Adj.length_toWalk` / 定理 `_root_.SimpleGraph.Adj.length_toWalk`

English:
theorem _root_.SimpleGraph.Adj.length_toWalk
  given: (h : G.Adj u v)
  statement: h.toWalk.length = 1
  proof: by
  simp

中文:
定理 _root_.SimpleGraph.Adj.length_toWalk
  条件: (h : G.Adj u v)
  结论: h.toWalk.length = 1
  证明: by
  simp
-/
theorem _root_.SimpleGraph.Adj.length_toWalk (h : G.Adj u v) : h.toWalk.length = 1 := by
  simp

/--
theorem `eq_of_length_eq_zero` / 定理 `eq_of_length_eq_zero`

English:
theorem eq_of_length_eq_zero
  given: {u v : V}
  statement: forall {p : G.Walk u v}, p.length = 0 -> u = v

中文:
定理 eq_of_length_eq_zero
  条件: {u v : V}
  结论: 对任意 {p : G.Walk u v}, p.length = 0 -> u = v
-/
theorem eq_of_length_eq_zero {u v : V} : forall {p : G.Walk u v}, p.length = 0 -> u = v
  | nil, _ => rfl

/--
theorem `adj_of_length_eq_one` / 定理 `adj_of_length_eq_one`

English:
theorem adj_of_length_eq_one
  given: {u v : V}
  statement: forall {p : G.Walk u v}, p.length = 1 -> G.Adj u v

中文:
定理 adj_of_length_eq_one
  条件: {u v : V}
  结论: 对任意 {p : G.Walk u v}, p.length = 1 -> G.Adj u v
-/
theorem adj_of_length_eq_one {u v : V} : forall {p : G.Walk u v}, p.length = 1 -> G.Adj u v
  | cons h nil, _ => h

/--
theorem `exists_length_eq_zero_iff` / 定理 `exists_length_eq_zero_iff`

English:
theorem exists_length_eq_zero_iff
  given: {u v : V}
  statement: (exists p : G.Walk u v, p.length = 0) ↔ u = v
  proof: ⟨fun ⟨_, h⟩ => (eq_of_length_eq_zero h), (· ▸ ⟨nil, rfl⟩)⟩

@[simp]

中文:
定理 exists_length_eq_zero_iff
  条件: {u v : V}
  结论: (存在 p : G.Walk u v, p.length = 0) ↔ u = v
  证明: ⟨fun ⟨_, h⟩ => (eq_of_length_eq_zero h), (· ▸ ⟨nil, rfl⟩)⟩

@[simp]

Depends on / 依赖: eq_of_length_eq_zero
-/
theorem exists_length_eq_zero_iff {u v : V} : (exists p : G.Walk u v, p.length = 0) ↔ u = v :=
  ⟨fun ⟨_, h⟩ => (eq_of_length_eq_zero h), (· ▸ ⟨nil, rfl⟩)⟩

@[simp]
/--
lemma `exists_length_eq_one_iff` / 引理 `exists_length_eq_one_iff`

English:
lemma exists_length_eq_one_iff
  given: {u v : V}
  statement: (exists (p : G.Walk u v), p.length = 1) ↔ G.Adj u v
  proof: ⟨fun ⟨_, hp⟩ => adj_of_length_eq_one hp, (⟨·.toWalk, by simp⟩)⟩

中文:
引理 exists_length_eq_one_iff
  条件: {u v : V}
  结论: (存在 (p : G.Walk u v), p.length = 1) ↔ G.Adj u v
  证明: ⟨fun ⟨_, hp⟩ => adj_of_length_eq_one hp, (⟨·.toWalk, by simp⟩)⟩

Depends on / 依赖: adj_of_length_eq_one, toWalk
-/
lemma exists_length_eq_one_iff {u v : V} : (exists (p : G.Walk u v), p.length = 1) ↔ G.Adj u v :=
  ⟨fun ⟨_, hp⟩ => adj_of_length_eq_one hp, (⟨·.toWalk, by simp⟩)⟩

/--
theorem `eq_of_length_le_one` / 定理 `eq_of_length_le_one`

English:
theorem eq_of_length_le_one
  given: {p q : G.Walk u v} (hp : p.length <= 1) (hq : q.length <= 1)
  statement: p = q
  proof: by
  grind [cases Walk, length_cons, Adj.ne]

中文:
定理 eq_of_length_le_one
  条件: {p q : G.Walk u v} (hp : p.length <= 1) (hq : q.length <= 1)
  结论: p = q
  证明: by
  grind [cases Walk, length_cons, Adj.ne]

Depends on / 依赖: Adj.ne, length_cons
-/
theorem eq_of_length_le_one {p q : G.Walk u v} (hp : p.length <= 1) (hq : q.length <= 1) : p = q := by
  grind [cases Walk, length_cons, Adj.ne]

/--
Definition of `support` / `support` 的定义

English:
definition support
  signature: {u v : V}

中文:
定义 support
  签名: {u v : V}
-/
def support {u v : V} : G.Walk u v -> List V
  | nil => [u]
  | cons _ p => u :: p.support

/--
Definition of `darts` / `darts` 的定义

English:
definition darts
  signature: {u v : V}

中文:
定义 darts
  签名: {u v : V}
-/
def darts {u v : V} : G.Walk u v -> List G.Dart
  | nil => []
  | cons h p => ⟨(u, _), h⟩ :: p.darts

/--
Definition of `edges` / `edges` 的定义

English:
definition edges
  signature: {u v : V} (p : G.Walk u v)
  body: p.darts.map Dart.edge

中文:
定义 edges
  签名: {u v : V} (p : G.Walk u v)
  定义体: p.darts.map Dart.edge

Depends on / 依赖: Dart.edge, p.darts.map
-/
def edges {u v : V} (p : G.Walk u v) : List (Sym2 V) := p.darts.map Dart.edge

/--
theorem `edges_eq_map_darts` / 定理 `edges_eq_map_darts`

English:
theorem edges_eq_map_darts
  given: (p : G.Walk u v)
  statement: p.edges = p.darts.map Dart.edge
  proof: rfl

@[simp]

中文:
定理 edges_eq_map_darts
  条件: (p : G.Walk u v)
  结论: p.edges = p.darts.map Dart.edge
  证明: rfl

@[simp]
-/
theorem edges_eq_map_darts (p : G.Walk u v) : p.edges = p.darts.map Dart.edge :=
  rfl

@[simp]
/--
theorem `support_nil` / 定理 `support_nil`

English:
theorem support_nil
  given: {u : V}
  statement: (nil : G.Walk u u).support = [u]
  proof: rfl

@[simp, grind =]

中文:
定理 support_nil
  条件: {u : V}
  结论: (nil : G.Walk u u).support = [u]
  证明: rfl

@[simp, grind =]
-/
theorem support_nil {u : V} : (nil : G.Walk u u).support = [u] := rfl

@[simp, grind =]
/--
theorem `support_cons` / 定理 `support_cons`

English:
theorem support_cons
  given: {u v w : V} (h : G.Adj u v) (p : G.Walk v w)
  proof: rfl

中文:
定理 support_cons
  条件: {u v w : V} (h : G.Adj u v) (p : G.Walk v w)
  证明: rfl
-/
theorem support_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (cons h p).support = u :: p.support := rfl

/--
theorem `_root_.SimpleGraph.Adj.support_toWalk` / 定理 `_root_.SimpleGraph.Adj.support_toWalk`

English:
theorem _root_.SimpleGraph.Adj.support_toWalk
  given: (h : G.Adj u v)
  statement: h.toWalk.support = [u, v]
  proof: rfl

@[simp]

中文:
定理 _root_.SimpleGraph.Adj.support_toWalk
  条件: (h : G.Adj u v)
  结论: h.toWalk.support = [u, v]
  证明: rfl

@[simp]
-/
theorem _root_.SimpleGraph.Adj.support_toWalk (h : G.Adj u v) : h.toWalk.support = [u, v] :=
  rfl

@[simp]
/--
theorem `support_ne_nil` / 定理 `support_ne_nil`

English:
theorem support_ne_nil
  given: {u v : V} (p : G.Walk u v)
  statement: p.support != []
  proof: by cases p <;> simp

@[simp]

中文:
定理 support_ne_nil
  条件: {u v : V} (p : G.Walk u v)
  结论: p.support != []
  证明: by cases p <;> simp

@[simp]
-/
theorem support_ne_nil {u v : V} (p : G.Walk u v) : p.support != [] := by cases p <;> simp

@[simp]
/--
theorem `head_support` / 定理 `head_support`

English:
theorem head_support
  given: {G : SimpleGraph V} {a b : V} (p : G.Walk a b)
  proof: by cases p <;> simp

@[simp]

中文:
定理 head_support
  条件: {G : SimpleGraph V} {a b : V} (p : G.Walk a b)
  证明: by cases p <;> simp

@[simp]
-/
theorem head_support {G : SimpleGraph V} {a b : V} (p : G.Walk a b) :
    p.support.head (by simp) = a := by cases p <;> simp

@[simp]
/--
theorem `getLast_support` / 定理 `getLast_support`

English:
theorem getLast_support
  given: {G : SimpleGraph V} {a b : V} (p : G.Walk a b)
  proof: by
  induction p <;> simp [*]

@[simp]

中文:
定理 getLast_support
  条件: {G : SimpleGraph V} {a b : V} (p : G.Walk a b)
  证明: by
  induction p <;> simp [*]

@[simp]
-/
theorem getLast_support {G : SimpleGraph V} {a b : V} (p : G.Walk a b) :
    p.support.getLast (by simp) = b := by
  induction p <;> simp [*]

@[simp]
/--
lemma `cons_tail_support` / 引理 `cons_tail_support`

English:
lemma cons_tail_support
  given: (p : G.Walk u v)
  statement: u :: p.support.tail = p.support
  proof: by
  cases p <;> simp

@[deprecated cons_tail_support (since := "2026-03-16")]

中文:
引理 cons_tail_support
  条件: (p : G.Walk u v)
  结论: u :: p.support.tail = p.support
  证明: by
  cases p <;> simp

@[deprecated cons_tail_support (since := "2026-03-16")]
-/
lemma cons_tail_support (p : G.Walk u v) : u :: p.support.tail = p.support := by
  cases p <;> simp

@[deprecated cons_tail_support (since := "2026-03-16")]
/--
theorem `support_eq_cons` / 定理 `support_eq_cons`

English:
theorem support_eq_cons
  given: {u v : V} (p : G.Walk u v)
  statement: p.support = u :: p.support.tail
  proof: by
  cases p <;> simp

@[simp]

中文:
定理 support_eq_cons
  条件: {u v : V} (p : G.Walk u v)
  结论: p.support = u :: p.support.tail
  证明: by
  cases p <;> simp

@[simp]
-/
theorem support_eq_cons {u v : V} (p : G.Walk u v) : p.support = u :: p.support.tail := by
  cases p <;> simp

@[simp]
/--
theorem `start_mem_support` / 定理 `start_mem_support`

English:
theorem start_mem_support
  given: {u v : V} (p : G.Walk u v)
  statement: u in p.support
  proof: by cases p <;> simp

@[simp]

中文:
定理 start_mem_support
  条件: {u v : V} (p : G.Walk u v)
  结论: u in p.support
  证明: by cases p <;> simp

@[simp]
-/
theorem start_mem_support {u v : V} (p : G.Walk u v) : u in p.support := by cases p <;> simp

@[simp]
/--
theorem `end_mem_support` / 定理 `end_mem_support`

English:
theorem end_mem_support
  given: {u v : V} (p : G.Walk u v)
  statement: v in p.support
  proof: by induction p <;> simp [*]

@[simp]

中文:
定理 end_mem_support
  条件: {u v : V} (p : G.Walk u v)
  结论: v in p.support
  证明: by induction p <;> simp [*]

@[simp]
-/
theorem end_mem_support {u v : V} (p : G.Walk u v) : v in p.support := by induction p <;> simp [*]

@[simp]
/--
theorem `support_nonempty` / 定理 `support_nonempty`

English:
theorem support_nonempty
  given: {u v : V} (p : G.Walk u v)
  statement: { w | w in p.support }.Nonempty
  proof: ⟨u, by simp⟩

中文:
定理 support_nonempty
  条件: {u v : V} (p : G.Walk u v)
  结论: { w | w in p.support }.Nonempty
  证明: ⟨u, by simp⟩
-/
theorem support_nonempty {u v : V} (p : G.Walk u v) : { w | w in p.support }.Nonempty :=
  ⟨u, by simp⟩

/--
theorem `mem_support_iff` / 定理 `mem_support_iff`

English:
theorem mem_support_iff
  given: {u v w : V} (p : G.Walk u v)
  proof: by cases p <;> simp

中文:
定理 mem_support_iff
  条件: {u v w : V} (p : G.Walk u v)
  证明: by cases p <;> simp
-/
theorem mem_support_iff {u v w : V} (p : G.Walk u v) :
    w in p.support ↔ w = u ∨ w in p.support.tail := by cases p <;> simp

/--
theorem `mem_support_nil_iff` / 定理 `mem_support_nil_iff`

English:
theorem mem_support_nil_iff
  given: {u v : V}
  statement: u in (nil : G.Walk v v).support ↔ u = v
  proof: by simp

@[simp]

中文:
定理 mem_support_nil_iff
  条件: {u v : V}
  结论: u in (nil : G.Walk v v).support ↔ u = v
  证明: by simp

@[simp]
-/
theorem mem_support_nil_iff {u v : V} : u in (nil : G.Walk v v).support ↔ u = v := by simp

@[simp]
/--
theorem `end_mem_tail_support_of_ne` / 定理 `end_mem_tail_support_of_ne`

English:
theorem end_mem_tail_support_of_ne
  given: {u v : V} (h : u != v) (p : G.Walk u v)
  statement: v in p.support.tail
  proof: by
  obtain ⟨_, _, _, rfl⟩ := exists_eq_cons_of_ne h p
  simp

中文:
定理 end_mem_tail_support_of_ne
  条件: {u v : V} (h : u != v) (p : G.Walk u v)
  结论: v in p.support.tail
  证明: by
  obtain ⟨_, _, _, rfl⟩ := exists_eq_cons_of_ne h p
  simp

Depends on / 依赖: exists_eq_cons_of_ne
-/
theorem end_mem_tail_support_of_ne {u v : V} (h : u != v) (p : G.Walk u v) : v in p.support.tail := by
  obtain ⟨_, _, _, rfl⟩ := exists_eq_cons_of_ne h p
  simp

/--
theorem `support_suffix_support_cons` / 定理 `support_suffix_support_cons`

English:
theorem support_suffix_support_cons
  given: (p : G.Walk v w) (hadj : G.Adj u v)
  proof: by
  simp

中文:
定理 support_suffix_support_cons
  条件: (p : G.Walk v w) (hadj : G.Adj u v)
  证明: by
  simp
-/
theorem support_suffix_support_cons (p : G.Walk v w) (hadj : G.Adj u v) :
    p.support <:+ (p.cons hadj).support := by
  simp

/--
theorem `support_subset_support_cons` / 定理 `support_subset_support_cons`

English:
theorem support_subset_support_cons
  given: {u v w : V} (p : G.Walk v w) (hadj : G.Adj u v)
  proof: by
  simp

中文:
定理 support_subset_support_cons
  条件: {u v w : V} (p : G.Walk v w) (hadj : G.Adj u v)
  证明: by
  simp
-/
theorem support_subset_support_cons {u v w : V} (p : G.Walk v w) (hadj : G.Adj u v) :
    p.support subseteq (p.cons hadj).support := by
  simp

/--
theorem `coe_support` / 定理 `coe_support`

English:
theorem coe_support
  given: {u v : V} (p : G.Walk u v)
  proof: by cases p <;> rfl

中文:
定理 coe_support
  条件: {u v : V} (p : G.Walk u v)
  证明: by cases p <;> rfl
-/
theorem coe_support {u v : V} (p : G.Walk u v) :
    (p.support : Multiset V) = {u} + p.support.tail := by cases p <;> rfl

/--
theorem `isChain_adj_cons_support` / 定理 `isChain_adj_cons_support`

English:
theorem isChain_adj_cons_support
  given: {u v w : V} (h : G.Adj u v)

中文:
定理 isChain_adj_cons_support
  条件: {u v w : V} (h : G.Adj u v)
-/
theorem isChain_adj_cons_support {u v w : V} (h : G.Adj u v) :
    forall (p : G.Walk v w), List.IsChain G.Adj (u :: p.support)
  | nil => .cons_cons h (.singleton _)
  | cons h' p => .cons_cons h (isChain_adj_cons_support h' p)

/--
theorem `isChain_adj_support` / 定理 `isChain_adj_support`

English:
theorem isChain_adj_support
  given: {u v : V}
  statement: forall (p : G.Walk u v), List.IsChain G.Adj p.support

中文:
定理 isChain_adj_support
  条件: {u v : V}
  结论: 对任意 (p : G.Walk u v), List.IsChain G.Adj p.support
-/
theorem isChain_adj_support {u v : V} : forall (p : G.Walk u v), List.IsChain G.Adj p.support
  | nil => .singleton _
  | cons h p => isChain_adj_cons_support h p

/--
theorem `isChain_dartAdj_cons_darts` / 定理 `isChain_dartAdj_cons_darts`

English:
theorem isChain_dartAdj_cons_darts
  given: {d : G.Dart} {v w : V} (h : d.snd = v) (p : G.Walk v w)
  proof: by
  induction p generalizing d with
  | nil => exact .singleton _
  | cons h' p ih => exact .cons_cons h (ih rfl)

中文:
定理 isChain_dartAdj_cons_darts
  条件: {d : G.Dart} {v w : V} (h : d.snd = v) (p : G.Walk v w)
  证明: by
  induction p generalizing d with
  | nil => exact .singleton _
  | cons h' p ih => exact .cons_cons h (ih rfl)

Depends on / 依赖: cons_cons, generalizing, singleton
-/
theorem isChain_dartAdj_cons_darts {d : G.Dart} {v w : V} (h : d.snd = v) (p : G.Walk v w) :
    List.IsChain G.DartAdj (d :: p.darts) := by
  induction p generalizing d with
  | nil => exact .singleton _
  | cons h' p ih => exact .cons_cons h (ih rfl)

/--
theorem `isChain_dartAdj_darts` / 定理 `isChain_dartAdj_darts`

English:
theorem isChain_dartAdj_darts
  given: {u v : V}
  statement: forall (p : G.Walk u v), List.IsChain G.DartAdj p.darts

中文:
定理 isChain_dartAdj_darts
  条件: {u v : V}
  结论: 对任意 (p : G.Walk u v), List.IsChain G.DartAdj p.darts
-/
theorem isChain_dartAdj_darts {u v : V} : forall (p : G.Walk u v), List.IsChain G.DartAdj p.darts
  | nil => .nil
  -- Porting note: needed to defer `rfl` to help elaboration
  | cons h p => isChain_dartAdj_cons_darts (by rfl) p

/--
theorem `edges_subset_edgeSet` / 定理 `edges_subset_edgeSet`

English:
theorem edges_subset_edgeSet
  given: {u v : V}

中文:
定理 edges_subset_edgeSet
  条件: {u v : V}
-/
theorem edges_subset_edgeSet {u v : V} :
    forall (p : G.Walk u v) ⦃e : Sym2 V⦄, e in p.edges -> e in G.edgeSet
  | cons h' p', e, h => by
    cases h
    · exact h'
    next h' => exact edges_subset_edgeSet p' h'

/--
theorem `adj_of_mem_edges` / 定理 `adj_of_mem_edges`

English:
theorem adj_of_mem_edges
  given: {u v x y : V} (p : G.Walk u v) (h : s(x, y) in p.edges)
  statement: G.Adj x y
  proof: p.edges_subset_edgeSet h

@[simp]

中文:
定理 adj_of_mem_edges
  条件: {u v x y : V} (p : G.Walk u v) (h : s(x, y) in p.edges)
  结论: G.Adj x y
  证明: p.edges_subset_edgeSet h

@[simp]

Depends on / 依赖: edges_subset_edgeSet, p.edges_subset_edgeSet
-/
theorem adj_of_mem_edges {u v x y : V} (p : G.Walk u v) (h : s(x, y) in p.edges) : G.Adj x y :=
  p.edges_subset_edgeSet h

@[simp]
/--
theorem `darts_nil` / 定理 `darts_nil`

English:
theorem darts_nil
  given: {u : V}
  statement: (nil : G.Walk u u).darts = []
  proof: rfl

@[simp]

中文:
定理 darts_nil
  条件: {u : V}
  结论: (nil : G.Walk u u).darts = []
  证明: rfl

@[simp]
-/
theorem darts_nil {u : V} : (nil : G.Walk u u).darts = [] := rfl

@[simp]
/--
theorem `darts_cons` / 定理 `darts_cons`

English:
theorem darts_cons
  given: {u v w : V} (h : G.Adj u v) (p : G.Walk v w)
  proof: rfl

中文:
定理 darts_cons
  条件: {u v w : V} (h : G.Adj u v) (p : G.Walk v w)
  证明: rfl
-/
theorem darts_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (cons h p).darts = ⟨(u, v), h⟩ :: p.darts := rfl

/--
theorem `_root_.SimpleGraph.Adj.darts_toWalk` / 定理 `_root_.SimpleGraph.Adj.darts_toWalk`

English:
theorem _root_.SimpleGraph.Adj.darts_toWalk
  given: (h : G.Adj u v)
  statement: h.toWalk.darts = [⟨(u, v), h⟩]
  proof: rfl

中文:
定理 _root_.SimpleGraph.Adj.darts_toWalk
  条件: (h : G.Adj u v)
  结论: h.toWalk.darts = [⟨(u, v), h⟩]
  证明: rfl
-/
theorem _root_.SimpleGraph.Adj.darts_toWalk (h : G.Adj u v) : h.toWalk.darts = [⟨(u, v), h⟩] :=
  rfl

/--
theorem `cons_map_snd_darts` / 定理 `cons_map_snd_darts`

English:
theorem cons_map_snd_darts
  given: {u v : V} (p : G.Walk u v)
  statement: (u :: p.darts.map (·.snd)) = p.support
  proof: by
  induction p <;> simp [*]

中文:
定理 cons_map_snd_darts
  条件: {u v : V} (p : G.Walk u v)
  结论: (u :: p.darts.map (·.snd)) = p.support
  证明: by
  induction p <;> simp [*]
-/
theorem cons_map_snd_darts {u v : V} (p : G.Walk u v) : (u :: p.darts.map (·.snd)) = p.support := by
  induction p <;> simp [*]

/--
theorem `map_snd_darts` / 定理 `map_snd_darts`

English:
theorem map_snd_darts
  given: {u v : V} (p : G.Walk u v)
  statement: p.darts.map (·.snd) = p.support.tail
  proof: by
  simpa using congr_arg List.tail (cons_map_snd_darts p)

中文:
定理 map_snd_darts
  条件: {u v : V} (p : G.Walk u v)
  结论: p.darts.map (·.snd) = p.support.tail
  证明: by
  simpa using congr_arg List.tail (cons_map_snd_darts p)

Depends on / 依赖: List.tail, congr_arg, cons_map_snd_darts
-/
theorem map_snd_darts {u v : V} (p : G.Walk u v) : p.darts.map (·.snd) = p.support.tail := by
  simpa using congr_arg List.tail (cons_map_snd_darts p)

/--
theorem `map_fst_darts_append` / 定理 `map_fst_darts_append`

English:
theorem map_fst_darts_append
  given: {u v : V} (p : G.Walk u v)
  proof: by
  induction p <;> simp [*]

中文:
定理 map_fst_darts_append
  条件: {u v : V} (p : G.Walk u v)
  证明: by
  induction p <;> simp [*]
-/
theorem map_fst_darts_append {u v : V} (p : G.Walk u v) :
    p.darts.map (·.fst) ++ [v] = p.support := by
  induction p <;> simp [*]

/--
theorem `map_fst_darts` / 定理 `map_fst_darts`

English:
theorem map_fst_darts
  given: {u v : V} (p : G.Walk u v)
  statement: p.darts.map (·.fst) = p.support.dropLast
  proof: by
  simpa! using! congr_arg List.dropLast (map_fst_darts_append p)

@[simp]

中文:
定理 map_fst_darts
  条件: {u v : V} (p : G.Walk u v)
  结论: p.darts.map (·.fst) = p.support.dropLast
  证明: by
  simpa! using! congr_arg List.dropLast (map_fst_darts_append p)

@[simp]

Depends on / 依赖: List.dropLast, congr_arg, dropLast, map_fst_darts_append
-/
theorem map_fst_darts {u v : V} (p : G.Walk u v) : p.darts.map (·.fst) = p.support.dropLast := by
  simpa! using! congr_arg List.dropLast (map_fst_darts_append p)

@[simp]
/--
theorem `edges_nil` / 定理 `edges_nil`

English:
theorem edges_nil
  given: {u : V}
  statement: (nil : G.Walk u u).edges = []
  proof: rfl

@[simp]

中文:
定理 edges_nil
  条件: {u : V}
  结论: (nil : G.Walk u u).edges = []
  证明: rfl

@[simp]
-/
theorem edges_nil {u : V} : (nil : G.Walk u u).edges = [] := rfl

@[simp]
/--
theorem `edges_cons` / 定理 `edges_cons`

English:
theorem edges_cons
  given: {u v w : V} (h : G.Adj u v) (p : G.Walk v w)
  proof: rfl

中文:
定理 edges_cons
  条件: {u v w : V} (h : G.Adj u v) (p : G.Walk v w)
  证明: rfl
-/
theorem edges_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (cons h p).edges = s(u, v) :: p.edges := rfl

/--
theorem `_root_.SimpleGraph.Adj.edges_toWalk` / 定理 `_root_.SimpleGraph.Adj.edges_toWalk`

English:
theorem _root_.SimpleGraph.Adj.edges_toWalk
  given: (h : G.Adj u v)
  statement: h.toWalk.edges = [s(u, v)]
  proof: rfl

@[simp, grind =]

中文:
定理 _root_.SimpleGraph.Adj.edges_toWalk
  条件: (h : G.Adj u v)
  结论: h.toWalk.edges = [s(u, v)]
  证明: rfl

@[simp, grind =]
-/
theorem _root_.SimpleGraph.Adj.edges_toWalk (h : G.Adj u v) : h.toWalk.edges = [s(u, v)] :=
  rfl

@[simp, grind =]
/--
theorem `length_support` / 定理 `length_support`

English:
theorem length_support
  given: {u v : V} (p : G.Walk u v)
  statement: p.support.length = p.length + 1
  proof: by
  induction p <;> simp [*]

@[simp, grind =]

中文:
定理 length_support
  条件: {u v : V} (p : G.Walk u v)
  结论: p.support.length = p.length + 1
  证明: by
  induction p <;> simp [*]

@[simp, grind =]
-/
theorem length_support {u v : V} (p : G.Walk u v) : p.support.length = p.length + 1 := by
  induction p <;> simp [*]

@[simp, grind =]
/--
theorem `length_darts` / 定理 `length_darts`

English:
theorem length_darts
  given: {u v : V} (p : G.Walk u v)
  statement: p.darts.length = p.length
  proof: by
  induction p <;> simp [*]

@[simp, grind =]

中文:
定理 length_darts
  条件: {u v : V} (p : G.Walk u v)
  结论: p.darts.length = p.length
  证明: by
  induction p <;> simp [*]

@[simp, grind =]
-/
theorem length_darts {u v : V} (p : G.Walk u v) : p.darts.length = p.length := by
  induction p <;> simp [*]

@[simp, grind =]
/--
theorem `length_edges` / 定理 `length_edges`

English:
theorem length_edges
  given: {u v : V} (p : G.Walk u v)
  statement: p.edges.length = p.length
  proof: by simp [edges]

中文:
定理 length_edges
  条件: {u v : V} (p : G.Walk u v)
  结论: p.edges.length = p.length
  证明: by simp [edges]
-/
theorem length_edges {u v : V} (p : G.Walk u v) : p.edges.length = p.length := by simp [edges]

/--
theorem `getElem_edges_eq_edge_getElem_darts` / 定理 `getElem_edges_eq_edge_getElem_darts`

English:
theorem getElem_edges_eq_edge_getElem_darts
  given: {p : G.Walk u v} {i : Nat} (h : i < p.edges.length)
  proof: List.getElem_map ..

中文:
定理 getElem_edges_eq_edge_getElem_darts
  条件: {p : G.Walk u v} {i : 自然数} (h : i < p.edges.length)
  证明: List.getElem_map ..

Depends on / 依赖: List.getElem_map, getElem_map
-/
theorem getElem_edges_eq_edge_getElem_darts {p : G.Walk u v} {i : Nat} (h : i < p.edges.length) :
    p.edges[i] = (p.darts[i]'(by grind)).edge :=
  List.getElem_map ..

/--
theorem `edge_getElem_darts` / 定理 `edge_getElem_darts`

English:
theorem edge_getElem_darts
  given: {p : G.Walk u v} {i : Nat} (h : i < p.darts.length)
  proof: by
  rw [getElem_edges_eq_edge_getElem_darts]

@[simp]

中文:
定理 edge_getElem_darts
  条件: {p : G.Walk u v} {i : 自然数} (h : i < p.darts.length)
  证明: by
  rw [getElem_edges_eq_edge_getElem_darts]

@[simp]

Depends on / 依赖: getElem_edges_eq_edge_getElem_darts
-/
theorem edge_getElem_darts {p : G.Walk u v} {i : Nat} (h : i < p.darts.length) :
    p.darts[i].edge = p.edges[i]'(by grind) := by
  rw [getElem_edges_eq_edge_getElem_darts]

@[simp]
/--
theorem `fst_darts_getElem` / 定理 `fst_darts_getElem`

English:
theorem fst_darts_getElem
  given: {p : G.Walk u v} {i : Nat} (hi : i < p.darts.length)
  proof: by
  grind [map_fst_darts]

@[simp]

中文:
定理 fst_darts_getElem
  条件: {p : G.Walk u v} {i : 自然数} (hi : i < p.darts.length)
  证明: by
  grind [map_fst_darts]

@[simp]

Depends on / 依赖: map_fst_darts
-/
theorem fst_darts_getElem {p : G.Walk u v} {i : Nat} (hi : i < p.darts.length) :
    p.darts[i].fst = p.support.dropLast[i]'(by grind) := by
  grind [map_fst_darts]

@[simp]
/--
theorem `snd_darts_getElem` / 定理 `snd_darts_getElem`

English:
theorem snd_darts_getElem
  given: {p : G.Walk u v} {i : Nat} (hi : i < p.darts.length)
  proof: by
  grind [map_snd_darts]

@[simp]

中文:
定理 snd_darts_getElem
  条件: {p : G.Walk u v} {i : 自然数} (hi : i < p.darts.length)
  证明: by
  grind [map_snd_darts]

@[simp]

Depends on / 依赖: map_snd_darts
-/
theorem snd_darts_getElem {p : G.Walk u v} {i : Nat} (hi : i < p.darts.length) :
    p.darts[i].snd = p.support.tail[i]'(by grind) := by
  grind [map_snd_darts]

@[simp]
/--
lemma `support_getElem_zero` / 引理 `support_getElem_zero`

English:
lemma support_getElem_zero
  given: (p : G.Walk u v)
  statement: p.support[0] = u
  proof: by cases p <;> simp

@[simp]

中文:
引理 support_getElem_zero
  条件: (p : G.Walk u v)
  结论: p.support[0] = u
  证明: by cases p <;> simp

@[simp]
-/
lemma support_getElem_zero (p : G.Walk u v) : p.support[0] = u := by cases p <;> simp

@[simp]
/--
lemma `support_getElem_length` / 引理 `support_getElem_length`

English:
lemma support_getElem_length
  given: (p : G.Walk u v)
  statement: p.support[p.length] = v
  proof: by
  induction p <;> simp_all

中文:
引理 support_getElem_length
  条件: (p : G.Walk u v)
  结论: p.support[p.length] = v
  证明: by
  induction p <;> simp_all
-/
lemma support_getElem_length (p : G.Walk u v) : p.support[p.length] = v := by
  induction p <;> simp_all

/--
theorem `mem_darts_iff_infix_support` / 定理 `mem_darts_iff_infix_support`

English:
theorem mem_darts_iff_infix_support
  given: {u' v'} {p : G.Walk u v} (h : G.Adj u' v')
  proof: by
  refine .trans ⟨fun h => ?_, fun ⟨i, hi, h⟩ => ?_⟩ List.infix_iff_getElem?.symm
  · have ⟨i, hi, h⟩ := List.getElem_of_mem h
    exact ⟨i, by grind, fun j hj => by grind [fst_darts_getElem, snd_darts_getElem]⟩
  · have := h 0
    have := h 1
    convert! p.darts.getElem_mem (n := i) (by grind)
 

中文:
定理 mem_darts_iff_infix_support
  条件: {u' v'} {p : G.Walk u v} (h : G.Adj u' v')
  证明: by
  refine .trans ⟨fun h => ?_, fun ⟨i, hi, h⟩ => ?_⟩ List.infix_iff_getElem?.symm
  · have ⟨i, hi, h⟩ := List.getElem_of_mem h
    exact ⟨i, by grind, fun j hj => by grind [fst_darts_getElem, snd_darts_getElem]⟩
  · have := h 0
    have := h 1
    convert! p.darts.getElem_mem (n := i) (by grind)
 

Depends on / 依赖: List.getElem_of_mem, List.infix_iff_getElem, convert, fst_darts_getElem, getElem_mem, getElem_of_mem, infix_iff_getElem, p.darts.getElem_mem, snd_darts_getElem
-/
theorem mem_darts_iff_infix_support {u' v'} {p : G.Walk u v} (h : G.Adj u' v') :
    ⟨⟨u', v'⟩, h⟩ in p.darts ↔ [u', v'] <:+: p.support := by
  refine .trans ⟨fun h => ?_, fun ⟨i, hi, h⟩ => ?_⟩ List.infix_iff_getElem?.symm
  · have ⟨i, hi, h⟩ := List.getElem_of_mem h
    exact ⟨i, by grind, fun j hj => by grind [fst_darts_getElem, snd_darts_getElem]⟩
  · have := h 0
    have := h 1
    convert! p.darts.getElem_mem (n := i) (by grind)
      <;> grind [fst_darts_getElem, snd_darts_getElem]

/--
theorem `mem_darts_iff_fst_snd_infix_support` / 定理 `mem_darts_iff_fst_snd_infix_support`

English:
theorem mem_darts_iff_fst_snd_infix_support
  given: {p : G.Walk u v} {d : G.Dart}
  proof: mem_darts_iff_infix_support ..

中文:
定理 mem_darts_iff_fst_snd_infix_support
  条件: {p : G.Walk u v} {d : G.Dart}
  证明: mem_darts_iff_infix_support ..

Depends on / 依赖: mem_darts_iff_infix_support
-/
theorem mem_darts_iff_fst_snd_infix_support {p : G.Walk u v} {d : G.Dart} :
    d in p.darts ↔ [d.fst, d.snd] <:+: p.support :=
  mem_darts_iff_infix_support ..

/--
theorem `dart_fst_mem_support_of_mem_darts` / 定理 `dart_fst_mem_support_of_mem_darts`

English:
theorem dart_fst_mem_support_of_mem_darts
  given: {u v : V}

中文:
定理 dart_fst_mem_support_of_mem_darts
  条件: {u v : V}
-/
theorem dart_fst_mem_support_of_mem_darts {u v : V} :
    forall (p : G.Walk u v) {d : G.Dart}, d in p.darts -> d.fst in p.support
  | cons h p', d, hd => by
    simp only [support_cons, darts_cons, List.mem_cons] at hd ⊢
    rcases hd with rfl | hd
    · exact .inl rfl
    · exact .inr (dart_fst_mem_support_of_mem_darts _ hd)

/--
theorem `mem_support_iff_exists_mem_edges` / 定理 `mem_support_iff_exists_mem_edges`

English:
theorem mem_support_iff_exists_mem_edges
  given: {u v w : V} {p : G.Walk u v}
  proof: by
  induction p <;> aesop

中文:
定理 mem_support_iff_exists_mem_edges
  条件: {u v w : V} {p : G.Walk u v}
  证明: by
  induction p <;> aesop
-/
theorem mem_support_iff_exists_mem_edges {u v w : V} {p : G.Walk u v} :
    w in p.support ↔ w = v ∨ exists e in p.edges, w in e := by
  induction p <;> aesop

/--
theorem `darts_nodup_of_support_nodup` / 定理 `darts_nodup_of_support_nodup`

English:
theorem darts_nodup_of_support_nodup
  given: {u v : V} {p : G.Walk u v} (h : p.support.Nodup)
  proof: by
  induction p with
  | nil => simp
  | cons _ p' ih =>
    simp only [darts_cons, support_cons, List.nodup_cons] at h ⊢
    exact ⟨(h.1 <| dart_fst_mem_support_of_mem_darts p' ·), ih h.2⟩

中文:
定理 darts_nodup_of_support_nodup
  条件: {u v : V} {p : G.Walk u v} (h : p.support.Nodup)
  证明: by
  induction p with
  | nil => simp
  | cons _ p' ih =>
    simp only [darts_cons, support_cons, List.nodup_cons] at h ⊢
    exact ⟨(h.1 <| dart_fst_mem_support_of_mem_darts p' ·), ih h.2⟩

Depends on / 依赖: List.nodup_cons, dart_fst_mem_support_of_mem_darts, darts_cons, nodup_cons, support_cons
-/
theorem darts_nodup_of_support_nodup {u v : V} {p : G.Walk u v} (h : p.support.Nodup) :
    p.darts.Nodup := by
  induction p with
  | nil => simp
  | cons _ p' ih =>
    simp only [darts_cons, support_cons, List.nodup_cons] at h ⊢
    exact ⟨(h.1 <| dart_fst_mem_support_of_mem_darts p' ·), ih h.2⟩

/--
theorem `edges_eq_zipWith_support` / 定理 `edges_eq_zipWith_support`

English:
theorem edges_eq_zipWith_support
  given: {u v : V} {p : G.Walk u v}
  proof: by
  induction p with
  | nil => simp
  | cons _ p' ih => cases p' <;> simp [edges_cons, ih]

中文:
定理 edges_eq_zipWith_support
  条件: {u v : V} {p : G.Walk u v}
  证明: by
  induction p with
  | nil => simp
  | cons _ p' ih => cases p' <;> simp [edges_cons, ih]

Depends on / 依赖: edges_cons
-/
theorem edges_eq_zipWith_support {u v : V} {p : G.Walk u v} :
    p.edges = List.zipWith (s(·, ·)) p.support p.support.tail := by
  induction p with
  | nil => simp
  | cons _ p' ih => cases p' <;> simp [edges_cons, ih]

/--
theorem `edges_injective` / 定理 `edges_injective`

English:
theorem edges_injective
  given: {u v : V}
  statement: Function.Injective (Walk.edges : G.Walk u v -> List (Sym2 V))
  proof: by simpa [h₁, h₂.ne] using h
    rw [edges_injective h₃]

中文:
定理 edges_injective
  条件: {u v : V}
  结论: Function.Injective (Walk.edges : G.Walk u v -> List (Sym2 V))
  证明: by simpa [h₁, h₂.ne] using h
    rw [edges_injective h₃]

Depends on / 依赖: edges_injective
-/
theorem edges_injective {u v : V} : Function.Injective (Walk.edges : G.Walk u v -> List (Sym2 V))
  | .nil, .nil, _ => rfl
  | .nil, .cons _ _, h => by simp at h
  | .cons _ _, .nil, h => by simp at h
  | .cons' u v c h₁ w₁, .cons' _ v' _ h₂ w₂, h => by
    obtain ⟨rfl, h₃⟩ : v = v' ∧ w₁.edges = w₂.edges := by simpa [h₁, h₂.ne] using h
    rw [edges_injective h₃]

/--
theorem `darts_injective` / 定理 `darts_injective`

English:
theorem darts_injective
  given: {u v : V}
  statement: Function.Injective (Walk.darts : G.Walk u v -> List G.Dart)
  proof: edges_injective.of_comp

中文:
定理 darts_injective
  条件: {u v : V}
  结论: Function.Injective (Walk.darts : G.Walk u v -> List G.Dart)
  证明: edges_injective.of_comp

Depends on / 依赖: edges_injective, edges_injective.of_comp, of_comp
-/
theorem darts_injective {u v : V} : Function.Injective (Walk.darts : G.Walk u v -> List G.Dart) :=
  edges_injective.of_comp

/--
Definition of `edgeSet` / `edgeSet` 的定义

English:
definition edgeSet
  signature: {u v : V} (p : G.Walk u v)
  body: {e | e in p.edges}

@[simp]

中文:
定义 edgeSet
  签名: {u v : V} (p : G.Walk u v)
  定义体: {e | e in p.edges}

@[simp]

Depends on / 依赖: p.edges
-/
def edgeSet {u v : V} (p : G.Walk u v) : Set (Sym2 V) := {e | e in p.edges}

@[simp]
/--
lemma `mem_edgeSet` / 引理 `mem_edgeSet`

English:
lemma mem_edgeSet
  given: {u v : V} {p : G.Walk u v} {e : Sym2 V}
  statement: e in p.edgeSet ↔ e in p.edges
  proof: Iff.rfl

@[simp]

中文:
引理 mem_edgeSet
  条件: {u v : V} {p : G.Walk u v} {e : Sym2 V}
  结论: e in p.edgeSet ↔ e in p.edges
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
lemma mem_edgeSet {u v : V} {p : G.Walk u v} {e : Sym2 V} : e in p.edgeSet ↔ e in p.edges := Iff.rfl

@[simp]
/--
lemma `edgeSet_nil` / 引理 `edgeSet_nil`

English:
lemma edgeSet_nil
  given: (u : V)
  statement: (nil : G.Walk u u).edgeSet = ∅
  proof: by ext; simp

@[simp]

中文:
引理 edgeSet_nil
  条件: (u : V)
  结论: (nil : G.Walk u u).edgeSet = ∅
  证明: by ext; simp

@[simp]
-/
lemma edgeSet_nil (u : V) : (nil : G.Walk u u).edgeSet = ∅ := by ext; simp

@[simp]
/--
theorem `edgeSet_cons` / 定理 `edgeSet_cons`

English:
theorem edgeSet_cons
  given: {u v w : V} (h : G.Adj u v) (p : G.Walk v w)
  proof: by ext; simp

中文:
定理 edgeSet_cons
  条件: {u v w : V} (h : G.Adj u v) (p : G.Walk v w)
  证明: by ext; simp
-/
theorem edgeSet_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (cons h p).edgeSet = insert s(u, v) p.edgeSet := by ext; simp

/--
theorem `coe_edges_toFinset` / 定理 `coe_edges_toFinset`

English:
theorem coe_edges_toFinset
  given: [DecidableEq V] {u v : V} (p : G.Walk u v)
  proof: by
  simp [edgeSet]

中文:
定理 coe_edges_toFinset
  条件: [DecidableEq V] {u v : V} (p : G.Walk u v)
  证明: by
  simp [edgeSet]

Depends on / 依赖: edgeSet
-/
theorem coe_edges_toFinset [DecidableEq V] {u v : V} (p : G.Walk u v) :
    (p.edges.toFinset : Set (Sym2 V)) = p.edgeSet := by
  simp [edgeSet]

/--
Inductive type `Nil` / 归纳类型 `Nil`

English:
inductive Nil
  parameters: : {v w : V} -> G.Walk v w -> Prop
  constructors (1):
    - nil: {u : V} : Nil (nil : G.Walk u u)

中文:
归纳类型 Nil
  参数: : {v w : V} -> G.Walk v w -> 命题
  构造子 (1 个):
    - nil: {u : V} : Nil (nil : G.Walk u u)
-/
inductive Nil : {v w : V} -> G.Walk v w -> Prop
  | nil {u : V} : Nil (nil : G.Walk u u)

/--
lemma `nil_nil` / 引理 `nil_nil`

English:
lemma nil_nil
  statement: (nil : G.Walk u u).Nil
  proof: Nil.nil

中文:
引理 nil_nil
  结论: (nil : G.Walk u u).Nil
  证明: Nil.nil
-/
@[simp, grind .] lemma nil_nil : (nil : G.Walk u u).Nil := Nil.nil

/--
lemma `not_nil_cons` / 引理 `not_nil_cons`

English:
lemma not_nil_cons
  given: {h : G.Adj u v} {p : G.Walk v w}
  statement: ¬ (cons h p).Nil
  proof: nofun

中文:
引理 not_nil_cons
  条件: {h : G.Adj u v} {p : G.Walk v w}
  结论: ¬ (cons h p).Nil
  证明: nofun
-/
@[simp] lemma not_nil_cons {h : G.Adj u v} {p : G.Walk v w} : ¬ (cons h p).Nil := nofun

instance (p : G.Walk v w) : Decidable p.Nil :=
  match p with
  | nil => isTrue .nil
  | cons _ _ => isFalse nofun

@[grind .]
/--
lemma `Nil.eq` / 引理 `Nil.eq`

English:
lemma Nil.eq
  given: {p : G.Walk v w}
  statement: p.Nil -> v = w | .nil => rfl

中文:
引理 Nil.eq
  条件: {p : G.Walk v w}
  结论: p.Nil -> v = w | .nil => rfl
-/
protected lemma Nil.eq {p : G.Walk v w} : p.Nil -> v = w | .nil => rfl

/--
lemma `not_nil_of_ne` / 引理 `not_nil_of_ne`

English:
lemma not_nil_of_ne
  given: {p : G.Walk v w}
  statement: v != w -> ¬ p.Nil
  proof: mt Nil.eq

中文:
引理 not_nil_of_ne
  条件: {p : G.Walk v w}
  结论: v != w -> ¬ p.Nil
  证明: mt Nil.eq

Depends on / 依赖: Nil.eq
-/
lemma not_nil_of_ne {p : G.Walk v w} : v != w -> ¬ p.Nil := mt Nil.eq

/--
lemma `nil_iff_support_eq` / 引理 `nil_iff_support_eq`

English:
lemma nil_iff_support_eq
  given: {p : G.Walk v w}
  statement: p.Nil ↔ p.support = [v]
  proof: by
  cases p <;> simp

@[simp]

中文:
引理 nil_iff_support_eq
  条件: {p : G.Walk v w}
  结论: p.Nil ↔ p.support = [v]
  证明: by
  cases p <;> simp

@[simp]
-/
lemma nil_iff_support_eq {p : G.Walk v w} : p.Nil ↔ p.support = [v] := by
  cases p <;> simp

@[simp]
/--
lemma `darts_eq_nil` / 引理 `darts_eq_nil`

English:
lemma darts_eq_nil
  given: {p : G.Walk v w}
  statement: p.darts = [] ↔ p.Nil
  proof: by
  cases p <;> simp

@[simp]

中文:
引理 darts_eq_nil
  条件: {p : G.Walk v w}
  结论: p.darts = [] ↔ p.Nil
  证明: by
  cases p <;> simp

@[simp]
-/
lemma darts_eq_nil {p : G.Walk v w} : p.darts = [] ↔ p.Nil := by
  cases p <;> simp

@[simp]
/--
lemma `edges_eq_nil` / 引理 `edges_eq_nil`

English:
lemma edges_eq_nil
  given: {p : G.Walk v w}
  statement: p.edges = [] ↔ p.Nil
  proof: by
  cases p <;> simp

@[simp, grind .]

中文:
引理 edges_eq_nil
  条件: {p : G.Walk v w}
  结论: p.edges = [] ↔ p.Nil
  证明: by
  cases p <;> simp

@[simp, grind .]
-/
lemma edges_eq_nil {p : G.Walk v w} : p.edges = [] ↔ p.Nil := by
  cases p <;> simp

@[simp, grind .]
/--
theorem `length_eq_zero_iff` / 定理 `length_eq_zero_iff`

English:
theorem length_eq_zero_iff
  given: {p : G.Walk u v}
  statement: p.length = 0 ↔ p.Nil
  proof: by
  cases p <;> simp

alias ⟨_, Nil.length_eq_zero⟩ := length_eq_zero_iff

@[deprecated length_eq_zero_iff (since := "2026-05-11")]

中文:
定理 length_eq_zero_iff
  条件: {p : G.Walk u v}
  结论: p.length = 0 ↔ p.Nil
  证明: by
  cases p <;> simp

alias ⟨_, Nil.length_eq_zero⟩ := length_eq_zero_iff

@[deprecated length_eq_zero_iff (since := "2026-05-11")]
-/
theorem length_eq_zero_iff {p : G.Walk u v} : p.length = 0 ↔ p.Nil := by
  cases p <;> simp

alias ⟨_, Nil.length_eq_zero⟩ := length_eq_zero_iff

@[deprecated length_eq_zero_iff (since := "2026-05-11")]
/--
lemma `nil_iff_length_eq` / 引理 `nil_iff_length_eq`

English:
lemma nil_iff_length_eq
  given: {p : G.Walk v w}
  statement: p.Nil ↔ p.length = 0
  proof: length_eq_zero_iff.symm

中文:
引理 nil_iff_length_eq
  条件: {p : G.Walk v w}
  结论: p.Nil ↔ p.length = 0
  证明: length_eq_zero_iff.symm

Depends on / 依赖: length_eq_zero_iff, length_eq_zero_iff.symm
-/
lemma nil_iff_length_eq {p : G.Walk v w} : p.Nil ↔ p.length = 0 :=
  length_eq_zero_iff.symm

/--
lemma `not_nil_iff_lt_length` / 引理 `not_nil_iff_lt_length`

English:
lemma not_nil_iff_lt_length
  given: {p : G.Walk v w}
  statement: ¬ p.Nil ↔ 0 < p.length
  proof: by
  cases p <;> simp

中文:
引理 not_nil_iff_lt_length
  条件: {p : G.Walk v w}
  结论: ¬ p.Nil ↔ 0 < p.length
  证明: by
  cases p <;> simp
-/
lemma not_nil_iff_lt_length {p : G.Walk v w} : ¬ p.Nil ↔ 0 < p.length := by
  cases p <;> simp

/--
lemma `not_nil_iff` / 引理 `not_nil_iff`

English:
lemma not_nil_iff
  given: {p : G.Walk v w}
  proof: by
  cases p <;> simp [*]

中文:
引理 not_nil_iff
  条件: {p : G.Walk v w}
  证明: by
  cases p <;> simp [*]
-/
lemma not_nil_iff {p : G.Walk v w} :
    ¬ p.Nil ↔ exists (u : V) (h : G.Adj v u) (q : G.Walk u w), p = cons h q := by
  cases p <;> simp [*]

/-- A walk with its endpoints defeq is `Nil` if and only if it is equal to `nil`. -/
@[simp]
/--
theorem `eq_nil_iff_nil` / 定理 `eq_nil_iff_nil`

English:
theorem eq_nil_iff_nil
  given: {p : G.Walk v v}
  statement: p = nil ↔ p.Nil
  proof: by
  cases p <;> simp

alias ⟨_, Nil.eq_nil⟩ := eq_nil_iff_nil

@[deprecated eq_nil_iff_nil (since := "2026-05-11")]

中文:
定理 eq_nil_iff_nil
  条件: {p : G.Walk v v}
  结论: p = nil ↔ p.Nil
  证明: by
  cases p <;> simp

alias ⟨_, Nil.eq_nil⟩ := eq_nil_iff_nil

@[deprecated eq_nil_iff_nil (since := "2026-05-11")]
-/
theorem eq_nil_iff_nil {p : G.Walk v v} : p = nil ↔ p.Nil := by
  cases p <;> simp

alias ⟨_, Nil.eq_nil⟩ := eq_nil_iff_nil

@[deprecated eq_nil_iff_nil (since := "2026-05-11")]
/--
lemma `nil_iff_eq_nil` / 引理 `nil_iff_eq_nil`

English:
lemma nil_iff_eq_nil
  statement: forall {p : G.Walk v v}, p.Nil ↔ p = nil
  proof: eq_nil_iff_nil.symm

中文:
引理 nil_iff_eq_nil
  结论: 对任意 {p : G.Walk v v}, p.Nil ↔ p = nil
  证明: eq_nil_iff_nil.symm

Depends on / 依赖: eq_nil_iff_nil, eq_nil_iff_nil.symm
-/
lemma nil_iff_eq_nil : forall {p : G.Walk v v}, p.Nil ↔ p = nil :=
  eq_nil_iff_nil.symm

/--
lemma `nil_of_subsingleton` / 引理 `nil_of_subsingleton`

English:
lemma nil_of_subsingleton
  given: [Subsingleton V] (p : G.Walk v w)
  statement: p.Nil
  proof: match p with
  | nil => Nil.nil
.elim | cons h w => Unique.eq_default G ▸ h

@[simp]

中文:
引理 nil_of_subsingleton
  条件: [Subsingleton V] (p : G.Walk v w)
  结论: p.Nil
  证明: match p with
  | nil => Nil.nil
.elim | cons h w => Unique.eq_default G ▸ h

@[simp]

Depends on / 依赖: Nil.nil, Unique, Unique.eq_default, eq_default
-/
lemma nil_of_subsingleton [Subsingleton V] (p : G.Walk v w) : p.Nil :=
  match p with
  | nil => Nil.nil
.elim | cons h w => Unique.eq_default G ▸ h

@[simp]
/--
theorem `exists_nil_iff` / 定理 `exists_nil_iff`

English:
theorem exists_nil_iff
  given: {u v : V}
  statement: (exists p : G.Walk u v, p.Nil) ↔ u = v
  proof: ⟨fun ⟨_, h⟩ => h.eq, (· ▸ ⟨nil, .nil⟩)⟩

中文:
定理 exists_nil_iff
  条件: {u v : V}
  结论: (存在 p : G.Walk u v, p.Nil) ↔ u = v
  证明: ⟨fun ⟨_, h⟩ => h.eq, (· ▸ ⟨nil, .nil⟩)⟩

Depends on / 依赖: h.eq
-/
theorem exists_nil_iff {u v : V} : (exists p : G.Walk u v, p.Nil) ↔ u = v :=
  ⟨fun ⟨_, h⟩ => h.eq, (· ▸ ⟨nil, .nil⟩)⟩

/-- The recursion principle for nonempty walks -/
@[elab_as_elim]
/--
Definition of `notNilRec` / `notNilRec` 的定义

English:
definition notNilRec
  signature: {motive : {u w : V} -> (p : G.Walk u w) -> (h : ¬ p.Nil) -> Sort*}
  body: match p with
  | nil => fun hp => absurd .nil hp
  | .cons h q => fun _ => cons h q

@[simp]

中文:
定义 notNilRec
  签名: {motive : {u w : V} -> (p : G.Walk u w) -> (h : ¬ p.Nil) -> Sort*}
  定义体: match p with
  | nil => fun hp => absurd .nil hp
  | .cons h q => fun _ => cons h q

@[simp]

Depends on / 依赖: absurd
-/
def notNilRec {motive : {u w : V} -> (p : G.Walk u w) -> (h : ¬ p.Nil) -> Sort*}
    (cons : {u v w : V} -> (h : G.Adj u v) -> (q : G.Walk v w) -> motive (cons h q) not_nil_cons)
    (p : G.Walk u w) : (hp : ¬ p.Nil) -> motive p hp :=
  match p with
  | nil => fun hp => absurd .nil hp
  | .cons h q => fun _ => cons h q

@[simp]
/--
lemma `notNilRec_cons` / 引理 `notNilRec_cons`

English:
lemma notNilRec_cons
  statement: {motive : {u w : V} -> (p : G.Walk u w) -> ¬ p.Nil -> Sort*}
  proof: by rfl

中文:
引理 notNilRec_cons
  结论: {motive : {u w : V} -> (p : G.Walk u w) -> ¬ p.Nil -> Sort*}
  证明: by rfl
-/
lemma notNilRec_cons {motive : {u w : V} -> (p : G.Walk u w) -> ¬ p.Nil -> Sort*}
    (cons : {u v w : V} -> (h : G.Adj u v) -> (q : G.Walk v w) ->
    motive (q.cons h) Walk.not_nil_cons) (h' : G.Adj u v) (q' : G.Walk v w) :
    @Walk.notNilRec _ _ _ _ _ cons _ _ = cons h' q' := by rfl

/--
theorem `end_mem_tail_support` / 定理 `end_mem_tail_support`

English:
theorem end_mem_tail_support
  given: {u v : V} {p : G.Walk u v} (h : ¬ p.Nil)
  statement: v in p.support.tail
  proof: p.notNilRec (by simp) h

中文:
定理 end_mem_tail_support
  条件: {u v : V} {p : G.Walk u v} (h : ¬ p.Nil)
  结论: v in p.support.tail
  证明: p.notNilRec (by simp) h

Depends on / 依赖: notNilRec, p.notNilRec
-/
theorem end_mem_tail_support {u v : V} {p : G.Walk u v} (h : ¬ p.Nil) : v in p.support.tail :=
  p.notNilRec (by simp) h

/--
theorem `mem_support_iff_exists_mem_edges_of_not_nil` / 定理 `mem_support_iff_exists_mem_edges_of_not_nil`

English:
theorem mem_support_iff_exists_mem_edges_of_not_nil
  given: {u v w : V} {p : G.Walk u v} (hnil : ¬p.Nil)
  proof: by
  induction p with
  | nil => simp at hnil
  | cons h p ih => cases p <;> aesop

中文:
定理 mem_support_iff_exists_mem_edges_of_not_nil
  条件: {u v w : V} {p : G.Walk u v} (hnil : ¬p.Nil)
  证明: by
  induction p with
  | nil => simp at hnil
  | cons h p ih => cases p <;> aesop
-/
theorem mem_support_iff_exists_mem_edges_of_not_nil {u v w : V} {p : G.Walk u v} (hnil : ¬p.Nil) :
    w in p.support ↔ exists e in p.edges, w in e := by
  induction p with
  | nil => simp at hnil
  | cons h p ih => cases p <;> aesop

/--
theorem `exists_boundary_dart` / 定理 `exists_boundary_dart`

English:
theorem exists_boundary_dart
  given: {u v : V} (p : G.Walk u v) (S : Set V) (uS : u in S) (vS : v ∉ S)
  proof: by
  induction p with
  | nil => cases vS uS
  | cons a p' ih =>
    rename_i x _
    by_cases h : x in S
    · obtain ⟨d, hd, hcd⟩ := ih h vS
      exact ⟨d, List.Mem.tail _ hd, hcd⟩
    · exact ⟨⟨_, a⟩, List.Mem.head _, uS, h⟩

中文:
定理 exists_boundary_dart
  条件: {u v : V} (p : G.Walk u v) (S : Set V) (uS : u in S) (vS : v ∉ S)
  证明: by
  induction p with
  | nil => cases vS uS
  | cons a p' ih =>
    rename_i x _
    by_cases h : x in S
    · obtain ⟨d, hd, hcd⟩ := ih h vS
      exact ⟨d, List.Mem.tail _ hd, hcd⟩
    · exact ⟨⟨_, a⟩, List.Mem.head _, uS, h⟩

Depends on / 依赖: List.Mem.head, List.Mem.tail, rename_i
-/
theorem exists_boundary_dart {u v : V} (p : G.Walk u v) (S : Set V) (uS : u in S) (vS : v ∉ S) :
    exists d : G.Dart, d in p.darts ∧ d.fst in S ∧ d.snd ∉ S := by
  induction p with
  | nil => cases vS uS
  | cons a p' ih =>
    rename_i x _
    by_cases h : x in S
    · obtain ⟨d, hd, hcd⟩ := ih h vS
      exact ⟨d, List.Mem.tail _ hd, hcd⟩
    · exact ⟨⟨_, a⟩, List.Mem.head _, uS, h⟩

/--
Definition of `ofSupport` / `ofSupport` 的定义

English:
definition ofSupport
  signature: (l : List V) (hne : l != []) (hchain : l.IsChain G.Adj)
  body: match l with
  | [_] => .nil
| _ :: v :: l => .cons hchain.rel .ofSupport (v :: l) (l.cons_ne_nil v) hchain.of_cons

中文:
定义 ofSupport
  签名: (l : List V) (hne : l != []) (hchain : l.IsChain G.Adj)
  定义体: match l with
  | [_] => .nil
| _ :: v :: l => .cons hchain.rel .ofSupport (v :: l) (l.cons_ne_nil v) hchain.of_cons

Depends on / 依赖: cons_ne_nil, hchain, hchain.of_cons, hchain.rel, l.cons_ne_nil, ofSupport, of_cons
-/
def ofSupport (l : List V) (hne : l != []) (hchain : l.IsChain G.Adj) :
    G.Walk (l.head hne) (l.getLast hne) :=
  match l with
  | [_] => .nil
| _ :: v :: l => .cons hchain.rel .ofSupport (v :: l) (l.cons_ne_nil v) hchain.of_cons

variable (G v) in
@[simp]
/--
theorem `ofSupport_singleton` / 定理 `ofSupport_singleton`

English:
theorem ofSupport_singleton
  proof: rfl

@[simp]

中文:
定理 ofSupport_singleton
  证明: rfl

@[simp]
-/
theorem ofSupport_singleton :
    ofSupport [v] ([].cons_ne_nil v) (.singleton v) = .nil (G := G) (u := v) :=
  rfl

@[simp]
/--
theorem `ofSupport_cons_cons` / 定理 `ofSupport_cons_cons`

English:
theorem ofSupport_cons_cons
  given: {l : List V} (hchain : u :: v :: l |>.IsChain G.Adj)
  proof: rfl

中文:
定理 ofSupport_cons_cons
  条件: {l : List V} (hchain : u :: v :: l |>.IsChain G.Adj)
  证明: rfl
-/
theorem ofSupport_cons_cons {l : List V} (hchain : u :: v :: l |>.IsChain G.Adj) :
    ofSupport (u :: v :: l) ((v :: l).cons_ne_nil u) hchain =
      .cons hchain.rel (.ofSupport (v :: l) (l.cons_ne_nil v) hchain.of_cons) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `support_ofSupport` / 定理 `support_ofSupport`

English:
theorem support_ofSupport
  given: {l : List V} (hne : l != []) (hchain : l.IsChain G.Adj)
  proof: by
  match l with
  | [_] => rfl
  | _ :: v :: l =>
    simpa using support_ofSupport (l.cons_ne_nil v) hchain.of_cons

@[simp, grind =]

中文:
定理 support_ofSupport
  条件: {l : List V} (hne : l != []) (hchain : l.IsChain G.Adj)
  证明: by
  match l with
  | [_] => rfl
  | _ :: v :: l =>
    simpa using support_ofSupport (l.cons_ne_nil v) hchain.of_cons

@[simp, grind =]

Depends on / 依赖: cons_ne_nil, hchain, hchain.of_cons, l.cons_ne_nil, of_cons, support_ofSupport
-/
theorem support_ofSupport {l : List V} (hne : l != []) (hchain : l.IsChain G.Adj) :
    (ofSupport l hne hchain).support = l := by
  match l with
  | [_] => rfl
  | _ :: v :: l =>
    simpa using support_ofSupport (l.cons_ne_nil v) hchain.of_cons

@[simp, grind =]
/--
theorem `length_ofSupport` / 定理 `length_ofSupport`

English:
theorem length_ofSupport
  given: {l : List V} (hne : l != []) (hchain : l.IsChain G.Adj)
  proof: by
  grind [support_ofSupport]

中文:
定理 length_ofSupport
  条件: {l : List V} (hne : l != []) (hchain : l.IsChain G.Adj)
  证明: by
  grind [support_ofSupport]

Depends on / 依赖: support_ofSupport
-/
theorem length_ofSupport {l : List V} (hne : l != []) (hchain : l.IsChain G.Adj) :
    (ofSupport l hne hchain).length = l.length - 1 := by
  grind [support_ofSupport]

/--
Definition of `ofDarts` / `ofDarts` 的定义

English:
definition ofDarts
  signature: (l : List G.Dart) (hne : l != []) (hchain : l.IsChain G.DartAdj)
  body: match l with
  | [d] => .cons d.adj .nil
  | d₁ :: d₂ :: l =>
.cons (hchain.rel ▸ d₁.adj) ofDarts (d₂ :: l) (l.cons_ne_nil d₂) hchain.of_cons

@[simp]

中文:
定义 ofDarts
  签名: (l : List G.Dart) (hne : l != []) (hchain : l.IsChain G.DartAdj)
  定义体: match l with
  | [d] => .cons d.adj .nil
  | d₁ :: d₂ :: l =>
.cons (hchain.rel ▸ d₁.adj) ofDarts (d₂ :: l) (l.cons_ne_nil d₂) hchain.of_cons

@[simp]

Depends on / 依赖: cons_ne_nil, d.adj, hchain, hchain.of_cons, hchain.rel, l.cons_ne_nil, ofDarts, of_cons
-/
def ofDarts (l : List G.Dart) (hne : l != []) (hchain : l.IsChain G.DartAdj) :
    G.Walk (l.head hne).fst (l.getLast hne).snd :=
  match l with
  | [d] => .cons d.adj .nil
  | d₁ :: d₂ :: l =>
.cons (hchain.rel ▸ d₁.adj) ofDarts (d₂ :: l) (l.cons_ne_nil d₂) hchain.of_cons

@[simp]
/--
theorem `ofDarts_singleton` / 定理 `ofDarts_singleton`

English:
theorem ofDarts_singleton
  given: (d : G.Dart)
  statement: ofDarts [d] (by simp) (by simp) = .cons d.adj .nil
  proof: rfl

中文:
定理 ofDarts_singleton
  条件: (d : G.Dart)
  结论: ofDarts [d] (by simp) (by simp) = .cons d.adj .nil
  证明: rfl
-/
theorem ofDarts_singleton (d : G.Dart) : ofDarts [d] (by simp) (by simp) = .cons d.adj .nil :=
  rfl

/--
theorem `ofDarts_singleton'` / 定理 `ofDarts_singleton'`

English:
theorem ofDarts_singleton'
  given: (d : G.Dart)
  statement: ofDarts [d] (by simp) (by simp) = d.adj.toWalk
  proof: rfl

@[simp]

中文:
定理 ofDarts_singleton'
  条件: (d : G.Dart)
  结论: ofDarts [d] (by simp) (by simp) = d.adj.toWalk
  证明: rfl

@[simp]
-/
theorem ofDarts_singleton' (d : G.Dart) : ofDarts [d] (by simp) (by simp) = d.adj.toWalk :=
  rfl

@[simp]
/--
theorem `ofDarts_cons_cons` / 定理 `ofDarts_cons_cons`

English:
theorem ofDarts_cons_cons
  statement: {d₁ d₂ : G.Dart} {l : List G.Dart}
  proof: rfl

中文:
定理 ofDarts_cons_cons
  结论: {d₁ d₂ : G.Dart} {l : List G.Dart}
  证明: rfl
-/
theorem ofDarts_cons_cons {d₁ d₂ : G.Dart} {l : List G.Dart}
    (hchain : d₁ :: d₂ :: l |>.IsChain G.DartAdj) :
    ofDarts (d₁ :: d₂ :: l) ((d₂ :: l).cons_ne_nil d₁) hchain =
      .cons (hchain.rel ▸ d₁.adj) (ofDarts (d₂ :: l) (l.cons_ne_nil d₂) hchain.of_cons) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `darts_ofDarts` / 定理 `darts_ofDarts`

English:
theorem darts_ofDarts
  given: {l : List G.Dart} (hne : l != []) (hchain : l.IsChain G.DartAdj)
  proof: by
  match l with
  | [_] => rfl
  | d₁ :: d₂ :: l =>
    simpa [hchain.rel.symm] using darts_ofDarts (l.cons_ne_nil d₂) hchain.of_cons

@[simp]

中文:
定理 darts_ofDarts
  条件: {l : List G.Dart} (hne : l != []) (hchain : l.IsChain G.DartAdj)
  证明: by
  match l with
  | [_] => rfl
  | d₁ :: d₂ :: l =>
    simpa [hchain.rel.symm] using darts_ofDarts (l.cons_ne_nil d₂) hchain.of_cons

@[simp]

Depends on / 依赖: cons_ne_nil, darts_ofDarts, hchain, hchain.of_cons, hchain.rel.symm, l.cons_ne_nil, of_cons
-/
theorem darts_ofDarts {l : List G.Dart} (hne : l != []) (hchain : l.IsChain G.DartAdj) :
    (ofDarts l hne hchain).darts = l := by
  match l with
  | [_] => rfl
  | d₁ :: d₂ :: l =>
    simpa [hchain.rel.symm] using darts_ofDarts (l.cons_ne_nil d₂) hchain.of_cons

@[simp]
/--
theorem `edges_ofDarts` / 定理 `edges_ofDarts`

English:
theorem edges_ofDarts
  given: {l : List G.Dart} (hne : l != []) (hchain : l.IsChain G.DartAdj)
  proof: by
  simp [edges]

@[simp, grind =]

中文:
定理 edges_ofDarts
  条件: {l : List G.Dart} (hne : l != []) (hchain : l.IsChain G.DartAdj)
  证明: by
  simp [edges]

@[simp, grind =]
-/
theorem edges_ofDarts {l : List G.Dart} (hne : l != []) (hchain : l.IsChain G.DartAdj) :
    (ofDarts l hne hchain).edges = l.map Dart.edge := by
  simp [edges]

@[simp, grind =]
/--
theorem `length_ofDarts` / 定理 `length_ofDarts`

English:
theorem length_ofDarts
  given: {l : List G.Dart} (hne : l != []) (hchain : l.IsChain G.DartAdj)
  proof: by
  grind [darts_ofDarts]

中文:
定理 length_ofDarts
  条件: {l : List G.Dart} (hne : l != []) (hchain : l.IsChain G.DartAdj)
  证明: by
  grind [darts_ofDarts]

Depends on / 依赖: darts_ofDarts
-/
theorem length_ofDarts {l : List G.Dart} (hne : l != []) (hchain : l.IsChain G.DartAdj) :
    (ofDarts l hne hchain).length = l.length := by
  grind [darts_ofDarts]

end Walk

end SimpleGraph
