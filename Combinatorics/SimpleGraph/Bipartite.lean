/-
Copyright (c) 2025 Mitchell Horner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Horner
-/
module

public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Bipartite graphs

This file proves results about bipartite simple graphs, including several double-counting arguments.

## Main definitions

* `SimpleGraph.IsBipartiteWith G s t` is the condition that a simple graph `G` is bipartite in sets
  `s`, `t`, that is, `s` and `t` are disjoint and vertices `v`, `w` being adjacent in `G` implies
  that `v ∈ s` and `w ∈ t`, or `v ∈ t` and `w ∈ s`.

  Note that in this implementation, if `G.IsBipartiteWith s t`, `s ∪ t` need not cover the vertices
  of `G`, instead `s ∪ t` is only required to cover the *support* of `G`, that is, the vertices
  that form edges in `G`. This definition is equivalent to the expected definition. If `s` and `t`
  do not cover all the vertices, one recovers a covering of all the vertices by unioning the
  missing vertices `(s ∪ t)ᶜ` to either `s` or `t`.

* `SimpleGraph.IsBipartite`: Predicate for a simple graph to be bipartite.
  `G.IsBipartite` is defined as an abbreviation for `G.Colorable 2`.

* `SimpleGraph.isBipartite_iff_exists_isBipartiteWith` is the proof that `G.IsBipartite` iff
  `G.IsBipartiteWith s t`.

* `SimpleGraph.isBipartiteWith_sum_degrees_eq` is the proof that if `G.IsBipartiteWith s t`, then
  the sum of the degrees of the vertices in `s` is equal to the sum of the degrees of the vertices
  in `t`.

* `SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges` is the proof that if
  `G.IsBipartiteWith s t`, then sum of the degrees of the vertices in `s` is equal to the number of
  edges in `G`.

  See `SimpleGraph.sum_degrees_eq_twice_card_edges` for the general version, and
  `SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges'` for the version from the "right".

* `SimpleGraph.completeBipartiteGraph_isContained_iff` is the proof that simple graphs contain a
  copy of a `completeBipartiteGraph α β` iff there exists a "left" subset of `card α` vertices and
  a "right" subset of `card β` vertices such that every vertex in the "left" subset is adjacent to
  every vertex in the "right" subset.

* `SimpleGraph.between`; the simple graph `G.between s t` is the subgraph of `G` containing edges
  that connect a vertex in the set `s` to a vertex in the set `t`.

* `SimpleGraph.bipartiteDoubleCover`; the simple graph `G.bipartiteDoubleCover` has two vertices
  `inl v` and `inr v` for each vertex `v` in `G` such that `inl v` (`inr v`) is adjacent to `inr w`
  (`inl w`) iff `v` is adjacent to `w` in `G`.

## Implementation notes

For the formulation of double-counting arguments where a bipartite graph is considered as a
relation `r : α → β → Prop`, see `Mathlib/Combinatorics/Enumerative/DoubleCounting.lean`.

## TODO

* Prove that `G.IsBipartite` iff `G` does not contain an odd cycle.
  I.e., `G.IsBipartite ↔ ∀ n, (cycleGraph (2*n+1)).Free G`.
-/

@[expose] public section


open Finset Fintype

namespace SimpleGraph

variable {V : Type*} {v w : V} {G : SimpleGraph V} {s t : Set V}

section IsBipartiteWith

/-- `G` is bipartite in sets `s` and `t` iff `s` and `t` are disjoint and if vertices `v` and `w`
are adjacent in `G` then `v ∈ s` and `w ∈ t`, or `v ∈ t` and `w ∈ s`. -/
/-
**SimpleGraph.IsBipartiteWith** 是 Mathlib 中的一个归纳类型，位于命名空间 `SimpleGraph`。
形式化陈述：{V : Type u_1} → SimpleGraph V → Set V → Set V → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`G` is bipartite in sets `s` and `t` iff `s` and `t` are disjoint and if vertice
s `v` and `w`
are adjacent in `G` then `v ∈ s` and `w ∈ t`, or `v ∈ t` and `w ∈ s`.
-/
structure IsBipartiteWith (G : SimpleGraph V) (s t : Set V) : Prop where
  disjoint : Disjoint s t
  mem_of_adj ⦃v w : V⦄ : G.Adj v w → v ∈ s ∧ w ∈ t ∨ v ∈ t ∧ w ∈ s
/-
**SimpleGraph.IsBipartiteWith.symm** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsBipa
rtiteWith`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {s t : Set V}, G.IsBipartiteWith s t 
→ G.IsBipartiteWith t s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `SimpleGraph.IsBipartiteWith.disjoint`：∀ {V : Type u_1} {G : SimpleGraph 
V} {s t : Set V}, G.IsBipartiteWith s t → Disjoint s t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `SimpleGraph.IsBipartiteWith.mem_of_adj`：∀ {V : Type u_1} {G : SimpleGrap
h V} {s t : Set V},   G.IsBipartiteWith s t → ∀ ⦃v w : V⦄, G.Adj v w → v ∈ s ∧ w
 ∈ t ∨ v ∈ t ∧ w ∈ s
· 使用定理 `SimpleGraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Ad
j u v → G.Adj v u
-/
theorem IsBipartiteWith.symm (h : G.IsBipartiteWith s t) : G.IsBipartiteWith t s where
  disjoint := h.disjoint.symm
  mem_of_adj v w hadj := by
    rw [@and_comm (v ∈ t) (w ∈ s), @and_comm (v ∈ s) (w ∈ t)]
    exact h.mem_of_adj hadj.symm
/-
**SimpleGraph.isBipartiteWith_comm** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：isBipartiteWith_comm : G.IsBipartiteWith s t ↔ G.IsBipartiteWith t s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsBipartiteWith.symm`：∀ {V : Type u_1} {G : SimpleGraph V} {
s t : Set V}, G.IsBipartiteWith s t → G.IsBipartiteWith t s
-/
theorem isBipartiteWith_comm : G.IsBipartiteWith s t ↔ G.IsBipartiteWith t s :=
  ⟨IsBipartiteWith.symm, IsBipartiteWith.symm⟩

/-- If `G.IsBipartiteWith s t` and `v ∈ s`, then if `v` is adjacent to `w` in `G` then `w ∈ t`. -/
/-
**SimpleGraph.IsBipartiteWith.mem_of_mem_adj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGr
aph.IsBipartiteWith`。
形式化陈述：∀ {V : Type u_1} {v w : V} {G : SimpleGraph V} {s t : Set V}, G.IsBipartit
eWith s t → v ∈ s → G.Adj v w → w ∈ t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `SimpleGraph.IsBipartiteWith.disjoint`：∀ {V : Type u_1} {G : SimpleGraph 
V} {s t : Set V}, G.IsBipartiteWith s t → Disjoint s t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `SimpleGraph.IsBipartiteWith.mem_of_adj`：∀ {V : Type u_1} {G : SimpleGrap
h V} {s t : Set V},   G.IsBipartiteWith s t → ∀ ⦃v w : V⦄, G.Adj v w → v ∈ s ∧ w
 ∈ t ∨ v ∈ t ∧ w ∈ s

--- 原说明 ---
If `G.IsBipartiteWith s t` and `v ∈ s`, then if `v` is adjacent to `w` in `G` th
en `w ∈ t`.
-/
theorem IsBipartiteWith.mem_of_mem_adj
    (h : G.IsBipartiteWith s t) (hv : v ∈ s) (hadj : G.Adj v w) : w ∈ t := by
  apply h.mem_of_adj at hadj
  have nhv : v ∉ t := Set.disjoint_left.mp h.disjoint hv
  simpa [hv, nhv] using hadj

/-- If `G.IsBipartiteWith s t` and `v ∈ s`, then the neighbor set of `v` is the set of vertices in
`t` adjacent to `v` in `G`. -/
/-
**SimpleGraph.isBipartiteWith_neighborSet** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph
`。
形式化陈述：isBipartiteWith_neighborSet (h : G.IsBipartiteWith s t) (hv : v in s) : G.
neighborSet v = { w in t | G.Adj v w }
参数：h : G.IsBipartiteWith s t；hv : v in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.mem_neighborSet`：mem_neighborSet (v w : V) : w in G.neighbor
Set v ↔ G.Adj v w
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `iff_and_self`：∀ {p q : Prop}, (p ↔ q ∧ p) ↔ p → q
· 使用定理 `SimpleGraph.IsBipartiteWith.mem_of_mem_adj`：∀ {V : Type u_1} {v w : V} {
G : SimpleGraph V} {s t : Set V}, G.IsBipartiteWith s t → v ∈ s → G.Adj v w → w 
∈ t

--- 原说明 ---
If `G.IsBipartiteWith s t` and `v ∈ s`, then the neighbor set of `v` is the set 
of vertices in
`t` adjacent to `v` in `G`.
-/
theorem isBipartiteWith_neighborSet (h : G.IsBipartiteWith s t) (hv : v ∈ s) :
    G.neighborSet v = { w ∈ t | G.Adj v w } := by
  ext w
  rw [mem_neighborSet, Set.mem_ofPred_eq, iff_and_self]
  exact h.mem_of_mem_adj hv

/-- If `G.IsBipartiteWith s t` and `v ∈ s`, then the neighbor set of `v` is a subset of `t`. -/
/-
**SimpleGraph.isBipartiteWith_neighborSet_subset** 是 Mathlib 中的一个定理，位于命名空间 `Simp
leGraph`。
形式化陈述：isBipartiteWith_neighborSet_subset (h : G.IsBipartiteWith s t) (hv : v in 
s) : G.neighborSet v subseteq t
参数：h : G.IsBipartiteWith s t；hv : v in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.isBipartiteWith_neighborSet`：isBipartiteWith_neighborSet (h 
: G.IsBipartiteWith s t) (hv : v in s) : G.neighborSet v = { w in t | G.Adj v w 
}
· 使用定理 `Set.sep_subset`：sep_subset (s : Set α) (p : α -> Prop) : { x in s | p x 
} subseteq s

--- 原说明 ---
If `G.IsBipartiteWith s t` and `v ∈ s`, then the neighbor set of `v` is a subset
 of `t`.
-/
theorem isBipartiteWith_neighborSet_subset (h : G.IsBipartiteWith s t) (hv : v ∈ s) :
    G.neighborSet v ⊆ t := by
  rw [isBipartiteWith_neighborSet h hv]
  exact Set.sep_subset t (G.Adj v ·)

/-- If `G.IsBipartiteWith s t` and `v ∈ s`, then the neighbor set of `v` is disjoint to `s`. -/
/-
**SimpleGraph.isBipartiteWith_neighborSet_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Si
mpleGraph`。
形式化陈述：isBipartiteWith_neighborSet_disjoint (h : G.IsBipartiteWith s t) (hv : v i
n s) : Disjoint (G.neighborSet v) s
参数：h : G.IsBipartiteWith s t；hv : v in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.disjoint_of_subset_left`：disjoint_of_subset_left (h : s subseteq u) 
(d : Disjoint u t) : Disjoint s t
· 使用定理 `SimpleGraph.isBipartiteWith_neighborSet_subset`：isBipartiteWith_neighbor
Set_subset (h : G.IsBipartiteWith s t) (hv : v in s) : G.neighborSet v subseteq 
t
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `SimpleGraph.IsBipartiteWith.disjoint`：∀ {V : Type u_1} {G : SimpleGraph 
V} {s t : Set V}, G.IsBipartiteWith s t → Disjoint s t

--- 原说明 ---
If `G.IsBipartiteWith s t` and `v ∈ s`, then the neighbor set of `v` is disjoint
 to `s`.
-/
theorem isBipartiteWith_neighborSet_disjoint (h : G.IsBipartiteWith s t) (hv : v ∈ s) :
    Disjoint (G.neighborSet v) s :=
  Set.disjoint_of_subset_left (isBipartiteWith_neighborSet_subset h hv) h.disjoint.symm

/-- If `G.IsBipartiteWith s t` and `w ∈ t`, then if `v` is adjacent to `w` in `G` then `v ∈ s`. -/
/-
**SimpleGraph.IsBipartiteWith.mem_of_mem_adj'** 是 Mathlib 中的一个定理，位于命名空间 `SimpleG
raph.IsBipartiteWith`。
形式化陈述：∀ {V : Type u_1} {v w : V} {G : SimpleGraph V} {s t : Set V}, G.IsBipartit
eWith s t → w ∈ t → G.Adj v w → v ∈ s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.disjoint_right`：disjoint_right : Disjoint s t ↔ forall ⦃a⦄, a in t -
> a ∉ s
· 使用定理 `SimpleGraph.IsBipartiteWith.disjoint`：∀ {V : Type u_1} {G : SimpleGraph 
V} {s t : Set V}, G.IsBipartiteWith s t → Disjoint s t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `SimpleGraph.IsBipartiteWith.mem_of_adj`：∀ {V : Type u_1} {G : SimpleGrap
h V} {s t : Set V},   G.IsBipartiteWith s t → ∀ ⦃v w : V⦄, G.Adj v w → v ∈ s ∧ w
 ∈ t ∨ v ∈ t ∧ w ∈ s

--- 原说明 ---
If `G.IsBipartiteWith s t` and `w ∈ t`, then if `v` is adjacent to `w` in `G` th
en `v ∈ s`.
-/
theorem IsBipartiteWith.mem_of_mem_adj'
    (h : G.IsBipartiteWith s t) (hw : w ∈ t) (hadj : G.Adj v w) : v ∈ s := by
  apply h.mem_of_adj at hadj
  have nhw : w ∉ s := Set.disjoint_right.mp h.disjoint hw
  simpa [hw, nhw] using hadj

/-- If `G.IsBipartiteWith s t` and `w ∈ t`, then the neighbor set of `w` is the set of vertices in
`s` adjacent to `w` in `G`. -/
/-
**SimpleGraph.isBipartiteWith_neighborSet'** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h`。
形式化陈述：isBipartiteWith_neighborSet' (h : G.IsBipartiteWith s t) (hw : w in t) : G
.neighborSet w = { v in s | G.Adj v w }
参数：h : G.IsBipartiteWith s t；hw : w in t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.mem_neighborSet`：mem_neighborSet (v w : V) : w in G.neighbor
Set v ↔ G.Adj v w
· 使用定理 `SimpleGraph.adj_comm`：adj_comm (u v : V) : G.Adj u v ↔ G.Adj v u
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `iff_and_self`：∀ {p q : Prop}, (p ↔ q ∧ p) ↔ p → q
· 使用定理 `SimpleGraph.IsBipartiteWith.mem_of_mem_adj'`：∀ {V : Type u_1} {v w : V} 
{G : SimpleGraph V} {s t : Set V}, G.IsBipartiteWith s t → w ∈ t → G.Adj v w → v
 ∈ s

--- 原说明 ---
If `G.IsBipartiteWith s t` and `w ∈ t`, then the neighbor set of `w` is the set 
of vertices in
`s` adjacent to `w` in `G`.
-/
theorem isBipartiteWith_neighborSet' (h : G.IsBipartiteWith s t) (hw : w ∈ t) :
    G.neighborSet w = { v ∈ s | G.Adj v w } := by
  ext v
  rw [mem_neighborSet, adj_comm, Set.mem_ofPred_eq, iff_and_self]
  exact h.mem_of_mem_adj' hw

/-- If `G.IsBipartiteWith s t` and `w ∈ t`, then the neighbor set of `w` is a subset of `s`. -/
/-
**SimpleGraph.isBipartiteWith_neighborSet_subset'** 是 Mathlib 中的一个定理，位于命名空间 `Sim
pleGraph`。
形式化陈述：isBipartiteWith_neighborSet_subset' (h : G.IsBipartiteWith s t) (hw : w in
 t) : G.neighborSet w subseteq s
参数：h : G.IsBipartiteWith s t；hw : w in t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.isBipartiteWith_neighborSet'`：isBipartiteWith_neighborSet' (
h : G.IsBipartiteWith s t) (hw : w in t) : G.neighborSet w = { v in s | G.Adj v 
w }
· 使用定理 `Set.sep_subset`：sep_subset (s : Set α) (p : α -> Prop) : { x in s | p x 
} subseteq s

--- 原说明 ---
If `G.IsBipartiteWith s t` and `w ∈ t`, then the neighbor set of `w` is a subset
 of `s`.
-/
theorem isBipartiteWith_neighborSet_subset' (h : G.IsBipartiteWith s t) (hw : w ∈ t) :
    G.neighborSet w ⊆ s := by
  rw [isBipartiteWith_neighborSet' h hw]
  exact Set.sep_subset s (G.Adj · w)

/-- If `G.IsBipartiteWith s t`, then the support of `G` is a subset of `s ∪ t`. -/
/-
**SimpleGraph.isBipartiteWith_support_subset** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGr
aph`。
形式化陈述：isBipartiteWith_support_subset (h : G.IsBipartiteWith s t) : G.support sub
seteq s union t
参数：h : G.IsBipartiteWith s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsBipartiteWith.mem_of_adj`：∀ {V : Type u_1} {G : SimpleGrap
h V} {s t : Set V},   G.IsBipartiteWith s t → ∀ ⦃v w : V⦄, G.Adj v w → v ∈ s ∧ w
 ∈ t ∨ v ∈ t ∧ w ∈ s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b

--- 原说明 ---
If `G.IsBipartiteWith s t`, then the support of `G` is a subset of `s ∪ t`.
-/
theorem isBipartiteWith_support_subset (h : G.IsBipartiteWith s t) : G.support ⊆ s ∪ t := by
  intro v ⟨w, hadj⟩
  apply h.mem_of_adj at hadj
  tauto

/-- If `G.IsBipartiteWith s t` and `w ∈ t`, then the neighbor set of `w` is disjoint to `t`. -/
/-
**SimpleGraph.isBipartiteWith_neighborSet_disjoint'** 是 Mathlib 中的一个定理，位于命名空间 `S
impleGraph`。
形式化陈述：isBipartiteWith_neighborSet_disjoint' (h : G.IsBipartiteWith s t) (hw : w 
in t) : Disjoint (G.neighborSet w) t
参数：h : G.IsBipartiteWith s t；hw : w in t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.disjoint_of_subset_left`：disjoint_of_subset_left (h : s subseteq u) 
(d : Disjoint u t) : Disjoint s t
· 使用定理 `SimpleGraph.isBipartiteWith_neighborSet_subset'`：isBipartiteWith_neighbo
rSet_subset' (h : G.IsBipartiteWith s t) (hw : w in t) : G.neighborSet w subsete
q s
· 使用定理 `SimpleGraph.IsBipartiteWith.disjoint`：∀ {V : Type u_1} {G : SimpleGraph 
V} {s t : Set V}, G.IsBipartiteWith s t → Disjoint s t

--- 原说明 ---
If `G.IsBipartiteWith s t` and `w ∈ t`, then the neighbor set of `w` is disjoint
 to `t`.
-/
theorem isBipartiteWith_neighborSet_disjoint' (h : G.IsBipartiteWith s t) (hw : w ∈ t) :
    Disjoint (G.neighborSet w) t :=
  Set.disjoint_of_subset_left (isBipartiteWith_neighborSet_subset' h hw) h.disjoint

variable {s t : Finset V}

section

variable [Fintype ↑(G.neighborSet v)] [Fintype ↑(G.neighborSet w)]

section decidableRel

variable [DecidableRel G.Adj]

/-- If `G.IsBipartiteWith s t` and `v ∈ s`, then the neighbor finset of `v` is the set of vertices
in `s` adjacent to `v` in `G`. -/
/-
**SimpleGraph.isBipartiteWith_neighborFinset** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGr
aph`。
形式化陈述：isBipartiteWith_neighborFinset (h : G.IsBipartiteWith s t) (hv : v in s) :
 G.neighborFinset v = { w in t | G.Adj v w }
参数：h : G.IsBipartiteWith s t；hv : v in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.mem_neighborFinset`：mem_neighborFinset (w : V) : w in G.neig
hborFinset v ↔ G.Adj v w
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `iff_and_self`：∀ {p q : Prop}, (p ↔ q ∧ p) ↔ p → q
· 使用定理 `SimpleGraph.IsBipartiteWith.mem_of_mem_adj`：∀ {V : Type u_1} {v w : V} {
G : SimpleGraph V} {s t : Set V}, G.IsBipartiteWith s t → v ∈ s → G.Adj v w → w 
∈ t

--- 原说明 ---
If `G.IsBipartiteWith s t` and `v ∈ s`, then the neighbor finset of `v` is the s
et of vertices
in `s` adjacent to `v` in `G`.
-/
theorem isBipartiteWith_neighborFinset (h : G.IsBipartiteWith s t) (hv : v ∈ s) :
    G.neighborFinset v = { w ∈ t | G.Adj v w } := by
  ext w
  rw [mem_neighborFinset, mem_filter, iff_and_self]
  exact h.mem_of_mem_adj hv

/-- If `G.IsBipartiteWith s t` and `w ∈ t`, then the neighbor finset of `w` is the set of vertices
in `s` adjacent to `w` in `G`. -/
/-
**SimpleGraph.isBipartiteWith_neighborFinset'** 是 Mathlib 中的一个定理，位于命名空间 `SimpleG
raph`。
形式化陈述：isBipartiteWith_neighborFinset' (h : G.IsBipartiteWith s t) (hw : w in t) 
: G.neighborFinset w = { v in s | G.Adj v w }
参数：h : G.IsBipartiteWith s t；hw : w in t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.mem_neighborFinset`：mem_neighborFinset (w : V) : w in G.neig
hborFinset v ↔ G.Adj v w
· 使用定理 `SimpleGraph.adj_comm`：adj_comm (u v : V) : G.Adj u v ↔ G.Adj v u
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `iff_and_self`：∀ {p q : Prop}, (p ↔ q ∧ p) ↔ p → q
· 使用定理 `SimpleGraph.IsBipartiteWith.mem_of_mem_adj'`：∀ {V : Type u_1} {v w : V} 
{G : SimpleGraph V} {s t : Set V}, G.IsBipartiteWith s t → w ∈ t → G.Adj v w → v
 ∈ s

--- 原说明 ---
If `G.IsBipartiteWith s t` and `w ∈ t`, then the neighbor finset of `w` is the s
et of vertices
in `s` adjacent to `w` in `G`.
-/
theorem isBipartiteWith_neighborFinset' (h : G.IsBipartiteWith s t) (hw : w ∈ t) :
    G.neighborFinset w = { v ∈ s | G.Adj v w } := by
  ext v
  rw [mem_neighborFinset, adj_comm, mem_filter, iff_and_self]
  exact h.mem_of_mem_adj' hw

/-- If `G.IsBipartiteWith s t` and `v ∈ s`, then the neighbor finset of `v` is the set of vertices
"above" `v` according to the adjacency relation of `G`. -/
/-
**SimpleGraph.isBipartiteWith_bipartiteAbove** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGr
aph`。
形式化陈述：isBipartiteWith_bipartiteAbove (h : G.IsBipartiteWith s t) (hv : v in s) :
 G.neighborFinset v = bipartiteAbove G.Adj t v
参数：h : G.IsBipartiteWith s t；hv : v in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.isBipartiteWith_neighborFinset`：isBipartiteWith_neighborFins
et (h : G.IsBipartiteWith s t) (hv : v in s) : G.neighborFinset v = { w in t | G
.Adj v w }
· 使用定理 `Finset.bipartiteAbove.eq_1`：∀ {α : Type u_2} {β : Type u_3} (r : α → β →
 Prop) (t : Finset β) (a : α) [inst : DecidablePred (r a)],   Finset.bipartiteAb
ove r t a = {b ∈…

--- 原说明 ---
If `G.IsBipartiteWith s t` and `v ∈ s`, then the neighbor finset of `v` is the s
et of vertices
"above" `v` according to the adjacency relation of `G`.
-/
theorem isBipartiteWith_bipartiteAbove (h : G.IsBipartiteWith s t) (hv : v ∈ s) :
    G.neighborFinset v = bipartiteAbove G.Adj t v := by
  rw [isBipartiteWith_neighborFinset h hv, bipartiteAbove]

/-- If `G.IsBipartiteWith s t` and `w ∈ t`, then the neighbor finset of `w` is the set of vertices
"below" `w` according to the adjacency relation of `G`. -/
/-
**SimpleGraph.isBipartiteWith_bipartiteBelow** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGr
aph`。
形式化陈述：isBipartiteWith_bipartiteBelow (h : G.IsBipartiteWith s t) (hw : w in t) :
 G.neighborFinset w = bipartiteBelow G.Adj s w
参数：h : G.IsBipartiteWith s t；hw : w in t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.isBipartiteWith_neighborFinset'`：isBipartiteWith_neighborFin
set' (h : G.IsBipartiteWith s t) (hw : w in t) : G.neighborFinset w = { v in s |
 G.Adj v w }
· 使用定理 `Finset.bipartiteBelow.eq_1`：∀ {α : Type u_2} {β : Type u_3} (r : α → β →
 Prop) (s : Finset α) (b : β) [inst : (a : α) → Decidable (r a b)],   Finset.bip
artiteBelow r s …

--- 原说明 ---
If `G.IsBipartiteWith s t` and `w ∈ t`, then the neighbor finset of `w` is the s
et of vertices
"below" `w` according to the adjacency relation of `G`.
-/
theorem isBipartiteWith_bipartiteBelow (h : G.IsBipartiteWith s t) (hw : w ∈ t) :
    G.neighborFinset w = bipartiteBelow G.Adj s w := by
  rw [isBipartiteWith_neighborFinset' h hw, bipartiteBelow]

end decidableRel

/-- If `G.IsBipartiteWith s t` and `v ∈ s`, then the neighbor finset of `v` is a subset of `s`. -/
/-
**SimpleGraph.isBipartiteWith_neighborFinset_subset** 是 Mathlib 中的一个定理，位于命名空间 `S
impleGraph`。
形式化陈述：isBipartiteWith_neighborFinset_subset (h : G.IsBipartiteWith s t) (hv : v 
in s) : G.neighborFinset v subseteq t
参数：h : G.IsBipartiteWith s t；hv : v in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.isBipartiteWith_neighborFinset`：isBipartiteWith_neighborFins
et (h : G.IsBipartiteWith s t) (hv : v in s) : G.neighborFinset v = { w in t | G
.Adj v w }
· 使用定理 `Finset.filter_subset`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidableP
red p] (s : Finset α), Finset.filter p s ⊆ s

--- 原说明 ---
If `G.IsBipartiteWith s t` and `v ∈ s`, then the neighbor finset of `v` is a sub
set of `s`.
-/
theorem isBipartiteWith_neighborFinset_subset (h : G.IsBipartiteWith s t) (hv : v ∈ s) :
    G.neighborFinset v ⊆ t := by
  classical
  rw [isBipartiteWith_neighborFinset h hv]
  exact filter_subset (G.Adj v ·) t

/-- If `G.IsBipartiteWith s t` and `v ∈ s`, then the neighbor finset of `v` is disjoint to `s`. -/
/-
**SimpleGraph.isBipartiteWith_neighborFinset_disjoint** 是 Mathlib 中的一个定理，位于命名空间 
`SimpleGraph`。
形式化陈述：isBipartiteWith_neighborFinset_disjoint (h : G.IsBipartiteWith s t) (hv : 
v in s) : Disjoint (G.neighborFinset v) s
参数：h : G.IsBipartiteWith s t；hv : v in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.neighborFinset_def`：neighborFinset_def : G.neighborFinset v 
= (G.neighborSet v).toFinset
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.disjoint_coe`：disjoint_coe : Disjoint (s : Set α) t ↔ Disjoint s 
t
· 使用定理 `Set.coe_toFinset`：coe_toFinset (s : Set α) [Fintype s] : (↑s.toFinset : 
Set α) = s
· 使用定理 `SimpleGraph.isBipartiteWith_neighborSet_disjoint`：isBipartiteWith_neighb
orSet_disjoint (h : G.IsBipartiteWith s t) (hv : v in s) : Disjoint (G.neighborS
et v) s

--- 原说明 ---
If `G.IsBipartiteWith s t` and `v ∈ s`, then the neighbor finset of `v` is disjo
int to `s`.
-/
theorem isBipartiteWith_neighborFinset_disjoint (h : G.IsBipartiteWith s t) (hv : v ∈ s) :
    Disjoint (G.neighborFinset v) s := by
  rw [neighborFinset_def, ← disjoint_coe, Set.coe_toFinset]
  exact isBipartiteWith_neighborSet_disjoint h hv

/-- If `G.IsBipartiteWith s t` and `v ∈ s`, then the degree of `v` in `G` is at most the size of
`t`. -/
/-
**SimpleGraph.isBipartiteWith_degree_le** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：isBipartiteWith_degree_le (h : G.IsBipartiteWith s t) (hv : v in s) : G.de
gree v <= #t
参数：h : G.IsBipartiteWith s t；hv : v in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.card_neighborFinset_eq_degree`：card_neighborFinset_eq_degree
 : #(G.neighborFinset v) = G.degree v
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `SimpleGraph.isBipartiteWith_neighborFinset_subset`：isBipartiteWith_neigh
borFinset_subset (h : G.IsBipartiteWith s t) (hv : v in s) : G.neighborFinset v 
subseteq t

--- 原说明 ---
If `G.IsBipartiteWith s t` and `v ∈ s`, then the degree of `v` in `G` is at most
 the size of
`t`.
-/
theorem isBipartiteWith_degree_le (h : G.IsBipartiteWith s t) (hv : v ∈ s) : G.degree v ≤ #t := by
  rw [← card_neighborFinset_eq_degree]
  exact card_le_card (isBipartiteWith_neighborFinset_subset h hv)

/-- If `G.IsBipartiteWith s t` and `w ∈ t`, then the neighbor finset of `w` is a subset of `s`. -/
/-
**SimpleGraph.isBipartiteWith_neighborFinset_subset'** 是 Mathlib 中的一个定理，位于命名空间 `
SimpleGraph`。
形式化陈述：isBipartiteWith_neighborFinset_subset' (h : G.IsBipartiteWith s t) (hw : w
 in t) : G.neighborFinset w subseteq s
参数：h : G.IsBipartiteWith s t；hw : w in t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.isBipartiteWith_neighborFinset'`：isBipartiteWith_neighborFin
set' (h : G.IsBipartiteWith s t) (hw : w in t) : G.neighborFinset w = { v in s |
 G.Adj v w }
· 使用定理 `Finset.filter_subset`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidableP
red p] (s : Finset α), Finset.filter p s ⊆ s

--- 原说明 ---
If `G.IsBipartiteWith s t` and `w ∈ t`, then the neighbor finset of `w` is a sub
set of `s`.
-/
theorem isBipartiteWith_neighborFinset_subset' (h : G.IsBipartiteWith s t) (hw : w ∈ t) :
    G.neighborFinset w ⊆ s := by
  classical
  rw [isBipartiteWith_neighborFinset' h hw]
  exact filter_subset (G.Adj · w) s

/-- If `G.IsBipartiteWith s t` and `w ∈ t`, then the neighbor finset of `w` is disjoint to `t`. -/
/-
**SimpleGraph.isBipartiteWith_neighborFinset_disjoint'** 是 Mathlib 中的一个定理，位于命名空间
 `SimpleGraph`。
形式化陈述：isBipartiteWith_neighborFinset_disjoint' (h : G.IsBipartiteWith s t) (hw :
 w in t) : Disjoint (G.neighborFinset w) t
参数：h : G.IsBipartiteWith s t；hw : w in t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.neighborFinset_def`：neighborFinset_def : G.neighborFinset v 
= (G.neighborSet v).toFinset
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.disjoint_coe`：disjoint_coe : Disjoint (s : Set α) t ↔ Disjoint s 
t
· 使用定理 `Set.coe_toFinset`：coe_toFinset (s : Set α) [Fintype s] : (↑s.toFinset : 
Set α) = s
· 使用定理 `SimpleGraph.isBipartiteWith_neighborSet_disjoint'`：isBipartiteWith_neigh
borSet_disjoint' (h : G.IsBipartiteWith s t) (hw : w in t) : Disjoint (G.neighbo
rSet w) t

--- 原说明 ---
If `G.IsBipartiteWith s t` and `w ∈ t`, then the neighbor finset of `w` is disjo
int to `t`.
-/
theorem isBipartiteWith_neighborFinset_disjoint' (h : G.IsBipartiteWith s t) (hw : w ∈ t) :
    Disjoint (G.neighborFinset w) t := by
  rw [neighborFinset_def, ← disjoint_coe, Set.coe_toFinset]
  exact isBipartiteWith_neighborSet_disjoint' h hw

/-- If `G.IsBipartiteWith s t` and `w ∈ t`, then the degree of `w` in `G` is at most the size of
`s`. -/
/-
**SimpleGraph.isBipartiteWith_degree_le'** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`
。
形式化陈述：isBipartiteWith_degree_le' (h : G.IsBipartiteWith s t) (hw : w in t) : G.d
egree w <= #s
参数：h : G.IsBipartiteWith s t；hw : w in t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.card_neighborFinset_eq_degree`：card_neighborFinset_eq_degree
 : #(G.neighborFinset v) = G.degree v
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `SimpleGraph.isBipartiteWith_neighborFinset_subset'`：isBipartiteWith_neig
hborFinset_subset' (h : G.IsBipartiteWith s t) (hw : w in t) : G.neighborFinset 
w subseteq s

--- 原说明 ---
If `G.IsBipartiteWith s t` and `w ∈ t`, then the degree of `w` in `G` is at most
 the size of
`s`.
-/
theorem isBipartiteWith_degree_le' (h : G.IsBipartiteWith s t) (hw : w ∈ t) : G.degree w ≤ #s := by
  rw [← card_neighborFinset_eq_degree]
  exact card_le_card (isBipartiteWith_neighborFinset_subset' h hw)

end

/-- If `G.IsBipartiteWith s t`, then the sum of the degrees of vertices in `s` is equal to the sum
of the degrees of vertices in `t`.

See `Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow`. -/
/-
**SimpleGraph.isBipartiteWith_sum_degrees_eq** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGr
aph`。
形式化陈述：isBipartiteWith_sum_degrees_eq [G.LocallyFinite] (h : G.IsBipartiteWith s 
t) : ∑ v in s, G.degree v = ∑ w in t, G.degree w
参数：h : G.IsBipartiteWith s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_attach`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid
 M] (s : Finset ι) (f : ι → M), ∑ x ∈ s.attach, f ↑x = ∑ x ∈ s, f x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SimpleGraph.isBipartiteWith_bipartiteAbove`：isBipartiteWith_bipartiteAbo
ve (h : G.IsBipartiteWith s t) (hv : v in s) : G.neighborFinset v = bipartiteAbo
ve G.Adj t v
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `SimpleGraph.isBipartiteWith_bipartiteBelow`：isBipartiteWith_bipartiteBel
ow (h : G.IsBipartiteWith s t) (hw : w in t) : G.neighborFinset w = bipartiteBel
ow G.Adj s w
· 使用定理 `Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow`：sum_card_bipa
rtiteAbove_eq_sum_card_bipartiteBelow [forall a b, Decidable (r a b)] : (∑ a in 
s, #(t.bipartiteAbove r a)) = ∑ b in t, #(s.bip…

--- 原说明 ---
If `G.IsBipartiteWith s t`, then the sum of the degrees of vertices in `s` is eq
ual to the sum
of the degrees of vertices in `t`.

See `Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow`.
-/
theorem isBipartiteWith_sum_degrees_eq [G.LocallyFinite] (h : G.IsBipartiteWith s t) :
    ∑ v ∈ s, G.degree v = ∑ w ∈ t, G.degree w := by
  classical
  simp_rw [← sum_attach t, ← sum_attach s, ← card_neighborFinset_eq_degree]
  conv_lhs =>
    rhs; intro v
    rw [isBipartiteWith_bipartiteAbove h v.prop]
  conv_rhs =>
    rhs; intro w
    rw [isBipartiteWith_bipartiteBelow h w.prop]
  simp_rw [sum_attach s fun w ↦ #(bipartiteAbove G.Adj t w),
    sum_attach t fun v ↦ #(bipartiteBelow G.Adj s v)]
  exact sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow G.Adj

variable [Fintype V] [DecidableRel G.Adj]
/-
**SimpleGraph.isBipartiteWith_sum_degrees_eq_twice_card_edges** 是 Mathlib 中的一个引理
，位于命名空间 `SimpleGraph`。
形式化陈述：isBipartiteWith_sum_degrees_eq_twice_card_edges [DecidableEq V] (h : G.IsB
ipartiteWith s t) : ∑ v in s union t, G.degree v = 2 * #G.edgeFinset
参数：h : G.IsBipartiteWith s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.isBipartiteWith_support_subset`：isBipartiteWith_support_subs
et (h : G.IsBipartiteWith s t) : G.support subseteq s union t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_subset`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [i
nst : AddCommMonoid M] {f : ι → M},   s₁ ⊆ s₂ → (∀ x ∈ s₂, x ∉ s₁ → f x = 0) → ∑
 x ∈ s₁…
· 使用定理 `Set.toFinset_subset`：toFinset_subset [Fintype s] {t : Finset α} : s.toFi
nset subseteq t ↔ s subseteq t
· 使用定理 `Finset.coe_union`：coe_union (s₁ s₂ : Finset α) : ↑(s₁ union s₂) = (s₁ un
ion s₂ : Set α)
· 使用定理 `SimpleGraph.degree_eq_zero_iff_notMem_support`：degree_eq_zero_iff_notMem
_support : G.degree v = 0 ↔ v ∉ G.support
· 使用定理 `Set.mem_toFinset`：mem_toFinset {s : Set α} [Fintype s] {a : α} : a in s.
toFinset ↔ a in s
· 使用定理 `SimpleGraph.sum_degrees_support_eq_twice_card_edges`：sum_degrees_support
_eq_twice_card_edges : ∑ v in G.support, G.degree v = 2 * #G.edgeFinset
-/
lemma isBipartiteWith_sum_degrees_eq_twice_card_edges [DecidableEq V] (h : G.IsBipartiteWith s t) :
    ∑ v ∈ s ∪ t, G.degree v = 2 * #G.edgeFinset := by
  have hsub : G.support ⊆ ↑s ∪ ↑t := isBipartiteWith_support_subset h
  rw [← coe_union, ← Set.toFinset_subset] at hsub
  rw [← Finset.sum_subset hsub, ← sum_degrees_support_eq_twice_card_edges]
  intro v _ hv
  rwa [Set.mem_toFinset, ← degree_eq_zero_iff_notMem_support] at hv

/-- The degree-sum formula for bipartite graphs, summing over the "left" part.

See `SimpleGraph.sum_degrees_eq_twice_card_edges` for the general version, and
`SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges'` for the version from the "right". -/
/-
**SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges** 是 Mathlib 中的一个定理，位于命名空
间 `SimpleGraph`。
形式化陈述：isBipartiteWith_sum_degrees_eq_card_edges (h : G.IsBipartiteWith s t) : ∑ 
v in s, G.degree v = #G.edgeFinset
参数：h : G.IsBipartiteWith s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.mul_left_cancel_iff`：∀ {n : ℕ}, 0 < n → ∀ {m k : ℕ}, n * m = n * k ↔
 m = k
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `SimpleGraph.isBipartiteWith_sum_degrees_eq_twice_card_edges`：isBipartite
With_sum_degrees_eq_twice_card_edges [DecidableEq V] (h : G.IsBipartiteWith s t)
 : ∑ v in s union t, G.degree v = 2 * #G.edgeFins…
· 使用定理 `Finset.sum_union`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   Disjoint s₁ s₂ → ∑
 x ∈ s…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.disjoint_coe`：disjoint_coe : Disjoint (s : Set α) t ↔ Disjoint s 
t
· 使用定理 `SimpleGraph.IsBipartiteWith.disjoint`：∀ {V : Type u_1} {G : SimpleGraph 
V} {s t : Set V}, G.IsBipartiteWith s t → Disjoint s t
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `add_right_inj`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G] (a : 
G) {b c : G}, a + b = a + c ↔ b = c
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `SimpleGraph.isBipartiteWith_sum_degrees_eq`：isBipartiteWith_sum_degrees_
eq [G.LocallyFinite] (h : G.IsBipartiteWith s t) : ∑ v in s, G.degree v = ∑ w in
 t, G.degree w

--- 原说明 ---
The degree-sum formula for bipartite graphs, summing over the "left" part.

See `SimpleGraph.sum_degrees_eq_twice_card_edges` for the general version, and
`SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges'` for the version from th
e "right".
-/
theorem isBipartiteWith_sum_degrees_eq_card_edges (h : G.IsBipartiteWith s t) :
    ∑ v ∈ s, G.degree v = #G.edgeFinset := by
  classical
  rw [← Nat.mul_left_cancel_iff zero_lt_two, ← isBipartiteWith_sum_degrees_eq_twice_card_edges h,
    sum_union (disjoint_coe.mp h.disjoint), two_mul, add_right_inj]
  exact isBipartiteWith_sum_degrees_eq h

/-- The degree-sum formula for bipartite graphs, summing over the "right" part.

See `SimpleGraph.sum_degrees_eq_twice_card_edges` for the general version, and
`SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges` for the version from the "left". -/
/-
**SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges'** 是 Mathlib 中的一个定理，位于命名
空间 `SimpleGraph`。
形式化陈述：isBipartiteWith_sum_degrees_eq_card_edges' (h : G.IsBipartiteWith s t) : ∑
 v in t, G.degree v = #G.edgeFinset
参数：h : G.IsBipartiteWith s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges`：isBipartiteWith_s
um_degrees_eq_card_edges (h : G.IsBipartiteWith s t) : ∑ v in s, G.degree v = #G
.edgeFinset
· 使用定理 `SimpleGraph.IsBipartiteWith.symm`：∀ {V : Type u_1} {G : SimpleGraph V} {
s t : Set V}, G.IsBipartiteWith s t → G.IsBipartiteWith t s

--- 原说明 ---
The degree-sum formula for bipartite graphs, summing over the "right" part.

See `SimpleGraph.sum_degrees_eq_twice_card_edges` for the general version, and
`SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges` for the version from the
 "left".
-/
theorem isBipartiteWith_sum_degrees_eq_card_edges' (h : G.IsBipartiteWith s t) :
    ∑ v ∈ t, G.degree v = #G.edgeFinset := isBipartiteWith_sum_degrees_eq_card_edges h.symm

end IsBipartiteWith

section IsBipartite

/-- The predicate for a simple graph to be bipartite. -/
/-
**SimpleGraph.IsBipartite** 是 Mathlib 中的一个缩写定义，位于命名空间 `SimpleGraph`。
形式化陈述：IsBipartite (G : SimpleGraph V) : Prop
参数：G : SimpleGraph V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The predicate for a simple graph to be bipartite.
-/
abbrev IsBipartite (G : SimpleGraph V) : Prop := G.Colorable 2

/-- If a simple graph `G` is bipartite, then there exist disjoint sets `s` and `t`
such that all edges in `G` connect a vertex in `s` to a vertex in `t`. -/
/-
**SimpleGraph.IsBipartite.exists_isBipartiteWith** 是 Mathlib 中的一个定理，位于命名空间 `Simp
leGraph.IsBipartite`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V}, G.IsBipartite → ∃ s t, G.IsBipartite
With s t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fin.instNeZeroHAddNatOfNat_mathlib_1`：∀ (n : ℕ) [NeZero n], NeZero 1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
If a simple graph `G` is bipartite, then there exist disjoint sets `s` and `t`
such that all edges in `G` connect a vertex in `s` to a vertex in `t`.
-/
lemma IsBipartite.exists_isBipartiteWith (h : G.IsBipartite) : ∃ s t, G.IsBipartiteWith s t := by
  obtain ⟨c, hc⟩ := h
  refine ⟨{v | c v = 0}, {v | c v = 1}, by aesop (add simp [Set.disjoint_left]), ?_⟩
  rintro v w hvw
  apply hc at hvw
  simp [Set.mem_ofPred_eq] at hvw ⊢
  lia

/-- If a simple graph `G` has a bipartition, then it is bipartite. -/
/-
**SimpleGraph.IsBipartiteWith.isBipartite** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph
.IsBipartiteWith`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {s t : Set V}, G.IsBipartiteWith s t 
→ G.IsBipartite
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `SimpleGraph.IsBipartiteWith.mem_of_adj`：∀ {V : Type u_1} {G : SimpleGrap
h V} {s t : Set V},   G.IsBipartiteWith s t → ∀ ⦃v w : V⦄, G.Adj v w → v ∈ s ∧ w
 ∈ t ∨ v ∈ t ∧ w ∈ s
· 使用定理 `Disjoint.subset_compl_left`：∀ {α : Type u_1} {s t : Set α}, Disjoint t s
 → s ⊆ tᶜ
· 使用定理 `SimpleGraph.IsBipartiteWith.disjoint`：∀ {V : Type u_1} {G : SimpleGraph 
V} {s t : Set V}, G.IsBipartiteWith s t → Disjoint s t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Fin.instNeZeroHAddNatOfNat_mathlib_1`：∀ (n : ℕ) [NeZero n], NeZero 1

--- 原说明 ---
If a simple graph `G` has a bipartition, then it is bipartite.
-/
lemma IsBipartiteWith.isBipartite {s t : Set V} (h : G.IsBipartiteWith s t) : G.IsBipartite := by
  refine ⟨s.indicator 1, fun {v w} hw ↦ ?_⟩
  obtain (⟨hs, ht⟩ | ⟨ht, hs⟩) := h.2 hw <;>
    { replace ht : _ ∉ s := h.1.subset_compl_left ht; simp [hs, ht] }

/-- `G.IsBipartite` if and only if `G.IsBipartiteWith s t`. -/
/-
**SimpleGraph.isBipartite_iff_exists_isBipartiteWith** 是 Mathlib 中的一个定理，位于命名空间 `
SimpleGraph`。
形式化陈述：isBipartite_iff_exists_isBipartiteWith : G.IsBipartite ↔ exists s t : Set 
V, G.IsBipartiteWith s t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsBipartite.exists_isBipartiteWith`：∀ {V : Type u_1} {G : Si
mpleGraph V}, G.IsBipartite → ∃ s t, G.IsBipartiteWith s t
· 使用定理 `SimpleGraph.IsBipartiteWith.isBipartite`：∀ {V : Type u_1} {G : SimpleGra
ph V} {s t : Set V}, G.IsBipartiteWith s t → G.IsBipartite

--- 原说明 ---
`G.IsBipartite` if and only if `G.IsBipartiteWith s t`.
-/
theorem isBipartite_iff_exists_isBipartiteWith :
    G.IsBipartite ↔ ∃ s t : Set V, G.IsBipartiteWith s t :=
  ⟨IsBipartite.exists_isBipartiteWith, fun ⟨_, _, h⟩ ↦ h.isBipartite⟩
/-
**SimpleGraph.chromaticNumber_le_two_iff_isBipartite** 是 Mathlib 中的一个定理，位于命名空间 `
SimpleGraph`。
形式化陈述：chromaticNumber_le_two_iff_isBipartite : G.chromaticNumber <= 2 ↔ G.IsBipa
rtite
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.chromaticNumber_le_iff_colorable`：chromaticNumber_le_iff_col
orable {n : Nat} : G.chromaticNumber <= n ↔ G.Colorable n
-/
theorem chromaticNumber_le_two_iff_isBipartite : G.chromaticNumber ≤ 2 ↔ G.IsBipartite :=
  chromaticNumber_le_iff_colorable
/-
**SimpleGraph.chromaticNumber_eq_two_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`
。
形式化陈述：chromaticNumber_eq_two_iff : G.chromaticNumber = 2 ↔ G.IsBipartite ∧ G != 
⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.chromaticNumber_le_two_iff_isBipartite`：chromaticNumber_le_t
wo_iff_isBipartite : G.chromaticNumber <= 2 ↔ G.IsBipartite
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.two_le_chromaticNumber_iff_ne_bot`：two_le_chromaticNumber_if
f_ne_bot : 2 <= G.chromaticNumber ↔ G != ⊥
· 使用引理 `ENat.eq_of_forall_natCast_le_iff`：eq_of_forall_natCast_le_iff (hm : fora
ll a : Nat, a <= m ↔ a <= n) : m = n
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem chromaticNumber_eq_two_iff : G.chromaticNumber = 2 ↔ G.IsBipartite ∧ G ≠ ⊥ :=
  ⟨fun h ↦ ⟨chromaticNumber_le_two_iff_isBipartite.mp (by simp [h]),
            two_le_chromaticNumber_iff_ne_bot.mp (by simp [h])⟩,
   fun ⟨h₁, h₂⟩ ↦ ENat.eq_of_forall_natCast_le_iff fun _ ↦
      ⟨fun h ↦ h.trans <| chromaticNumber_le_two_iff_isBipartite.mpr h₁,
       fun h ↦ h.trans <| two_le_chromaticNumber_iff_ne_bot.mpr h₂⟩⟩

end IsBipartite

section Copy

variable {α β : Type*} [Fintype α] [Fintype β]

set_option backward.isDefEq.respectTransparency.types false in
/-- A "left" subset of `card α` vertices and a "right" subset of `card β` vertices such that every
vertex in the "left" subset is adjacent to every vertex in the "right" subset gives rise to a copy
of a complete bipartite graph. -/
/-
**SimpleGraph.Copy.completeBipartiteGraph** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph
.Copy`。
形式化陈述：{V : Type u_1} →   {G : SimpleGraph V} →     {α : Type u_2} →       {β : T
ype u_3} →         [inst : Fintype α] →           [inst_1 : Fintype β] →        
     (left right : Finset V) →               left.card = Fintype.card α →       
          right.card = Fintype.card β → G.IsCompleteBetween ↑left ↑right → (comp
leteBipartiteGraph α β).Copy G
参数：left right : Finset V；completeBipartiteGraph α β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A "left" subset of `card α` vertices and a "right" subset of `card β` vertices s
uch that every
vertex in the "left" subset is adjacent to every vertex in the "right" subset gi
ves rise to a copy
of a complete bipartite graph.
-/
noncomputable def Copy.completeBipartiteGraph
    (left right : Finset V) (card_left : #left = card α) (card_right : #right = card β)
    (h : G.IsCompleteBetween left right) : Copy (completeBipartiteGraph α β) G := by
  have : Nonempty (α ↪ left) := by
    rw [← card_coe] at card_left
    exact Function.Embedding.nonempty_of_card_le card_left.symm.le
  let fα : α ↪ left := Classical.arbitrary (α ↪ left)
  have : Nonempty (β ↪ right) := by
    rw [← card_coe] at card_right
    exact Function.Embedding.nonempty_of_card_le card_right.symm.le
  let fβ : β ↪ right := Classical.arbitrary (β ↪ right)
  let f : α ⊕ β ↪ V := by
    refine ⟨Sum.elim (Subtype.val ∘ fα) (Subtype.val ∘ fβ), fun s₁ s₂ ↦ ?_⟩
    match s₁, s₂ with
    | .inl p₁, .inl p₂ => simp
    | .inr p₁, .inl p₂ =>
      simpa using (h (fα p₂).prop (fβ p₁).prop).ne'
    | .inl p₁, .inr p₂ =>
      simpa using (h (fα p₁).prop (fβ p₂).prop).symm.ne'
    | .inr p₁, .inr p₂ => simp
  refine ⟨⟨f.toFun, fun {s₁ s₂} hadj ↦ ?_⟩, f.injective⟩
  rcases hadj with ⟨hs₁, hs₂⟩ | ⟨hs₁, hs₂⟩
  all_goals dsimp [f]
  · rw [← Sum.inl_getLeft s₁ hs₁, ← Sum.inr_getRight s₂ hs₂,
      Sum.elim_inl, Sum.elim_inr]
    exact h (by simp) (by simp)
  · rw [← Sum.inr_getRight s₁ hs₁, ← Sum.inl_getLeft s₂ hs₂,
      Sum.elim_inl, Sum.elim_inr, adj_comm]
    exact h (by simp) (by simp)

/-- Simple graphs contain a copy of a `completeBipartiteGraph α β` iff there exists a "left"
subset of `card α` vertices and a "right" subset of `card β` vertices such that every vertex
in the "left" subset is adjacent to every vertex in the "right" subset. -/
/-
**SimpleGraph.completeBipartiteGraph_isContained_iff** 是 Mathlib 中的一个定理，位于命名空间 `
SimpleGraph`。
形式化陈述：completeBipartiteGraph_isContained_iff : completeBipartiteGraph α β ⊑ G ↔ 
exists (left right : Finset V), #left = card α ∧ #right = card β ∧ G.IsCompleteB
etween left right where mp
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用引理 `SimpleGraph.Copy.injective`：injective (f : Copy A B) : Injective f.toHom
· 使用定理 `Sum.inl_injective`：inl_injective : Function.Injective (inl : α -> α oplu
s β)
· 使用定理 `Sum.inr_injective`：inr_injective : Function.Injective (inr : β -> α oplu
s β)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.mem_map`：mem_map {b : β} : b in s.map f ↔ exists a in s, f a = b
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Hom.map_adj`：map_adj {v w : V} (h : G.Adj v w) : G'.Adj (f v
) (f w)
· 使用定理 `completeBipartiteGraph_adj`：∀ (V : Type u_1) (W : Type u_2) (v w : V ⊕ W
),   (completeBipartiteGraph V W).Adj v w = (v.isLeft = true ∧ w.isRight = true 
∨ v.isRight = tr…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Bool.false_eq_true`：(false = true) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p

--- 原说明 ---
Simple graphs contain a copy of a `completeBipartiteGraph α β` iff there exists 
a "left"
subset of `card α` vertices and a "right" subset of `card β` vertices such that 
every vertex
in the "left" subset is adjacent to every vertex in the "right" subset.
-/
theorem completeBipartiteGraph_isContained_iff :
    completeBipartiteGraph α β ⊑ G ↔
      ∃ (left right : Finset V), #left = card α ∧ #right = card β
        ∧ G.IsCompleteBetween left right where
  mp := by
    refine fun ⟨f⟩ ↦ ⟨univ.map ⟨f ∘ Sum.inl, f.injective.comp Sum.inl_injective⟩,
      univ.map ⟨f ∘ Sum.inr, f.injective.comp Sum.inr_injective⟩, by simp, by simp,
      fun _ hl _ hr ↦ ?_⟩
    rw [mem_coe, mem_map] at hl hr
    replace ⟨_, _, hl⟩ := hl
    replace ⟨_, _, hr⟩ := hr
    rw [← hl, ← hr]
    exact f.toHom.map_adj (by simp)
  mpr := fun ⟨left, right, card_left, card_right, h⟩ ↦
    ⟨.completeBipartiteGraph left right card_left card_right h⟩

end Copy

/-
**SimpleGraph.IsBipartiteWith.subgraph** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Is
BipartiteWith`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {s t : Set V},   G.IsBipartiteWith s 
t → ∀ (H : G.Subgraph), H.coe.IsBipartiteWith {x | ↑x ∈ s} {x | ↑x ∈ t}
参数：H : G.Subgraph。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsBipartiteWith.mem_of_adj`：∀ {V : Type u_1} {G : SimpleGrap
h V} {s t : Set V},   G.IsBipartiteWith s t → ∀ ⦃v w : V⦄, G.Adj v w → v ∈ s ∧ w
 ∈ t ∨ v ∈ t ∧ w ∈ s
· 使用定理 `SimpleGraph.Subgraph.adj_sub`：∀ {V : Type u} {G : SimpleGraph V} (self :
 G.Subgraph) {v w : V}, self.Adj v w → G.Adj v w
-/
lemma IsBipartiteWith.subgraph (h : G.IsBipartiteWith s t) (H : Subgraph G) :
    H.coe.IsBipartiteWith {x : H.verts | ↑x ∈ s} {x : H.verts | ↑x ∈ t} :=
  ⟨by grind [h.disjoint], fun _ _ hadj' ↦ h.mem_of_adj <| H.adj_sub hadj'⟩
/-
**SimpleGraph.IsBipartite.subgraph** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsBipa
rtite`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V}, G.IsBipartite → ∀ (H : G.Subgraph), 
H.coe.IsBipartite
参数：H : G.Subgraph。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.isBipartite_iff_exists_isBipartiteWith`：isBipartite_iff_exis
ts_isBipartiteWith : G.IsBipartite ↔ exists s t : Set V, G.IsBipartiteWith s t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.IsBipartiteWith.subgraph`：∀ {V : Type u_1} {G : SimpleGraph 
V} {s t : Set V},   G.IsBipartiteWith s t → ∀ (H : G.Subgraph), H.coe.IsBipartit
eWith {x | ↑x ∈ s} {x | ↑x…
-/
lemma IsBipartite.subgraph (h : G.IsBipartite) (H : Subgraph G) : H.coe.IsBipartite :=
  let ⟨_, _, hst⟩ := isBipartite_iff_exists_isBipartiteWith.mp h
  isBipartite_iff_exists_isBipartiteWith.mpr ⟨_, _, IsBipartiteWith.subgraph hst H⟩

section Between

/-- The subgraph of `G` containing edges that connect a vertex in the set `s` to a vertex in the
set `t`. -/
/-
**SimpleGraph.between** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：between (s t : Set V) (G : SimpleGraph V) : SimpleGraph V where Adj v w
参数：s t : Set V；G : SimpleGraph V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subgraph of `G` containing edges that connect a vertex in the set `s` to a v
ertex in the
set `t`.
-/
def between (s t : Set V) (G : SimpleGraph V) : SimpleGraph V where
  Adj v w := G.Adj v w ∧ (v ∈ s ∧ w ∈ t ∨ v ∈ t ∧ w ∈ s)
  symm.symm v w := by tauto
/-
**SimpleGraph.between_adj** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：between_adj : (G.between s t).Adj v w ↔ G.Adj v w ∧ (v in s ∧ w in t ∨ v i
n t ∧ w in s)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma between_adj : (G.between s t).Adj v w ↔ G.Adj v w ∧ (v ∈ s ∧ w ∈ t ∨ v ∈ t ∧ w ∈ s) := by rfl
/-
**SimpleGraph.between_le** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：between_le : G.between s t <= G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma between_le : G.between s t ≤ G := fun _ _ h ↦ h.1
/-
**SimpleGraph.between_comm** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：between_comm : G.between s t = G.between t s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.mk.congr_simp`：∀ {V : Type u} (Adj Adj_1 : V → V → Prop) (e_
Adj : Adj = Adj_1) (symm : Std.Symm Adj) (loopless : Std.Irrefl Adj),   { Adj :=
 Adj, symm := s…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma between_comm : G.between s t = G.between t s := by simp [between, or_comm]
/-
**SimpleGraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableRel G.Adj] [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)] :
    DecidableRel (G.between s t).Adj :=
  inferInstanceAs (DecidableRel fun v w ↦ G.Adj v w ∧ (v ∈ s ∧ w ∈ t ∨ v ∈ t ∧ w ∈ s))

/-- `G.between s t` is bipartite if the sets `s` and `t` are disjoint. -/
/-
**SimpleGraph.between_isBipartiteWith** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：between_isBipartiteWith (h : Disjoint s t) : (G.between s t).IsBipartiteWi
th s t where disjoint
参数：h : Disjoint s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
`G.between s t` is bipartite if the sets `s` and `t` are disjoint.
-/
theorem between_isBipartiteWith (h : Disjoint s t) : (G.between s t).IsBipartiteWith s t where
  disjoint := h
  mem_of_adj _ _ h := h.2

/-- `G.between s t` is bipartite if the sets `s` and `t` are disjoint. -/
/-
**SimpleGraph.between_isBipartite** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：between_isBipartite (h : Disjoint s t) : (G.between s t).IsBipartite
参数：h : Disjoint s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsBipartiteWith.isBipartite`：∀ {V : Type u_1} {G : SimpleGra
ph V} {s t : Set V}, G.IsBipartiteWith s t → G.IsBipartite
· 使用定理 `SimpleGraph.between_isBipartiteWith`：between_isBipartiteWith (h : Disjoi
nt s t) : (G.between s t).IsBipartiteWith s t where disjoint

--- 原说明 ---
`G.between s t` is bipartite if the sets `s` and `t` are disjoint.
-/
theorem between_isBipartite (h : Disjoint s t) : (G.between s t).IsBipartite :=
  (between_isBipartiteWith h).isBipartite

/-- The neighbor set of `v ∈ s` in `G.between s sᶜ` excludes the vertices in `s` adjacent to `v`
in `G`. -/
/-
**SimpleGraph.neighborSet_subset_between_union** 是 Mathlib 中的一个引理，位于命名空间 `Simple
Graph`。
形式化陈述：neighborSet_subset_between_union (hv : v in s) : G.neighborSet v subseteq 
(G.between s sᶜ).neighborSet v union s
参数：hv : v in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.neighborSet.eq_1`：∀ {V : Type u} (G : SimpleGraph V) (v : V)
, G.neighborSet v = {w | G.Adj v w}
· 使用定理 `Set.mem_union`：mem_union (x : α) (a b : Set α) : x in a union b ↔ x in a
 ∨ x in b
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用引理 `SimpleGraph.between_adj`：between_adj : (G.between s t).Adj v w ↔ G.Adj v
 w ∧ (v in s ∧ w in t ∨ v in t ∧ w in s)

--- 原说明 ---
The neighbor set of `v ∈ s` in `G.between s sᶜ` excludes the vertices in `s` adj
acent to `v`
in `G`.
-/
lemma neighborSet_subset_between_union (hv : v ∈ s) :
    G.neighborSet v ⊆ (G.between s sᶜ).neighborSet v ∪ s := by
  intro w hadj
  rw [neighborSet, Set.mem_union, Set.mem_ofPred, between_adj]
  by_cases hw : w ∈ s
  · exact Or.inr hw
  · exact Or.inl ⟨hadj, Or.inl ⟨hv, hw⟩⟩

/-- The neighbor set of `w ∈ sᶜ` in `G.between s sᶜ` excludes the vertices in `sᶜ` adjacent to `w`
in `G`. -/
/-
**SimpleGraph.neighborSet_subset_between_union_compl** 是 Mathlib 中的一个引理，位于命名空间 `
SimpleGraph`。
形式化陈述：neighborSet_subset_between_union_compl (hw : w in sᶜ) : G.neighborSet w su
bseteq (G.between s sᶜ).neighborSet w union sᶜ
参数：hw : w in sᶜ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.neighborSet.eq_1`：∀ {V : Type u} (G : SimpleGraph V) (v : V)
, G.neighborSet v = {w | G.Adj v w}
· 使用定理 `Set.mem_union`：mem_union (x : α) (a b : Set α) : x in a union b ↔ x in a
 ∨ x in b
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用引理 `SimpleGraph.between_adj`：between_adj : (G.between s t).Adj v w ↔ G.Adj v
 w ∧ (v in s ∧ w in t ∨ v in t ∧ w in s)

--- 原说明 ---
The neighbor set of `w ∈ sᶜ` in `G.between s sᶜ` excludes the vertices in `sᶜ` a
djacent to `w`
in `G`.
-/
lemma neighborSet_subset_between_union_compl (hw : w ∈ sᶜ) :
    G.neighborSet w ⊆ (G.between s sᶜ).neighborSet w ∪ sᶜ := by
  intro v hadj
  rw [neighborSet, Set.mem_union, Set.mem_ofPred, between_adj]
  by_cases hv : v ∈ s
  · exact Or.inl ⟨hadj, Or.inr ⟨hw, hv⟩⟩
  · exact Or.inr hv

variable [DecidableEq V] [Fintype V] {s t : Finset V} [DecidableRel G.Adj]

/-- The neighbor finset of `v ∈ s` in `G.between s sᶜ` excludes the vertices in `s` adjacent to `v`
in `G`. -/
/-
**SimpleGraph.neighborFinset_subset_between_union** 是 Mathlib 中的一个引理，位于命名空间 `Sim
pleGraph`。
形式化陈述：neighborFinset_subset_between_union (hv : v in s) : G.neighborFinset v sub
seteq (G.between s sᶜ).neighborFinset v union s
参数：hv : v in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_union`：coe_union (s₁ s₂ : Finset α) : ↑(s₁ union s₂) = (s₁ un
ion s₂ : Set α)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.coe_toFinset`：coe_toFinset (s : Set α) [Fintype s] : (↑s.toFinset : 
Set α) = s
· 使用引理 `SimpleGraph.neighborSet_subset_between_union`：neighborSet_subset_between
_union (hv : v in s) : G.neighborSet v subseteq (G.between s sᶜ).neighborSet v u
nion s

--- 原说明 ---
The neighbor finset of `v ∈ s` in `G.between s sᶜ` excludes the vertices in `s` 
adjacent to `v`
in `G`.
-/
lemma neighborFinset_subset_between_union (hv : v ∈ s) :
    G.neighborFinset v ⊆ (G.between s sᶜ).neighborFinset v ∪ s := by
  simpa [neighborFinset_def] using neighborSet_subset_between_union hv

/-- The degree of `v ∈ s` in `G` is at most the degree in `G.between s sᶜ` plus the excluded
vertices from `s`. -/
/-
**SimpleGraph.degree_le_between_add** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：degree_le_between_add (hv : v in s) : G.degree v <= (G.between s sᶜ).degre
e v + s.card
参数：hv : v in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_compl`：coe_compl (s : Finset α) : ↑sᶜ = (↑s : Set α)ᶜ
· 使用定理 `SimpleGraph.between_isBipartiteWith`：between_isBipartiteWith (h : Disjoi
nt s t) : (G.between s t).IsBipartiteWith s t where disjoint
· 使用定理 `disjoint_compl_right`：disjoint_compl_right : Disjoint a aᶜ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_union_of_disjoint`：∀ {α : Type u_1} {s t : Finset α} [inst :
 DecidableEq α], Disjoint s t → (s ∪ t).card = s.card + t.card
· 使用定理 `SimpleGraph.isBipartiteWith_neighborFinset_disjoint`：isBipartiteWith_nei
ghborFinset_disjoint (h : G.IsBipartiteWith s t) (hv : v in s) : Disjoint (G.nei
ghborFinset v) s
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用引理 `SimpleGraph.neighborFinset_subset_between_union`：neighborFinset_subset_b
etween_union (hv : v in s) : G.neighborFinset v subseteq (G.between s sᶜ).neighb
orFinset v union s

--- 原说明 ---
The degree of `v ∈ s` in `G` is at most the degree in `G.between s sᶜ` plus the 
excluded
vertices from `s`.
-/
theorem degree_le_between_add (hv : v ∈ s) :
    G.degree v ≤ (G.between s sᶜ).degree v + s.card := by
  have h_bipartite : (G.between s sᶜ).IsBipartiteWith s ↑(sᶜ) := by
    simpa using between_isBipartiteWith disjoint_compl_right
  simp_rw [← card_neighborFinset_eq_degree,
    ← card_union_of_disjoint (isBipartiteWith_neighborFinset_disjoint h_bipartite hv)]
  exact card_le_card (neighborFinset_subset_between_union hv)

/-- The neighbor finset of `w ∈ sᶜ` in `G.between s sᶜ` excludes the vertices in `sᶜ` adjacent to
`w` in `G`. -/
/-
**SimpleGraph.neighborFinset_subset_between_union_compl** 是 Mathlib 中的一个引理，位于命名空
间 `SimpleGraph`。
形式化陈述：neighborFinset_subset_between_union_compl (hw : w in sᶜ) : G.neighborFinse
t w subseteq (G.between s sᶜ).neighborFinset w union sᶜ
参数：hw : w in sᶜ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_union`：coe_union (s₁ s₂ : Finset α) : ↑(s₁ union s₂) = (s₁ un
ion s₂ : Set α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.coe_toFinset`：coe_toFinset (s : Set α) [Fintype s] : (↑s.toFinset : 
Set α) = s
· 使用定理 `Finset.coe_compl`：coe_compl (s : Finset α) : ↑sᶜ = (↑s : Set α)ᶜ
· 使用引理 `SimpleGraph.neighborSet_subset_between_union_compl`：neighborSet_subset_b
etween_union_compl (hw : w in sᶜ) : G.neighborSet w subseteq (G.between s sᶜ).ne
ighborSet w union sᶜ

--- 原说明 ---
The neighbor finset of `w ∈ sᶜ` in `G.between s sᶜ` excludes the vertices in `sᶜ
` adjacent to
`w` in `G`.
-/
lemma neighborFinset_subset_between_union_compl (hw : w ∈ sᶜ) :
    G.neighborFinset w ⊆ (G.between s sᶜ).neighborFinset w ∪ sᶜ := by
  simpa [neighborFinset_def] using G.neighborSet_subset_between_union_compl (by simpa using hw)

/-- The degree of `w ∈ sᶜ` in `G` is at most the degree in `G.between s sᶜ` plus the excluded
vertices from `sᶜ`. -/
/-
**SimpleGraph.degree_le_between_add_compl** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph
`。
形式化陈述：degree_le_between_add_compl (hw : w in sᶜ) : G.degree w <= (G.between s sᶜ
).degree w + sᶜ.card
参数：hw : w in sᶜ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_compl`：coe_compl (s : Finset α) : ↑sᶜ = (↑s : Set α)ᶜ
· 使用定理 `SimpleGraph.between_isBipartiteWith`：between_isBipartiteWith (h : Disjoi
nt s t) : (G.between s t).IsBipartiteWith s t where disjoint
· 使用定理 `disjoint_compl_right`：disjoint_compl_right : Disjoint a aᶜ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_union_of_disjoint`：∀ {α : Type u_1} {s t : Finset α} [inst :
 DecidableEq α], Disjoint s t → (s ∪ t).card = s.card + t.card
· 使用定理 `SimpleGraph.isBipartiteWith_neighborFinset_disjoint'`：isBipartiteWith_ne
ighborFinset_disjoint' (h : G.IsBipartiteWith s t) (hw : w in t) : Disjoint (G.n
eighborFinset w) t
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用引理 `SimpleGraph.neighborFinset_subset_between_union_compl`：neighborFinset_su
bset_between_union_compl (hw : w in sᶜ) : G.neighborFinset w subseteq (G.between
 s sᶜ).neighborFinset w union sᶜ

--- 原说明 ---
The degree of `w ∈ sᶜ` in `G` is at most the degree in `G.between s sᶜ` plus the
 excluded
vertices from `sᶜ`.
-/
theorem degree_le_between_add_compl (hw : w ∈ sᶜ) :
    G.degree w ≤ (G.between s sᶜ).degree w + sᶜ.card := by
  have h_bipartite : (G.between s sᶜ).IsBipartiteWith s ↑(sᶜ) := by
    simpa using between_isBipartiteWith disjoint_compl_right
  simp_rw [← card_neighborFinset_eq_degree,
    ← card_union_of_disjoint (isBipartiteWith_neighborFinset_disjoint' h_bipartite hw)]
  exact card_le_card (neighborFinset_subset_between_union_compl hw)

end Between

section completeBipartiteGraph

variable {W₁ W₂ : Type*}

/-
**SimpleGraph.edgeSet_completeBipartiteGraph** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGr
aph`。
形式化陈述：edgeSet_completeBipartiteGraph : (completeBipartiteGraph W₁ W₂).edgeSet = 
.range (fun x : W₁ × W₂ => s(.inl x.1, .inr x.2))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Sym2.ind`：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y))
 → ∀ (i : Sym2 α), f i
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `completeBipartiteGraph_adj`：∀ (V : Type u_1) (W : Type u_2) (v w : V ⊕ W
),   (completeBipartiteGraph V W).Adj v w = (v.isLeft = true ∧ w.isRight = true 
∨ v.isRight = tr…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Bool.false_eq_true`：(false = true) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `Sum.inl.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : α), (Sum.inl val
 = Sum.inl val_1) = (val = val_1)
· 使用定理 `Sum.inr.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : β), (Sum.inr val
 = Sum.inr val_1) = (val = val_1)
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
-/
theorem edgeSet_completeBipartiteGraph :
    (completeBipartiteGraph W₁ W₂).edgeSet =
    .range (fun x : W₁ × W₂ ↦ s(.inl x.1, .inr x.2)) := by
  refine Set.ext <| Sym2.ind fun u v ↦ ⟨fun h ↦ ?_, fun ⟨⟨a, b⟩, z⟩ ↦ ?_⟩
  · cases u <;> cases v <;> simp_all
  · grind [completeBipartiteGraph_adj, mem_edgeSet]
/-
**SimpleGraph.encard_edgeSet_completeBipartiteGraph** 是 Mathlib 中的一个定理，位于命名空间 `S
impleGraph`。
形式化陈述：encard_edgeSet_completeBipartiteGraph : (completeBipartiteGraph W₁ W₂).edg
eSet.encard = ENat.card W₁ * ENat.card W₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.edgeSet_completeBipartiteGraph`：edgeSet_completeBipartiteGra
ph : (completeBipartiteGraph W₁ W₂).edgeSet = .range (fun x : W₁ × W₂ => s(.inl 
x.1, .inr x.2))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENat.card_prod`：card_prod (α β : Type*) : card (α × β) = card α * card β
· 使用定理 `Set.encard_univ`：∀ (α : Type u_3), Set.univ.encard = ENat.card α
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Function.Injective.encard_image`：∀ {α : Type u_1} {β : Type u_2} {f : α 
→ β}, Function.Injective f → ∀ (s : Set α), (f '' s).encard = s.encard
-/
theorem encard_edgeSet_completeBipartiteGraph :
    (completeBipartiteGraph W₁ W₂).edgeSet.encard = ENat.card W₁ * ENat.card W₂ := by
  rw [edgeSet_completeBipartiteGraph, ← ENat.card_prod, ← Set.encard_univ, ← Set.image_univ]
  exact Function.Injective.encard_image (by grind [Function.Injective]) Set.univ

/-- An embedding of the edges of a bipartite graph into the edges of the complete bipartite graph -/
/-
**SimpleGraph.IsBipartiteWith.edgeSetEmbeddingCompleteBipartiteGraph** 是 Mathlib
 中的一个定义，位于命名空间 `SimpleGraph.IsBipartiteWith`。
形式化陈述：{V : Type u_1} →   {G : SimpleGraph V} →     {s t : Set V} →       [Decida
bleRel fun x1 x2 => x1 ∈ x2] → G.IsBipartiteWith s t → ↑G.edgeSet ↪ ↑(completeBi
partiteGraph ↑s ↑t).edgeSet
参数：completeBipartiteGraph ↑s ↑t。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.symm`：∀ {V : Type u} (self : SimpleGraph V), Std.Symm self.A
dj
· 使用定理 `SimpleGraph.IsBipartiteWith.mem_of_adj`：∀ {V : Type u_1} {G : SimpleGrap
h V} {s t : Set V},   G.IsBipartiteWith s t → ∀ ⦃v w : V⦄, G.Adj v w → v ∈ s ∧ w
 ∈ t ∨ v ∈ t ∧ w ∈ s

--- 原说明 ---
An embedding of the edges of a bipartite graph into the edges of the complete bi
partite graph
-/
def IsBipartiteWith.edgeSetEmbeddingCompleteBipartiteGraph [DecidableRel (· ∈ · : V → Set V → _)]
    (hG : G.IsBipartiteWith s t) : G.edgeSet ↪ (completeBipartiteGraph s t).edgeSet where
  toFun := fun ⟨e, he⟩ ↦
    e.fromRelNdrec he (sym := G.symm) (fun u v h ↦ hG.mem_of_adj h |>.by_cases
      (fun h ↦ ⟨s(.inl ⟨u, h.left⟩, .inr ⟨v, h.right⟩), .inl ⟨rfl, rfl⟩⟩)
      (fun h ↦ ⟨s(.inl ⟨v, h.right⟩, .inr ⟨u, h.left⟩), .inl ⟨rfl, rfl⟩⟩)
    ) <| by grind [Or.by_cases, hG.disjoint]
  inj' := by
    rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩
    change (dite ..) = (dite ..) → _
    grind

end completeBipartiteGraph

section

/-- The cardinality of the edge set of a bipartite graph is upper bounded by the product
of the cardinality of the two partitions. -/
/-
**SimpleGraph.IsBipartiteWith.encard_edgeSet_le** 是 Mathlib 中的一个定理，位于命名空间 `Simpl
eGraph.IsBipartiteWith`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {s t : Set V}, G.IsBipartiteWith s t 
→ G.edgeSet.encard ≤ s.encard * t.encard
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Function.Embedding.encard_le`：∀ {α : Type u_1} {β : Type u_2} {s : Set α
} {t : Set β} (e : ↑s ↪ ↑t), s.encard ≤ t.encard
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.encard_edgeSet_completeBipartiteGraph`：encard_edgeSet_comple
teBipartiteGraph : (completeBipartiteGraph W₁ W₂).edgeSet.encard = ENat.card W₁ 
* ENat.card W₂

--- 原说明 ---
The cardinality of the edge set of a bipartite graph is upper bounded by the pro
duct
of the cardinality of the two partitions.
-/
theorem IsBipartiteWith.encard_edgeSet_le (hG : G.IsBipartiteWith s t) :
    G.edgeSet.encard ≤ s.encard * t.encard := by
  classical
  grw [hG.edgeSetEmbeddingCompleteBipartiteGraph.encard_le]
  simp [encard_edgeSet_completeBipartiteGraph]
/-
**SimpleGraph.IsBipartite.four_mul_encard_edgeSet_le** 是 Mathlib 中的一个定理，位于命名空间 `
SimpleGraph.IsBipartite`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V}, G.IsBipartite → 4 * G.edgeSet.encard
 ≤ ENat.card V ^ 2
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `finite_or_infinite`：finite_or_infinite (α : Sort*) : Finite α ∨ Infinite
 α
· 使用定理 `SimpleGraph.IsBipartite.exists_isBipartiteWith`：∀ {V : Type u_1} {G : Si
mpleGraph V}, G.IsBipartite → ∃ s t, G.IsBipartiteWith s t
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `CanonicallyOrderedAdd.toMulLeftMono`：∀ {R : Type u} [inst : NonUnitalNon
AssocSemiring R] [inst_1 : LE R] [CanonicallyOrderedAdd R], MulLeftMono R
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `SimpleGraph.IsBipartiteWith.encard_edgeSet_le`：∀ {V : Type u_1} {G : Sim
pleGraph V} {s t : Set V}, G.IsBipartiteWith s t → G.edgeSet.encard ≤ s.encard *
 t.encard
· 使用定理 `Set.encard_le_card`：encard_le_card : s.encard <= ENat.card α
· 使用定理 `Set.encard_union_eq`：encard_union_eq (h : Disjoint s t) : (s union t).en
card = s.encard + t.encard
· 使用定理 `SimpleGraph.IsBipartiteWith.disjoint`：∀ {V : Type u_1} {G : SimpleGraph 
V} {s t : Set V}, G.IsBipartiteWith s t → Disjoint s t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENat.card_eq_coe_natCard`：card_eq_coe_natCard (α : Type*) [Finite α] : c
ard α = Nat.card α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Finite.cast_ncard_eq`：∀ {α : Type u_1} {s : Set α}, s.Finite → ↑s.nc
ard = s.encard
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ENat.card_eq_top_of_infinite`：card_eq_top_of_infinite [Infinite α] : car
d α = ⊤
· 使用定理 `ENat.top_pow`：∀ {n : ℕ}, n ≠ 0 → ⊤ ^ n = ⊤
（共 31 条，此处仅展示前 30 条）
-/
theorem IsBipartite.four_mul_encard_edgeSet_le (h : G.IsBipartite) :
    4 * G.edgeSet.encard ≤ ENat.card V ^ 2 := by
  refine finite_or_infinite V |>.elim (fun hv ↦ ?_) (fun _ ↦ by simp)
  have ⟨s, t, h⟩ := h.exists_isBipartiteWith
  grw [h.encard_edgeSet_le]
  have := Set.encard_union_eq h.disjoint ▸ Set.encard_le_card
  rw [ENat.card_eq_coe_natCard, ← s.toFinite.cast_ncard_eq, ← t.toFinite.cast_ncard_eq] at this ⊢
  norm_cast at this ⊢
  grind [Nat.pow_le_pow_left this 2, four_mul_le_sq_add s.ncard t.ncard]

end

section BipartiteDoubleCover

/-- `bipartiteDoubleCover G` has two vertices `inl v` and `inr v` for each vertex `v` in `G`
such that `inl v` (`inr v`) is adjacent to `inr w` (`inl w`) iff `v` is adjacent to `w` in `G`. -/
/-
**SimpleGraph.bipartiteDoubleCover** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：{V : Type u_1} → SimpleGraph V → SimpleGraph (V ⊕ V)
参数：V ⊕ V。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`bipartiteDoubleCover G` has two vertices `inl v` and `inr v` for each vertex `v
` in `G`
such that `inl v` (`inr v`) is adjacent to `inr w` (`inl w`) iff `v` is adjacent
 to `w` in `G`.
-/
@[simp] def bipartiteDoubleCover (G : SimpleGraph V) : SimpleGraph (V ⊕ V) where
  Adj
  | .inl v', .inr w' | .inr v', .inl w' => G.Adj v' w'
  | _, _ => False
  symm.symm _ _ := by grind [adj_symm]
/-
**SimpleGraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [h : DecidableRel G.Adj] : DecidableRel G.bipartiteDoubleCover.Adj
  | .inl _, .inr _ | .inr _, .inl _ => h _ _
  | .inl _, .inl _ | .inr _, .inr _ => inferInstanceAs (Decidable False)

/-- The bipartite double cover of `G` is contained in the corresponding complete bipartite graph,
that is, the bipartite double cover of `G` is bipartite. -/
/-
**SimpleGraph.bipartiteDoubleCover_le** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：bipartiteDoubleCover_le : G.bipartiteDoubleCover <= completeBipartiteGraph
 V V
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `completeBipartiteGraph_adj`：∀ (V : Type u_1) (W : Type u_2) (v w : V ⊕ W
),   (completeBipartiteGraph V W).Adj v w = (v.isLeft = true ∧ w.isRight = true 
∨ v.isRight = tr…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Bool.false_eq_true`：(false = true) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True

--- 原说明 ---
The bipartite double cover of `G` is contained in the corresponding complete bip
artite graph,
that is, the bipartite double cover of `G` is bipartite.
-/
theorem bipartiteDoubleCover_le : G.bipartiteDoubleCover ≤ completeBipartiteGraph V V :=
  fun v w hadj ↦ match v, w with
  | .inl _, .inr _ | .inr _, .inl _ => by simp
  | .inl _, .inl _ | .inr _, .inr _ => by simp at hadj

set_option backward.isDefEq.respectTransparency.types false in
/-- The bipartite double cover of `G` has twice the number of edges as `G`. -/
/-
**SimpleGraph.card_edgeFinset_bipartiteDoubleCover** 是 Mathlib 中的一个定理，位于命名空间 `Si
mpleGraph`。
形式化陈述：card_edgeFinset_bipartiteDoubleCover [Fintype V] [DecidableRel G.Adj] : #G
.bipartiteDoubleCover.edgeFinset = 2 * #G.edgeFinset
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.two_mul_card_edgeFinset`：two_mul_card_edgeFinset : 2 * #G.ed
geFinset = #(univ.filter fun (x, y) => G.Adj x y)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用引理 `Finset.card_bij`：card_bij (i : forall a in s, β) (hi : forall a ha, i a 
ha in t) (i_inj : forall a₁ ha₁ a₂ ha₂, i a₁ ha₁ = i a₂ ha₂ -> a₁ = a₂) (i_surj 
: for…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Sym2.ind`：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y))
 → ∀ (i : Sym2 α), f i
· 使用定理 `SimpleGraph.mem_edgeSet`：mem_edgeSet : s(v, w) in G.edgeSet ↔ G.Adj v w
· 使用定理 `SimpleGraph.mem_edgeFinset`：mem_edgeFinset : e in G.edgeFinset ↔ e in G.
edgeSet
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `Sum.inl.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : α), (Sum.inl val
 = Sum.inl val_1) = (val = val_1)
· 使用定理 `Sum.inr.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : β), (Sum.inr val
 = Sum.inr val_1) = (val = val_1)
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `SimpleGraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Ad
j u v → G.Adj v u

--- 原说明 ---
The bipartite double cover of `G` has twice the number of edges as `G`.
-/
theorem card_edgeFinset_bipartiteDoubleCover [Fintype V] [DecidableRel G.Adj] :
    #G.bipartiteDoubleCover.edgeFinset = 2 * #G.edgeFinset := by
  rw [two_mul_card_edgeFinset, eq_comm]
  apply card_bij (fun (v, w) _ ↦ s(.inl v, .inr w))
    (fun _ h ↦ by simpa using h) (by grind) (fun e he ↦ ?_)
  induction e with | _ v w
  rw [mem_edgeFinset, mem_edgeSet] at he
  match v, w with
  | .inl _, .inr _ => simpa using he
  | .inr _, .inl _ => simpa using he.symm
  | .inl _, .inl _ | .inr _, .inr _ => simp at he

/-- If the double cover of `G` contains `completeBipartiteGraph α β`, then `G` also
contains `completeBipartiteGraph α β`. -/
/-
**SimpleGraph.completeBipartiteGraph_isContained_bipartiteDoubleCover** 是 Mathli
b 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：completeBipartiteGraph_isContained_bipartiteDoubleCover {α β : Type*} [Fin
ite α] [Finite β] [Nonempty α] [Nonempty β] : completeBipartiteGraph α β ⊑ G.bip
artiteDoubleCover ↔ completeBipartiteGraph α β ⊑ G
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.card_pos`：∀ {α : Type u_1} {s : Finset α}, 0 < s.card ↔ s.Nonempt
y
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Fintype.card_pos`：card_pos [h : Nonempty α] : 0 < card α
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Bool.false_eq_true`：(false = true) = False
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用引理 `Finset.card_bij`：card_bij (i : forall a in s, β) (hi : forall a ha, i a 
ha in t) (i_inj : forall a₁ ha₁ a₂ ha₂, i a₁ ha₁ = i a₂ ha₂ -> a₁ = a₂) (i_surj 
: for…
· 使用定理 `Sum.inl.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : α), (Sum.inl val
 = Sum.inl val_1) = (val = val_1)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Sum.isLeft_inl`：∀ {α : Type u_1} {β : Type u_2} {x : α}, (Sum.inl x).isL
eft = true
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Sum.inl_getLeft`：∀ {α : Type u_1} {β : Type u_2} (x : α ⊕ β) (h : x.isLe
ft = true), Sum.inl (x.getLeft h) = x
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Sum.inr.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : β), (Sum.inr val
 = Sum.inr val_1) = (val = val_1)
（共 39 条，此处仅展示前 30 条）

--- 原说明 ---
If the double cover of `G` contains `completeBipartiteGraph α β`, then `G` also
contains `completeBipartiteGraph α β`.
-/
theorem completeBipartiteGraph_isContained_bipartiteDoubleCover
    {α β : Type*} [Finite α] [Finite β] [Nonempty α] [Nonempty β] :
    completeBipartiteGraph α β ⊑ G.bipartiteDoubleCover ↔ completeBipartiteGraph α β ⊑ G := by
  have : Fintype α := .ofFinite α
  have : Fintype β := .ofFinite β
  simp_rw [completeBipartiteGraph_isContained_iff]
  refine ⟨fun ⟨left, right, card_left, card_right, h⟩ ↦ ?_,
    fun ⟨left, right, card_left, card_right, h⟩ ↦ ?_⟩
  · simp_rw [← card_left, ← card_right]
    obtain ⟨l, hl⟩ : left.Nonempty := card_pos.mp <| card_pos.trans_le card_left.ge
    obtain ⟨r, hr⟩ : right.Nonempty := card_pos.mp <| card_pos.trans_le card_right.ge
    have hmem_left {l'} (hl' : l' ∈ left) :
        (l.isLeft → l'.isLeft) ∧ (l.isRight → l'.isRight) := by
      rcases l with l | l <;> rcases r with r | r <;> rcases l' with l' | l'
      all_goals solve | simp | simpa using h hl hr | simpa using h hl' hr
    have hmem_right {r'} (hr' : r' ∈ right) :
        (r.isLeft → r'.isLeft) ∧ (r.isRight → r'.isRight) := by
      rcases l with l | l <;> rcases r with r | r <;> rcases r' with r' | r'
      all_goals solve | simp | simpa using h hl hr | simpa using h hl hr'
    rcases l with l | l <;> rcases r with r | r
    · simpa using h hl hr
    · refine ⟨left.toLeft, right.toRight, ?_, ?_, fun i hi j hj ↦ ?_⟩
      · exact card_bij (fun i _ ↦ .inl i) (fun i hi ↦ by simpa using hi) (fun i hi j hj ↦ by simp)
          (fun i hi ↦ ⟨i.getLeft <| (hmem_left hi).left Sum.isLeft_inl, by simp [hi]⟩)
      · exact card_bij (fun j hj ↦ .inr j) (fun j hj ↦ by simpa using hj) (fun i hi j hj ↦ by simp)
          (fun j hj ↦ ⟨j.getRight <| (hmem_right hj).right Sum.isRight_inr, by simp [hj]⟩)
      · rw [mem_coe, mem_toLeft] at hi
        rw [mem_coe, mem_toRight] at hj
        simpa using h hi hj
    · refine ⟨left.toRight, right.toLeft, ?_, ?_, fun i hi j hj ↦ ?_⟩
      · exact card_bij (fun i _ ↦ .inr i) (fun i hi ↦ by simpa using hi) (fun i hi j hj ↦ by simp)
          (fun i hi ↦ ⟨i.getRight <| (hmem_left hi).right Sum.isRight_inr, by simp [hi]⟩)
      · exact card_bij (fun j hj ↦ .inl j) (fun j hj ↦ by simpa using hj) (fun i hi j hj ↦ by simp)
          (fun j hj ↦ ⟨j.getLeft <| (hmem_right hj).left Sum.isLeft_inl, by simp [hj]⟩)
      · rw [mem_coe, mem_toRight] at hi
        rw [mem_coe, mem_toLeft] at hj
        simpa using h hi hj
    · simpa using h hl hr
  · simp_rw [← card_left, ← card_right]
    refine ⟨left.map .inl, right.map .inr, card_map _, card_map _, fun i hi j hj ↦ ?_⟩
    simp_rw [mem_coe, mem_map, Function.Embedding.inl_apply,
      Function.Embedding.inr_apply] at hi hj
    obtain ⟨i', hi', hi⟩ := hi
    obtain ⟨j', hj', hj⟩ := hj
    simpa [← hi, ← hj] using h hi' hj'
/-
**SimpleGraph.isBipartiteWith_bipartiteDoubleCover** 是 Mathlib 中的一个定理，位于命名空间 `Si
mpleGraph`。
形式化陈述：isBipartiteWith_bipartiteDoubleCover : G.bipartiteDoubleCover.IsBipartiteW
ith {v | v.isLeft} {w | w.isRight} where disjoint
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bool.false_eq_true`：(false = true) = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Sum.inr.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : β), (Sum.inr val
 = Sum.inr val_1) = (val = val_1)
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
-/
theorem isBipartiteWith_bipartiteDoubleCover :
    G.bipartiteDoubleCover.IsBipartiteWith {v | v.isLeft} {w | w.isRight} where
  disjoint := by simp [Set.disjoint_iff_forall_ne]
  mem_of_adj := by simp
/-
**SimpleGraph.isBipartite_bipartiteDoubleCover** 是 Mathlib 中的一个定理，位于命名空间 `Simple
Graph`。
形式化陈述：isBipartite_bipartiteDoubleCover : G.bipartiteDoubleCover.IsBipartite
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsBipartiteWith.isBipartite`：∀ {V : Type u_1} {G : SimpleGra
ph V} {s t : Set V}, G.IsBipartiteWith s t → G.IsBipartite
· 使用定理 `SimpleGraph.isBipartiteWith_bipartiteDoubleCover`：isBipartiteWith_bipart
iteDoubleCover : G.bipartiteDoubleCover.IsBipartiteWith {v | v.isLeft} {w | w.is
Right} where disjoint
-/
theorem isBipartite_bipartiteDoubleCover : G.bipartiteDoubleCover.IsBipartite :=
  isBipartiteWith_bipartiteDoubleCover.isBipartite

end BipartiteDoubleCover

end SimpleGraph

