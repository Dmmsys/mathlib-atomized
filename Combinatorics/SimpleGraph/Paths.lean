/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
public import Mathlib.Combinatorics.SimpleGraph.Walk.Subwalks
public import Mathlib.Order.Preorder.Finite

/-!

# Trail, Path, and Cycle

In a simple graph,

* A *trail* is a walk whose edges each appear no more than once.

* A *circuit* is a nonempty trail whose first and last vertices are the
  same.

* A *path* is a trail whose vertices appear no more than once.

* A *cycle* is a nonempty trail whose first and last vertices are the
  same and whose vertices except for the first appear no more than once.

**Warning:** graph theorists mean something different by "path" than
do homotopy theorists. A "walk" in graph theory is a "path" in
homotopy theory. Another warning: some graph theorists use "path" and
"simple path" for "walk" and "path."

Some definitions and theorems have inspiration from multigraph
counterparts in [Chou1994].

## Main definitions

* `SimpleGraph.Walk.IsTrail`, `SimpleGraph.Walk.IsPath`, and `SimpleGraph.Walk.IsCycle`.

* `SimpleGraph.Path`

* `SimpleGraph.Path.map` for the induced map on paths,
  given an (injective) graph homomorphism.

## Tags
trails, paths, circuits, cycles
-/

@[expose] public section

open Function

universe u v w

namespace SimpleGraph

variable {V : Type u} {V' : Type v}
variable (G : SimpleGraph V) (G' : SimpleGraph V')

namespace Walk

variable {G G'} {u u' v w : V} {p : G.Walk u v} {f : G ->g G'}

/-! ### Trails, paths, circuits, cycles -/

/-- A *trail* is a walk with no repeating edges. -/
@[mk_iff isTrail_def]
/--
Definition of `IsTrail` / `IsTrail` 的定义

English:
structure IsTrail
  parameters: {u v : V} (p : G.Walk u v)
  axioms and operations (1):
    - edges_nodup : p.edges.Nodup

中文:
结构 是Trail
  参数: {u v : V} (p : G.途径 u v)
  公理与运算 (1 个):
    - edges_nodup : p.edges.Nodup
-/
structure IsTrail {u v : V} (p : G.Walk u v) : Prop where
  edges_nodup : p.edges.Nodup

/--
Definition of `IsPath` / `IsPath` 的定义

English:
structure IsPath
  parameters: {u v : V} (p : G.Walk u v)
  extends: isTrail : IsTrail p
  axioms and operations (1):
    - support_nodup : p.support.Nodup

中文:
结构 是道路
  参数: {u v : V} (p : G.途径 u v)
  继承: isTrail : 是Trail p
  公理与运算 (1 个):
    - support_nodup : p.support.Nodup
-/
structure IsPath {u v : V} (p : G.Walk u v) : Prop extends isTrail : IsTrail p where
  support_nodup : p.support.Nodup

/-- A *circuit* at `u : V` is a nonempty trail beginning and ending at `u`. -/
@[mk_iff isCircuit_def]
/--
Definition of `IsCircuit` / `IsCircuit` 的定义

English:
structure IsCircuit
  parameters: {u : V} (p : G.Walk u u)
  extends: isTrail : IsTrail p
  axioms and operations (1):
    - ne_nil : p != nil

中文:
结构 是Circuit
  参数: {u : V} (p : G.途径 u u)
  继承: isTrail : 是Trail p
  公理与运算 (1 个):
    - ne_nil : p != nil
-/
structure IsCircuit {u : V} (p : G.Walk u u) : Prop extends isTrail : IsTrail p where
  ne_nil : p != nil

/--
Definition of `IsCycle` / `IsCycle` 的定义

English:
structure IsCycle
  parameters: {u : V} (p : G.Walk u u)
  extends: isCircuit : IsCircuit p
  axioms and operations (1):
    - support_nodup : p.support.tail.Nodup

中文:
结构 是环
  参数: {u : V} (p : G.途径 u u)
  继承: isCircuit : 是Circuit p
  公理与运算 (1 个):
    - support_nodup : p.support.tail.Nodup
-/
structure IsCycle {u : V} (p : G.Walk u u) : Prop extends isCircuit : IsCircuit p where
  support_nodup : p.support.tail.Nodup

@[simp]
/--
theorem `isTrail_copy` / 定理 `isTrail_copy`

English:
theorem isTrail_copy
  given: {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v')
  proof: by
  subst_vars
  rfl

中文:
定理 isTrail_copy
  条件: {u v u' v'} (p : G.途径 u v) (hu : u = u') (hv : v = v')
  证明: by
  subst_vars
  rfl
-/
theorem isTrail_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).IsTrail ↔ p.IsTrail := by
  subst_vars
  rfl

/--
theorem `IsPath.mk'` / 定理 `IsPath.mk'`

English:
theorem IsPath.mk'
  given: {u v : V} {p : G.Walk u v} (h : p.support.Nodup)
  statement: p.IsPath
  proof: ⟨⟨edges_nodup_of_support_nodup h⟩, h⟩

中文:
定理 是道路.mk'
  条件: {u v : V} {p : G.途径 u v} (h : p.support.Nodup)
  结论: p.是道路
  证明: ⟨⟨edges_nodup_of_support_nodup h⟩, h⟩

Depends on / 依赖: edges_nodup_of_support_nodup
-/
theorem IsPath.mk' {u v : V} {p : G.Walk u v} (h : p.support.Nodup) : p.IsPath :=
  ⟨⟨edges_nodup_of_support_nodup h⟩, h⟩

/--
theorem `isPath_def` / 定理 `isPath_def`

English:
theorem isPath_def
  given: {u v : V} (p : G.Walk u v)
  statement: p.IsPath ↔ p.support.Nodup
  proof: ⟨IsPath.support_nodup, IsPath.mk'⟩

中文:
定理 isPath_def
  条件: {u v : V} (p : G.途径 u v)
  结论: p.是道路 ↔ p.support.Nodup
  证明: ⟨IsPath.support_nodup, IsPath.mk'⟩

Depends on / 依赖: IsPath, IsPath.mk, IsPath.support_nodup, support_nodup
-/
theorem isPath_def {u v : V} (p : G.Walk u v) : p.IsPath ↔ p.support.Nodup :=
  ⟨IsPath.support_nodup, IsPath.mk'⟩

/--
theorem `isPath_iff_injective_get_support` / 定理 `isPath_iff_injective_get_support`

English:
theorem isPath_iff_injective_get_support
  given: {u v : V} (p : G.Walk u v)
  proof: p.isPath_def.trans List.nodup_iff_injective_get

@[simp]

中文:
定理 isPath_iff_injective_get_support
  条件: {u v : V} (p : G.途径 u v)
  证明: p.isPath_def.trans List.nodup_iff_injective_get

@[simp]

Depends on / 依赖: List.nodup_iff_injective_get, isPath_def, nodup_iff_injective_get, p.isPath_def.trans
-/
theorem isPath_iff_injective_get_support {u v : V} (p : G.Walk u v) :
    p.IsPath ↔ (p.support.get ·).Injective :=
  p.isPath_def.trans List.nodup_iff_injective_get

@[simp]
/--
theorem `isPath_copy` / 定理 `isPath_copy`

English:
theorem isPath_copy
  given: {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v')
  proof: by
  subst_vars
  rfl

@[simp]

中文:
定理 isPath_copy
  条件: {u v u' v'} (p : G.途径 u v) (hu : u = u') (hv : v = v')
  证明: by
  subst_vars
  rfl

@[simp]
-/
theorem isPath_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).IsPath ↔ p.IsPath := by
  subst_vars
  rfl

@[simp]
/--
theorem `isCircuit_copy` / 定理 `isCircuit_copy`

English:
theorem isCircuit_copy
  given: {u u'} (p : G.Walk u u) (hu : u = u')
  proof: by
  subst_vars
  rfl

中文:
定理 isCircuit_copy
  条件: {u u'} (p : G.途径 u u) (hu : u = u')
  证明: by
  subst_vars
  rfl
-/
theorem isCircuit_copy {u u'} (p : G.Walk u u) (hu : u = u') :
    (p.copy hu hu).IsCircuit ↔ p.IsCircuit := by
  subst_vars
  rfl

/--
lemma `IsCircuit.not_nil` / 引理 `IsCircuit.not_nil`

English:
lemma IsCircuit.not_nil
  given: {p : G.Walk v v} (hp : IsCircuit p)
  statement: ¬ p.Nil
  proof: (hp.ne_nil ·.eq_nil)

中文:
引理 是Circuit.not_nil
  条件: {p : G.途径 v v} (hp : 是Circuit p)
  结论: ¬ p.Nil
  证明: (hp.ne_nil ·.eq_nil)

Depends on / 依赖: eq_nil, hp.ne_nil, ne_nil
-/
lemma IsCircuit.not_nil {p : G.Walk v v} (hp : IsCircuit p) : ¬ p.Nil := (hp.ne_nil ·.eq_nil)

/--
theorem `isCycle_def` / 定理 `isCycle_def`

English:
theorem isCycle_def
  given: {u : V} (p : G.Walk u u)
  proof: Iff.intro (fun h => ⟨h.1.1, h.1.2, h.2⟩) fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩

@[simp]

中文:
定理 isCycle_def
  条件: {u : V} (p : G.途径 u u)
  证明: Iff.intro (fun h => ⟨h.1.1, h.1.2, h.2⟩) fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩

@[simp]

Depends on / 依赖: Iff.intro
-/
theorem isCycle_def {u : V} (p : G.Walk u u) :
    p.IsCycle ↔ p.IsTrail ∧ p != nil ∧ p.support.tail.Nodup :=
  Iff.intro (fun h => ⟨h.1.1, h.1.2, h.2⟩) fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩

@[simp]
/--
theorem `isCycle_copy` / 定理 `isCycle_copy`

English:
theorem isCycle_copy
  given: {u u'} (p : G.Walk u u) (hu : u = u')
  proof: by
  subst_vars
  rfl

中文:
定理 isCycle_copy
  条件: {u u'} (p : G.途径 u u) (hu : u = u')
  证明: by
  subst_vars
  rfl
-/
theorem isCycle_copy {u u'} (p : G.Walk u u) (hu : u = u') :
    (p.copy hu hu).IsCycle ↔ p.IsCycle := by
  subst_vars
  rfl

/--
lemma `IsCycle.not_nil` / 引理 `IsCycle.not_nil`

English:
lemma IsCycle.not_nil
  given: {p : G.Walk v v} (hp : IsCycle p)
  statement: ¬ p.Nil
  proof: (hp.ne_nil ·.eq_nil)

@[simp]

中文:
引理 是环.not_nil
  条件: {p : G.途径 v v} (hp : 是环 p)
  结论: ¬ p.Nil
  证明: (hp.ne_nil ·.eq_nil)

@[simp]

Depends on / 依赖: eq_nil, hp.ne_nil, ne_nil
-/
lemma IsCycle.not_nil {p : G.Walk v v} (hp : IsCycle p) : ¬ p.Nil := (hp.ne_nil ·.eq_nil)

@[simp]
/--
theorem `IsTrail.nil` / 定理 `IsTrail.nil`

English:
theorem IsTrail.nil
  given: {u : V}
  statement: (nil : G.Walk u u).IsTrail
  proof: ⟨by simp [edges]⟩

中文:
定理 是Trail.nil
  条件: {u : V}
  结论: (nil : G.途径 u u).是Trail
  证明: ⟨by simp [edges]⟩
-/
theorem IsTrail.nil {u : V} : (nil : G.Walk u u).IsTrail :=
  ⟨by simp [edges]⟩

/--
theorem `IsTrail.of_cons` / 定理 `IsTrail.of_cons`

English:
theorem IsTrail.of_cons
  given: {u v w : V} {h : G.Adj u v} {p : G.Walk v w}
  proof: by simp [isTrail_def]

@[simp]

中文:
定理 是Trail.of_cons
  条件: {u v w : V} {h : G.伴随 u v} {p : G.途径 v w}
  证明: by simp [isTrail_def]

@[simp]

Depends on / 依赖: isTrail_def
-/
theorem IsTrail.of_cons {u v w : V} {h : G.Adj u v} {p : G.Walk v w} :
    (cons h p).IsTrail -> p.IsTrail := by simp [isTrail_def]

@[simp]
/--
theorem `isTrail_cons` / 定理 `isTrail_cons`

English:
theorem isTrail_cons
  given: {u v w : V} (h : G.Adj u v) (p : G.Walk v w)
  proof: by simp [isTrail_def, and_comm]

中文:
定理 isTrail_cons
  条件: {u v w : V} (h : G.伴随 u v) (p : G.途径 v w)
  证明: by simp [isTrail_def, and_comm]

Depends on / 依赖: and_comm, isTrail_def
-/
theorem isTrail_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (cons h p).IsTrail ↔ p.IsTrail ∧ s(u, v) ∉ p.edges := by simp [isTrail_def, and_comm]

/--
lemma `IsTrail.cons` / 引理 `IsTrail.cons`

English:
lemma IsTrail.cons
  statement: {w : G.Walk u' v} (hw : w.IsTrail) (hu : G.Adj u u')
  proof: by simp [*]

中文:
引理 是Trail.cons
  结论: {w : G.途径 u' v} (hw : w.是Trail) (hu : G.伴随 u u')
  证明: by simp [*]
-/
protected lemma IsTrail.cons {w : G.Walk u' v} (hw : w.IsTrail) (hu : G.Adj u u')
    (hu' : s(u, u') ∉ w.edges) : (w.cons hu).IsTrail := by simp [*]

/--
theorem `IsTrail.reverse` / 定理 `IsTrail.reverse`

English:
theorem IsTrail.reverse
  given: {u v : V} (p : G.Walk u v) (h : p.IsTrail)
  statement: p.reverse.IsTrail
  proof: by
  simpa [isTrail_def] using h

@[simp]

中文:
定理 是Trail.reverse
  条件: {u v : V} (p : G.途径 u v) (h : p.是Trail)
  结论: p.reverse.是Trail
  证明: by
  simpa [isTrail_def] using h

@[simp]

Depends on / 依赖: isTrail_def
-/
theorem IsTrail.reverse {u v : V} (p : G.Walk u v) (h : p.IsTrail) : p.reverse.IsTrail := by
  simpa [isTrail_def] using h

@[simp]
/--
theorem `reverse_isTrail_iff` / 定理 `reverse_isTrail_iff`

English:
theorem reverse_isTrail_iff
  given: {u v : V} (p : G.Walk u v)
  statement: p.reverse.IsTrail ↔ p.IsTrail
  proof: by
  constructor <;>
    · intro h
      convert! h.reverse _
      try rw [reverse_reverse]

@[simp]

中文:
定理 reverse_isTrail_iff
  条件: {u v : V} (p : G.途径 u v)
  结论: p.reverse.是Trail ↔ p.是Trail
  证明: by
  constructor <;>
    · intro h
      convert! h.reverse _
      try rw [reverse_reverse]

@[simp]

Depends on / 依赖: convert, h.reverse, reverse, reverse_reverse
-/
theorem reverse_isTrail_iff {u v : V} (p : G.Walk u v) : p.reverse.IsTrail ↔ p.IsTrail := by
  constructor <;>
    · intro h
      convert! h.reverse _
      try rw [reverse_reverse]

@[simp]
/--
theorem `isTrail_append` / 定理 `isTrail_append`

English:
theorem isTrail_append
  given: {u v w : V} (p : G.Walk u v) (q : G.Walk v w)
  proof: by
  simp [Walk.isTrail_def, List.nodup_append']

中文:
定理 isTrail_append
  条件: {u v w : V} (p : G.途径 u v) (q : G.途径 v w)
  证明: by
  simp [Walk.isTrail_def, List.nodup_append']

Depends on / 依赖: List.nodup_append, Walk.isTrail_def, isTrail_def, nodup_append
-/
theorem isTrail_append {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    (p.append q).IsTrail ↔ p.IsTrail ∧ q.IsTrail ∧ p.edges.Disjoint q.edges := by
  simp [Walk.isTrail_def, List.nodup_append']

/--
theorem `IsTrail.of_append_left` / 定理 `IsTrail.of_append_left`

English:
theorem IsTrail.of_append_left
  statement: {u v w : V} {p : G.Walk u v} {q : G.Walk v w}
  proof: by
  simp_all

中文:
定理 是Trail.of_append_left
  结论: {u v w : V} {p : G.途径 u v} {q : G.途径 v w}
  证明: by
  simp_all
-/
theorem IsTrail.of_append_left {u v w : V} {p : G.Walk u v} {q : G.Walk v w}
    (h : (p.append q).IsTrail) : p.IsTrail := by
  simp_all

/--
theorem `IsTrail.of_append_right` / 定理 `IsTrail.of_append_right`

English:
theorem IsTrail.of_append_right
  statement: {u v w : V} {p : G.Walk u v} {q : G.Walk v w}
  proof: by
  simp_all

中文:
定理 是Trail.of_append_right
  结论: {u v w : V} {p : G.途径 u v} {q : G.途径 v w}
  证明: by
  simp_all
-/
theorem IsTrail.of_append_right {u v w : V} {p : G.Walk u v} {q : G.Walk v w}
    (h : (p.append q).IsTrail) : q.IsTrail := by
  simp_all

/--
theorem `IsTrail.count_edges_le_one` / 定理 `IsTrail.count_edges_le_one`

English:
theorem IsTrail.count_edges_le_one
  statement: [DecidableEq V] {u v : V} {p : G.Walk u v} (h : p.IsTrail)
  proof: List.nodup_iff_count_le_one.mp h.edges_nodup e

中文:
定理 是Trail.count_edges_le_one
  结论: [DecidableEq V] {u v : V} {p : G.途径 u v} (h : p.是Trail)
  证明: List.nodup_iff_count_le_one.mp h.edges_nodup e

Depends on / 依赖: List.nodup_iff_count_le_one.mp, edges_nodup, h.edges_nodup, nodup_iff_count_le_one
-/
theorem IsTrail.count_edges_le_one [DecidableEq V] {u v : V} {p : G.Walk u v} (h : p.IsTrail)
    (e : Sym2 V) : p.edges.count e <= 1 :=
  List.nodup_iff_count_le_one.mp h.edges_nodup e

/--
theorem `IsTrail.count_edges_eq_one` / 定理 `IsTrail.count_edges_eq_one`

English:
theorem IsTrail.count_edges_eq_one
  statement: [DecidableEq V] {u v : V} {p : G.Walk u v} (h : p.IsTrail)
  proof: List.count_eq_one_of_mem h.edges_nodup he

中文:
定理 是Trail.count_edges_eq_one
  结论: [DecidableEq V] {u v : V} {p : G.途径 u v} (h : p.是Trail)
  证明: List.count_eq_one_of_mem h.edges_nodup he

Depends on / 依赖: List.count_eq_one_of_mem, count_eq_one_of_mem, edges_nodup, h.edges_nodup
-/
theorem IsTrail.count_edges_eq_one [DecidableEq V] {u v : V} {p : G.Walk u v} (h : p.IsTrail)
    {e : Sym2 V} (he : e in p.edges) : p.edges.count e = 1 :=
  List.count_eq_one_of_mem h.edges_nodup he

/--
theorem `IsTrail.length_le_card_edgeFinset` / 定理 `IsTrail.length_le_card_edgeFinset`

English:
theorem IsTrail.length_le_card_edgeFinset
  statement: [Fintype G.edgeSet] {u v : V}
  proof: by
  classical
  let edges := w.edges.toFinset
  have : edges.card = w.length := length_edges _ ▸ List.toFinset_card_of_nodup h.edges_nodup
  rw [← this]
  have : edges subseteq G.edgeFinset := by
    intro e h
    refine mem_edgeFinset.mpr ?_
    apply w.edges_subset_edgeSet
    simpa [edges] using

中文:
定理 是Trail.length_le_card_edgeFinset
  结论: [有限类型 G.edgeSet] {u v : V}
  证明: by
  classical
  let edges := w.edges.toFinset
  have : edges.card = w.length := length_edges _ ▸ List.toFinset_card_of_nodup h.edges_nodup
  rw [← this]
  have : edges subseteq G.edgeFinset := by
    intro e h
    refine mem_edgeFinset.mpr ?_
    apply w.edges_subset_edgeSet
    simpa [edges] using

Depends on / 依赖: Finset, Finset.card_le_card, G.edgeFinset, List.toFinset_card_of_nodup, card_le_card, classical, edgeFinset, edges.card, edges_nodup, edges_subset_edgeSet, h.edges_nodup, length, length_edges, mem_edgeFinset, mem_edgeFinset.mpr, subseteq, toFinset, toFinset_card_of_nodup, w.edges.toFinset, w.edges_subset_edgeSet
-/
theorem IsTrail.length_le_card_edgeFinset [Fintype G.edgeSet] {u v : V}
    {w : G.Walk u v} (h : w.IsTrail) : w.length <= G.edgeFinset.card := by
  classical
  let edges := w.edges.toFinset
  have : edges.card = w.length := length_edges _ ▸ List.toFinset_card_of_nodup h.edges_nodup
  rw [← this]
  have : edges subseteq G.edgeFinset := by
    intro e h
    refine mem_edgeFinset.mpr ?_
    apply w.edges_subset_edgeSet
    simpa [edges] using h
  exact Finset.card_le_card this

/--
theorem `IsPath.nil` / 定理 `IsPath.nil`

English:
theorem IsPath.nil
  given: {u : V}
  statement: (nil : G.Walk u u).IsPath
  proof: by constructor <;> simp

中文:
定理 是道路.nil
  条件: {u : V}
  结论: (nil : G.途径 u u).是道路
  证明: by constructor <;> simp
-/
theorem IsPath.nil {u : V} : (nil : G.Walk u u).IsPath := by constructor <;> simp

/--
theorem `IsPath.of_cons` / 定理 `IsPath.of_cons`

English:
theorem IsPath.of_cons
  given: {u v w : V} {h : G.Adj u v} {p : G.Walk v w}
  proof: by simp [isPath_def]

@[simp]

中文:
定理 是道路.of_cons
  条件: {u v w : V} {h : G.伴随 u v} {p : G.途径 v w}
  证明: by simp [isPath_def]

@[simp]

Depends on / 依赖: isPath_def
-/
theorem IsPath.of_cons {u v w : V} {h : G.Adj u v} {p : G.Walk v w} :
    (cons h p).IsPath -> p.IsPath := by simp [isPath_def]

@[simp]
/--
theorem `cons_isPath_iff` / 定理 `cons_isPath_iff`

English:
theorem cons_isPath_iff
  given: {u v w : V} (h : G.Adj u v) (p : G.Walk v w)
  proof: by
  constructor <;> simp +contextual [isPath_def]

中文:
定理 cons_isPath_iff
  条件: {u v w : V} (h : G.伴随 u v) (p : G.途径 v w)
  证明: by
  constructor <;> simp +contextual [isPath_def]

Depends on / 依赖: contextual, isPath_def
-/
theorem cons_isPath_iff {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (cons h p).IsPath ↔ p.IsPath ∧ u ∉ p.support := by
  constructor <;> simp +contextual [isPath_def]

/--
lemma `IsPath.cons` / 引理 `IsPath.cons`

English:
lemma IsPath.cons
  given: {p : Walk G v w} (hp : p.IsPath) (hu : u ∉ p.support) {h : G.Adj u v}
  proof: (cons_isPath_iff _ _).2 ⟨hp, hu⟩

@[simp]

中文:
引理 是道路.cons
  条件: {p : 途径 G v w} (hp : p.是道路) (hu : u ∉ p.support) {h : G.伴随 u v}
  证明: (cons_isPath_iff _ _).2 ⟨hp, hu⟩

@[simp]
-/
protected lemma IsPath.cons {p : Walk G v w} (hp : p.IsPath) (hu : u ∉ p.support) {h : G.Adj u v} :
    (cons h p).IsPath :=
  (cons_isPath_iff _ _).2 ⟨hp, hu⟩

@[simp]
/--
theorem `isPath_iff_nil` / 定理 `isPath_iff_nil`

English:
theorem isPath_iff_nil
  given: {u : V} {p : G.Walk u u}
  statement: p.IsPath ↔ p.Nil
  proof: by
  cases p <;> simp [IsPath.nil]

@[deprecated isPath_iff_nil (since := "2026-06-01")]

中文:
定理 isPath_iff_nil
  条件: {u : V} {p : G.途径 u u}
  结论: p.是道路 ↔ p.Nil
  证明: by
  cases p <;> simp [IsPath.nil]

@[deprecated isPath_iff_nil (since := "2026-06-01")]

Depends on / 依赖: IsPath, IsPath.nil
-/
theorem isPath_iff_nil {u : V} {p : G.Walk u u} : p.IsPath ↔ p.Nil := by
  cases p <;> simp [IsPath.nil]

@[deprecated isPath_iff_nil (since := "2026-06-01")]
/--
theorem `isPath_iff_eq_nil` / 定理 `isPath_iff_eq_nil`

English:
theorem isPath_iff_eq_nil
  given: {u : V} {p : G.Walk u u}
  statement: p.IsPath ↔ p = nil
  proof: by
  simp

中文:
定理 isPath_iff_eq_nil
  条件: {u : V} {p : G.途径 u u}
  结论: p.是道路 ↔ p = nil
  证明: by
  simp
-/
theorem isPath_iff_eq_nil {u : V} {p : G.Walk u u} : p.IsPath ↔ p = nil := by
  simp

/--
theorem `IsPath.nil_iff_eq` / 定理 `IsPath.nil_iff_eq`

English:
theorem IsPath.nil_iff_eq
  given: {u v : V} {p : G.Walk u v} (hp : p.IsPath)
  statement: p.Nil ↔ u = v
  proof: by
  refine ⟨fun ⟨⟩ => rfl, ?_⟩
  rintro rfl
  exact isPath_iff_nil.mp hp

中文:
定理 是道路.nil_iff_eq
  条件: {u v : V} {p : G.途径 u v} (hp : p.是道路)
  结论: p.Nil ↔ u = v
  证明: by
  refine ⟨fun ⟨⟩ => rfl, ?_⟩
  rintro rfl
  exact isPath_iff_nil.mp hp

Depends on / 依赖: isPath_iff_nil, isPath_iff_nil.mp
-/
theorem IsPath.nil_iff_eq {u v : V} {p : G.Walk u v} (hp : p.IsPath) : p.Nil ↔ u = v := by
  refine ⟨fun ⟨⟩ => rfl, ?_⟩
  rintro rfl
  exact isPath_iff_nil.mp hp

/--
theorem `_root_.SimpleGraph.Adj.isPath_toWalk` / 定理 `_root_.SimpleGraph.Adj.isPath_toWalk`

English:
theorem _root_.SimpleGraph.Adj.isPath_toWalk
  given: (h : G.Adj u v)
  statement: h.toWalk.IsPath
  proof: by
  simp [h.ne]

中文:
定理 _root_.简单图.伴随.isPath_toWalk
  条件: (h : G.伴随 u v)
  结论: h.toWalk.是道路
  证明: by
  simp [h.ne]

Depends on / 依赖: h.ne
-/
theorem _root_.SimpleGraph.Adj.isPath_toWalk (h : G.Adj u v) : h.toWalk.IsPath := by
  simp [h.ne]

/--
theorem `IsPath.reverse` / 定理 `IsPath.reverse`

English:
theorem IsPath.reverse
  given: {u v : V} {p : G.Walk u v} (h : p.IsPath)
  statement: p.reverse.IsPath
  proof: by
  simpa [isPath_def] using h

@[simp]

中文:
定理 是道路.reverse
  条件: {u v : V} {p : G.途径 u v} (h : p.是道路)
  结论: p.reverse.是道路
  证明: by
  simpa [isPath_def] using h

@[simp]

Depends on / 依赖: isPath_def
-/
theorem IsPath.reverse {u v : V} {p : G.Walk u v} (h : p.IsPath) : p.reverse.IsPath := by
  simpa [isPath_def] using h

@[simp]
/--
theorem `isPath_reverse_iff` / 定理 `isPath_reverse_iff`

English:
theorem isPath_reverse_iff
  given: {u v : V} (p : G.Walk u v)
  statement: p.reverse.IsPath ↔ p.IsPath
  proof: by
  constructor <;> intro h <;> convert! h.reverse; simp

中文:
定理 isPath_reverse_iff
  条件: {u v : V} (p : G.途径 u v)
  结论: p.reverse.是道路 ↔ p.是道路
  证明: by
  constructor <;> intro h <;> convert! h.reverse; simp

Depends on / 依赖: convert, h.reverse, reverse
-/
theorem isPath_reverse_iff {u v : V} (p : G.Walk u v) : p.reverse.IsPath ↔ p.IsPath := by
  constructor <;> intro h <;> convert! h.reverse; simp

/--
theorem `IsPath.of_append_left` / 定理 `IsPath.of_append_left`

English:
theorem IsPath.of_append_left
  given: {u v w : V} {p : G.Walk u v} {q : G.Walk v w}
  proof: by
  simp only [isPath_def, support_append]
  exact List.Nodup.of_append_left

中文:
定理 是道路.of_append_left
  条件: {u v w : V} {p : G.途径 u v} {q : G.途径 v w}
  证明: by
  simp only [isPath_def, support_append]
  exact List.Nodup.of_append_left

Depends on / 依赖: List.Nodup.of_append_left, isPath_def, of_append_left, support_append
-/
theorem IsPath.of_append_left {u v w : V} {p : G.Walk u v} {q : G.Walk v w} :
    (p.append q).IsPath -> p.IsPath := by
  simp only [isPath_def, support_append]
  exact List.Nodup.of_append_left

/--
theorem `IsPath.of_append_right` / 定理 `IsPath.of_append_right`

English:
theorem IsPath.of_append_right
  statement: {u v w : V} {p : G.Walk u v} {q : G.Walk v w}
  proof: by
  rw [← isPath_reverse_iff] at h ⊢
  rw [reverse_append] at h
  apply h.of_append_left

中文:
定理 是道路.of_append_right
  结论: {u v w : V} {p : G.途径 u v} {q : G.途径 v w}
  证明: by
  rw [← isPath_reverse_iff] at h ⊢
  rw [reverse_append] at h
  apply h.of_append_left

Depends on / 依赖: h.of_append_left, isPath_reverse_iff, of_append_left, reverse_append
-/
theorem IsPath.of_append_right {u v w : V} {p : G.Walk u v} {q : G.Walk v w}
    (h : (p.append q).IsPath) : q.IsPath := by
  rw [← isPath_reverse_iff] at h ⊢
  rw [reverse_append] at h
  apply h.of_append_left

/--
theorem `isTrail_of_isSubwalk` / 定理 `isTrail_of_isSubwalk`

English:
theorem isTrail_of_isSubwalk
  statement: {v w v' w'} {p₁ : G.Walk v w} {p₂ : G.Walk v' w'}
  proof: by
  obtain ⟨_, _, h⟩ := h
  rw [h] at h₂
  exact h₂.of_append_left.of_append_right

中文:
定理 isTrail_of_isSubwalk
  结论: {v w v' w'} {p₁ : G.途径 v w} {p₂ : G.途径 v' w'}
  证明: by
  obtain ⟨_, _, h⟩ := h
  rw [h] at h₂
  exact h₂.of_append_left.of_append_right

Depends on / 依赖: of_append_left, of_append_left.of_append_right, of_append_right
-/
theorem isTrail_of_isSubwalk {v w v' w'} {p₁ : G.Walk v w} {p₂ : G.Walk v' w'}
    (h : p₁.IsSubwalk p₂) (h₂ : p₂.IsTrail) : p₁.IsTrail := by
  obtain ⟨_, _, h⟩ := h
  rw [h] at h₂
  exact h₂.of_append_left.of_append_right

/--
theorem `isPath_of_isSubwalk` / 定理 `isPath_of_isSubwalk`

English:
theorem isPath_of_isSubwalk
  statement: {v w v' w' : V} {p₁ : G.Walk v w} {p₂ : G.Walk v' w'}
  proof: by
  obtain ⟨_, _, h⟩ := h
  rw [h] at h₂
  exact h₂.of_append_left.of_append_right

中文:
定理 isPath_of_isSubwalk
  结论: {v w v' w' : V} {p₁ : G.途径 v w} {p₂ : G.途径 v' w'}
  证明: by
  obtain ⟨_, _, h⟩ := h
  rw [h] at h₂
  exact h₂.of_append_left.of_append_right

Depends on / 依赖: of_append_left, of_append_left.of_append_right, of_append_right
-/
theorem isPath_of_isSubwalk {v w v' w' : V} {p₁ : G.Walk v w} {p₂ : G.Walk v' w'}
    (h : p₁.IsSubwalk p₂) (h₂ : p₂.IsPath) : p₁.IsPath := by
  obtain ⟨_, _, h⟩ := h
  rw [h] at h₂
  exact h₂.of_append_left.of_append_right

/--
lemma `IsPath.of_adj` / 引理 `IsPath.of_adj`

English:
lemma IsPath.of_adj
  given: {G : SimpleGraph V} {u v : V} (h : G.Adj u v)
  statement: h.toWalk.IsPath
  proof: by
  aesop

中文:
引理 是道路.of_adj
  条件: {G : 简单图 V} {u v : V} (h : G.伴随 u v)
  结论: h.toWalk.是道路
  证明: by
  aesop
-/
lemma IsPath.of_adj {G : SimpleGraph V} {u v : V} (h : G.Adj u v) : h.toWalk.IsPath := by
  aesop

/--
theorem `concat_isPath_iff` / 定理 `concat_isPath_iff`

English:
theorem concat_isPath_iff
  given: {p : G.Walk u v} (h : G.Adj v w)
  proof: by
  rw [← (p.concat h).isPath_reverse_iff]; rw [← p.isPath_reverse_iff]; rw [reverse_concat]; rw [← List.mem_reverse]; rw [← support_reverse]
  exact cons_isPath_iff h.symm p.reverse

中文:
定理 concat_isPath_iff
  条件: {p : G.途径 u v} (h : G.伴随 v w)
  证明: by
  rw [← (p.concat h).isPath_reverse_iff]; rw [← p.isPath_reverse_iff]; rw [reverse_concat]; rw [← List.mem_reverse]; rw [← support_reverse]
  exact cons_isPath_iff h.symm p.reverse

Depends on / 依赖: List.mem_reverse, concat, cons_isPath_iff, h.symm, isPath_reverse_iff, mem_reverse, p.concat, p.isPath_reverse_iff, p.reverse, reverse, reverse_concat, support_reverse
-/
theorem concat_isPath_iff {p : G.Walk u v} (h : G.Adj v w) :
    (p.concat h).IsPath ↔ p.IsPath ∧ w ∉ p.support := by
  rw [← (p.concat h).isPath_reverse_iff]; rw [← p.isPath_reverse_iff]; rw [reverse_concat]; rw [← List.mem_reverse]; rw [← support_reverse]
  exact cons_isPath_iff h.symm p.reverse

/--
theorem `IsPath.concat` / 定理 `IsPath.concat`

English:
theorem IsPath.concat
  statement: {p : G.Walk u v} (hp : p.IsPath) (hw : w ∉ p.support)
  proof: (concat_isPath_iff h).mpr ⟨hp, hw⟩

中文:
定理 是道路.concat
  结论: {p : G.途径 u v} (hp : p.是道路) (hw : w ∉ p.support)
  证明: (concat_isPath_iff h).mpr ⟨hp, hw⟩

Depends on / 依赖: concat_isPath_iff
-/
theorem IsPath.concat {p : G.Walk u v} (hp : p.IsPath) (hw : w ∉ p.support)
    (h : G.Adj v w) : (p.concat h).IsPath :=
  (concat_isPath_iff h).mpr ⟨hp, hw⟩

/--
lemma `IsPath.take_of_take` / 引理 `IsPath.take_of_take`

English:
lemma IsPath.take_of_take
  given: {n k} {p : G.Walk u v} (h : (p.take k).IsPath) (hle : n <= k)
  proof: isPath_of_isSubwalk (p.take_isSubwalk_take hle) h

中文:
引理 是道路.take_of_take
  条件: {n k} {p : G.途径 u v} (h : (p.take k).是道路) (hle : n <= k)
  证明: isPath_of_isSubwalk (p.take_isSubwalk_take hle) h

Depends on / 依赖: isPath_of_isSubwalk, p.take_isSubwalk_take, take_isSubwalk_take
-/
lemma IsPath.take_of_take {n k} {p : G.Walk u v} (h : (p.take k).IsPath) (hle : n <= k) :
    (p.take n).IsPath :=
  isPath_of_isSubwalk (p.take_isSubwalk_take hle) h

/--
lemma `IsPath.drop_of_drop` / 引理 `IsPath.drop_of_drop`

English:
lemma IsPath.drop_of_drop
  given: {n k} {p : G.Walk u v} (h : (p.drop k).IsPath) (hle : k <= n)
  proof: isPath_of_isSubwalk (p.drop_isSubwalk_drop hle) h

中文:
引理 是道路.drop_of_drop
  条件: {n k} {p : G.途径 u v} (h : (p.drop k).是道路) (hle : k <= n)
  证明: isPath_of_isSubwalk (p.drop_isSubwalk_drop hle) h

Depends on / 依赖: drop_isSubwalk_drop, isPath_of_isSubwalk, p.drop_isSubwalk_drop
-/
lemma IsPath.drop_of_drop {n k} {p : G.Walk u v} (h : (p.drop k).IsPath) (hle : k <= n) :
    (p.drop n).IsPath :=
  isPath_of_isSubwalk (p.drop_isSubwalk_drop hle) h

/--
lemma `IsPath.take` / 引理 `IsPath.take`

English:
lemma IsPath.take
  given: {p : G.Walk u v} (h : p.IsPath) (n : Nat)
  proof: isPath_of_isSubwalk (p.isSubwalk_take n) h

中文:
引理 是道路.take
  条件: {p : G.途径 u v} (h : p.是道路) (n : 自然数)
  证明: isPath_of_isSubwalk (p.isSubwalk_take n) h

Depends on / 依赖: isPath_of_isSubwalk, isSubwalk_take, p.isSubwalk_take
-/
lemma IsPath.take {p : G.Walk u v} (h : p.IsPath) (n : Nat) :
    (p.take n).IsPath :=
  isPath_of_isSubwalk (p.isSubwalk_take n) h

/--
lemma `IsPath.drop` / 引理 `IsPath.drop`

English:
lemma IsPath.drop
  given: {p : G.Walk u v} (h : p.IsPath) (n : Nat)
  proof: isPath_of_isSubwalk (p.isSubwalk_drop n) h

中文:
引理 是道路.drop
  条件: {p : G.途径 u v} (h : p.是道路) (n : 自然数)
  证明: isPath_of_isSubwalk (p.isSubwalk_drop n) h

Depends on / 依赖: isPath_of_isSubwalk, isSubwalk_drop, p.isSubwalk_drop
-/
lemma IsPath.drop {p : G.Walk u v} (h : p.IsPath) (n : Nat) :
    (p.drop n).IsPath :=
  isPath_of_isSubwalk (p.isSubwalk_drop n) h

/--
lemma `IsPath.mem_support_iff_exists_append` / 引理 `IsPath.mem_support_iff_exists_append`

English:
lemma IsPath.mem_support_iff_exists_append
  given: {p : G.Walk u v} (hp : p.IsPath)
  proof: by
  refine ⟨fun hw => ?_, fun ⟨q, r, hq, hr, hqr⟩ => p.mem_support_iff_exists_append.mpr ⟨q, r, hqr⟩⟩
  obtain ⟨q, r, hqr⟩ := p.mem_support_iff_exists_append.mp hw
  have : (q.append r).IsPath := hqr ▸ hp
  exact ⟨q, r, this.of_append_left, this.of_append_right, hqr⟩

中文:
引理 是道路.mem_support_iff_存在_append
  条件: {p : G.途径 u v} (hp : p.是道路)
  证明: by
  refine ⟨fun hw => ?_, fun ⟨q, r, hq, hr, hqr⟩ => p.mem_support_iff_exists_append.mpr ⟨q, r, hqr⟩⟩
  obtain ⟨q, r, hqr⟩ := p.mem_support_iff_exists_append.mp hw
  have : (q.append r).IsPath := hqr ▸ hp
  exact ⟨q, r, this.of_append_left, this.of_append_right, hqr⟩

Depends on / 依赖: IsPath, append, mem_support_iff_exists_append, of_append_left, of_append_right, p.mem_support_iff_exists_append.mp, p.mem_support_iff_exists_append.mpr, q.append, this.of_append_left, this.of_append_right
-/
lemma IsPath.mem_support_iff_exists_append {p : G.Walk u v} (hp : p.IsPath) :
    w in p.support ↔ exists (q : G.Walk u w) (r : G.Walk w v), q.IsPath ∧ r.IsPath ∧ p = q.append r := by
  refine ⟨fun hw => ?_, fun ⟨q, r, hq, hr, hqr⟩ => p.mem_support_iff_exists_append.mpr ⟨q, r, hqr⟩⟩
  obtain ⟨q, r, hqr⟩ := p.mem_support_iff_exists_append.mp hw
  have : (q.append r).IsPath := hqr ▸ hp
  exact ⟨q, r, this.of_append_left, this.of_append_right, hqr⟩

/--
lemma `IsPath.disjoint_support_of_append` / 引理 `IsPath.disjoint_support_of_append`

English:
lemma IsPath.disjoint_support_of_append
  statement: {p : G.Walk u v} {q : G.Walk v w}
  proof: by
  have hpq' := hpq.support_nodup
  rw [support_append] at hpq'
  rw [support_tail_of_not_nil q hq]
  exact List.disjoint_of_nodup_append hpq'

中文:
引理 是道路.disjoint_support_of_append
  结论: {p : G.途径 u v} {q : G.途径 v w}
  证明: by
  have hpq' := hpq.support_nodup
  rw [support_append] at hpq'
  rw [support_tail_of_not_nil q hq]
  exact List.disjoint_of_nodup_append hpq'

Depends on / 依赖: List.disjoint_of_nodup_append, disjoint_of_nodup_append, hpq.support_nodup, support_append, support_nodup, support_tail_of_not_nil
-/
lemma IsPath.disjoint_support_of_append {p : G.Walk u v} {q : G.Walk v w}
    (hpq : (p.append q).IsPath) (hq : ¬q.Nil) : p.support.Disjoint q.tail.support := by
  have hpq' := hpq.support_nodup
  rw [support_append] at hpq'
  rw [support_tail_of_not_nil q hq]
  exact List.disjoint_of_nodup_append hpq'

/--
lemma `IsPath.ne_of_mem_support_of_append` / 引理 `IsPath.ne_of_mem_support_of_append`

English:
lemma IsPath.ne_of_mem_support_of_append
  statement: {p : G.Walk u v} {q : G.Walk v w}
  proof: by
  rintro rfl
  have hq : ¬q.Nil := by
    intro hq
    simp [nil_iff_support_eq.mp hq, hyv] at hy
  have hx' : x in q.tail.support := by
    rw [support_tail_of_not_nil q hq]
    rw [mem_support_iff] at hy
    exact hy.resolve_left hyv
  exact IsPath.disjoint_support_of_append hpq hq hx hx'

@[si

中文:
引理 是道路.ne_of_mem_support_of_append
  结论: {p : G.途径 u v} {q : G.途径 v w}
  证明: by
  rintro rfl
  have hq : ¬q.Nil := by
    intro hq
    simp [nil_iff_support_eq.mp hq, hyv] at hy
  have hx' : x in q.tail.support := by
    rw [support_tail_of_not_nil q hq]
    rw [mem_support_iff] at hy
    exact hy.resolve_left hyv
  exact IsPath.disjoint_support_of_append hpq hq hx hx'

@[si

Depends on / 依赖: IsPath, IsPath.disjoint_support_of_append, disjoint_support_of_append, hy.resolve_left, mem_support_iff, nil_iff_support_eq, nil_iff_support_eq.mp, q.Nil, q.tail.support, resolve_left, support, support_tail_of_not_nil
-/
lemma IsPath.ne_of_mem_support_of_append {p : G.Walk u v} {q : G.Walk v w}
    (hpq : (p.append q).IsPath) {x y : V} (hyv : y != v) (hx : x in p.support) (hy : y in q.support) :
    x != y := by
  rintro rfl
  have hq : ¬q.Nil := by
    intro hq
    simp [nil_iff_support_eq.mp hq, hyv] at hy
  have hx' : x in q.tail.support := by
    rw [support_tail_of_not_nil q hq]
    rw [mem_support_iff] at hy
    exact hy.resolve_left hyv
  exact IsPath.disjoint_support_of_append hpq hq hx hx'

@[simp]
/--
theorem `not_isCircuit_nil` / 定理 `not_isCircuit_nil`

English:
theorem not_isCircuit_nil
  given: {u : V}
  statement: ¬(nil : G.Walk u u).IsCircuit
  proof: (·.ne_nil rfl)

@[simp]

中文:
定理 not_isCircuit_nil
  条件: {u : V}
  结论: ¬(nil : G.途径 u u).是Circuit
  证明: (·.ne_nil rfl)

@[simp]

Depends on / 依赖: ne_nil
-/
theorem not_isCircuit_nil {u : V} : ¬(nil : G.Walk u u).IsCircuit :=
  (·.ne_nil rfl)

@[simp]
/--
theorem `not_isCycle_nil` / 定理 `not_isCycle_nil`

English:
theorem not_isCycle_nil
  given: {u : V}
  statement: ¬(nil : G.Walk u u).IsCycle
  proof: (·.ne_nil rfl)

@[deprecated (since := "2026-06-16")] alias IsCycle.not_of_nil := not_isCycle_nil

中文:
定理 not_isCycle_nil
  条件: {u : V}
  结论: ¬(nil : G.途径 u u).是环
  证明: (·.ne_nil rfl)

@[deprecated (since := "2026-06-16")] alias IsCycle.not_of_nil := not_isCycle_nil

Depends on / 依赖: ne_nil
-/
theorem not_isCycle_nil {u : V} : ¬(nil : G.Walk u u).IsCycle :=
  (·.ne_nil rfl)

@[deprecated (since := "2026-06-16")] alias IsCycle.not_of_nil := not_isCycle_nil

/--
lemma `IsCircuit.ne_bot` / 引理 `IsCircuit.ne_bot`

English:
lemma IsCircuit.ne_bot
  statement: forall {p : G.Walk u u}, p.IsCircuit -> G != ⊥

中文:
引理 是Circuit.ne_bot
  结论: 对任意 {p : G.途径 u u}, p.是Circuit -> G != ⊥
-/
lemma IsCircuit.ne_bot : forall {p : G.Walk u u}, p.IsCircuit -> G != ⊥
  | cons h _, hp => by rintro rfl; exact h

/--
lemma `IsCircuit.three_le_length` / 引理 `IsCircuit.three_le_length`

English:
lemma IsCircuit.three_le_length
  given: {p : G.Walk v v} (hp : p.IsCircuit)
  statement: 3 <= p.length
  proof: by
  match p with
  | .cons hadj .nil => simp at hadj
| .cons _ .cons _ .nil => simpa using hp.isTrail
| .cons _ .cons _ .cons _ _ => grind [length_cons]

中文:
引理 是Circuit.three_le_length
  条件: {p : G.途径 v v} (hp : p.是Circuit)
  结论: 3 <= p.length
  证明: by
  match p with
  | .cons hadj .nil => simp at hadj
| .cons _ .cons _ .nil => simpa using hp.isTrail
| .cons _ .cons _ .cons _ _ => grind [length_cons]

Depends on / 依赖: hp.isTrail, isTrail, length_cons
-/
lemma IsCircuit.three_le_length {p : G.Walk v v} (hp : p.IsCircuit) : 3 <= p.length := by
  match p with
  | .cons hadj .nil => simp at hadj
| .cons _ .cons _ .nil => simpa using hp.isTrail
| .cons _ .cons _ .cons _ _ => grind [length_cons]

/--
lemma `not_nil_of_isCycle_cons` / 引理 `not_nil_of_isCycle_cons`

English:
lemma not_nil_of_isCycle_cons
  given: {p : G.Walk u v} {h : G.Adj v u} (hc : (Walk.cons h p).IsCycle)
  proof: by
  grind [not_nil_iff_lt_length, hc.three_le_length, length_cons]

中文:
引理 not_nil_of_isCycle_cons
  条件: {p : G.途径 u v} {h : G.伴随 v u} (hc : (途径.cons h p).是环)
  证明: by
  grind [not_nil_iff_lt_length, hc.three_le_length, length_cons]

Depends on / 依赖: hc.three_le_length, length_cons, not_nil_iff_lt_length, three_le_length
-/
lemma not_nil_of_isCycle_cons {p : G.Walk u v} {h : G.Adj v u} (hc : (Walk.cons h p).IsCycle) :
    ¬ p.Nil := by
  grind [not_nil_iff_lt_length, hc.three_le_length, length_cons]

/--
theorem `cons_isCycle_iff` / 定理 `cons_isCycle_iff`

English:
theorem cons_isCycle_iff
  given: {u v : V} (p : G.Walk v u) (h : G.Adj u v)
  proof: by
  simp only [Walk.isCycle_def, Walk.isPath_def, Walk.isTrail_def, edges_cons, List.nodup_cons,
    support_cons, List.tail_cons]
  have : p.support.Nodup -> p.edges.Nodup := edges_nodup_of_support_nodup
  tauto

中文:
定理 cons_isCycle_iff
  条件: {u v : V} (p : G.途径 v u) (h : G.伴随 u v)
  证明: by
  simp only [Walk.isCycle_def, Walk.isPath_def, Walk.isTrail_def, edges_cons, List.nodup_cons,
    support_cons, List.tail_cons]
  have : p.support.Nodup -> p.edges.Nodup := edges_nodup_of_support_nodup
  tauto

Depends on / 依赖: List.nodup_cons, List.tail_cons, Walk.isCycle_def, Walk.isPath_def, Walk.isTrail_def, edges_cons, edges_nodup_of_support_nodup, isCycle_def, isPath_def, isTrail_def, nodup_cons, p.edges.Nodup, p.support.Nodup, support, support_cons, tail_cons
-/
theorem cons_isCycle_iff {u v : V} (p : G.Walk v u) (h : G.Adj u v) :
    (Walk.cons h p).IsCycle ↔ p.IsPath ∧ s(u, v) ∉ p.edges := by
  simp only [Walk.isCycle_def, Walk.isPath_def, Walk.isTrail_def, edges_cons, List.nodup_cons,
    support_cons, List.tail_cons]
  have : p.support.Nodup -> p.edges.Nodup := edges_nodup_of_support_nodup
  tauto

/--
theorem `IsCycle.nodup_dropLast_support` / 定理 `IsCycle.nodup_dropLast_support`

English:
theorem IsCycle.nodup_dropLast_support
  given: {p : G.Walk u u} (h : p.IsCycle)
  proof: p.tail_support_perm_dropLast_support.nodup_iff.mp h.support_nodup

中文:
定理 是环.nodup_dropLast_support
  条件: {p : G.途径 u u} (h : p.是环)
  证明: p.tail_support_perm_dropLast_support.nodup_iff.mp h.support_nodup

Depends on / 依赖: h.support_nodup, nodup_iff, p.tail_support_perm_dropLast_support.nodup_iff.mp, support_nodup, tail_support_perm_dropLast_support
-/
theorem IsCycle.nodup_dropLast_support {p : G.Walk u u} (h : p.IsCycle) :
    p.support.dropLast.Nodup :=
  p.tail_support_perm_dropLast_support.nodup_iff.mp h.support_nodup

/--
lemma `IsCycle.reverse` / 引理 `IsCycle.reverse`

English:
lemma IsCycle.reverse
  given: {p : G.Walk u u} (h : p.IsCycle)
  statement: p.reverse.IsCycle
  proof: by
  simp only [Walk.isCycle_def, nodup_tail_support_reverse] at h ⊢
  exact ⟨h.1.reverse, fun h' => h.2.1 (by simp_all [← Walk.length_eq_zero_iff]), h.2.2⟩

@[simp]

中文:
引理 是环.reverse
  条件: {p : G.途径 u u} (h : p.是环)
  结论: p.reverse.是环
  证明: by
  simp only [Walk.isCycle_def, nodup_tail_support_reverse] at h ⊢
  exact ⟨h.1.reverse, fun h' => h.2.1 (by simp_all [← Walk.length_eq_zero_iff]), h.2.2⟩

@[simp]
-/
protected lemma IsCycle.reverse {p : G.Walk u u} (h : p.IsCycle) : p.reverse.IsCycle := by
  simp only [Walk.isCycle_def, nodup_tail_support_reverse] at h ⊢
  exact ⟨h.1.reverse, fun h' => h.2.1 (by simp_all [← Walk.length_eq_zero_iff]), h.2.2⟩

@[simp]
/--
lemma `isCycle_reverse` / 引理 `isCycle_reverse`

English:
lemma isCycle_reverse
  given: {p : G.Walk u u}
  statement: p.reverse.IsCycle ↔ p.IsCycle where
  proof: by simpa using h.reverse
  mpr := .reverse

中文:
引理 isCycle_reverse
  条件: {p : G.途径 u u}
  结论: p.reverse.是环 ↔ p.是环 where
  证明: by simpa using h.reverse
  mpr := .reverse

Depends on / 依赖: h.reverse, reverse
-/
lemma isCycle_reverse {p : G.Walk u u} : p.reverse.IsCycle ↔ p.IsCycle where
  mp h := by simpa using h.reverse
  mpr := .reverse

/--
lemma `IsCycle.isPath_of_append_right` / 引理 `IsCycle.isPath_of_append_right`

English:
lemma IsCycle.isPath_of_append_right
  statement: {p : G.Walk u v} {q : G.Walk v u} (h : ¬ p.Nil)
  proof: by
  have := hcyc.2
  rw [tail_support_append]; rw [List.nodup_append'] at this
  rw [isPath_def]; rw [← cons_tail_support]; rw [List.nodup_cons]
  exact ⟨this.2.2 (p.end_mem_tail_support h), this.2.1⟩

中文:
引理 是环.isPath_of_append_right
  结论: {p : G.途径 u v} {q : G.途径 v u} (h : ¬ p.Nil)
  证明: by
  have := hcyc.2
  rw [tail_support_append]; rw [List.nodup_append'] at this
  rw [isPath_def]; rw [← cons_tail_support]; rw [List.nodup_cons]
  exact ⟨this.2.2 (p.end_mem_tail_support h), this.2.1⟩

Depends on / 依赖: List.nodup_append, List.nodup_cons, cons_tail_support, end_mem_tail_support, isPath_def, nodup_append, nodup_cons, p.end_mem_tail_support, tail_support_append
-/
lemma IsCycle.isPath_of_append_right {p : G.Walk u v} {q : G.Walk v u} (h : ¬ p.Nil)
    (hcyc : (p.append q).IsCycle) : q.IsPath := by
  have := hcyc.2
  rw [tail_support_append]; rw [List.nodup_append'] at this
  rw [isPath_def]; rw [← cons_tail_support]; rw [List.nodup_cons]
  exact ⟨this.2.2 (p.end_mem_tail_support h), this.2.1⟩

/--
lemma `IsCycle.isPath_of_append_left` / 引理 `IsCycle.isPath_of_append_left`

English:
lemma IsCycle.isPath_of_append_left
  statement: {p : G.Walk u v} {q : G.Walk v u} (h : ¬ q.Nil)
  proof: p.isPath_reverse_iff.mp ((reverse_append _ _ ▸ hcyc.reverse).isPath_of_append_right (by simpa))

中文:
引理 是环.isPath_of_append_left
  结论: {p : G.途径 u v} {q : G.途径 v u} (h : ¬ q.Nil)
  证明: p.isPath_reverse_iff.mp ((reverse_append _ _ ▸ hcyc.reverse).isPath_of_append_right (by simpa))

Depends on / 依赖: hcyc.reverse, isPath_of_append_right, isPath_reverse_iff, p.isPath_reverse_iff.mp, reverse, reverse_append
-/
lemma IsCycle.isPath_of_append_left {p : G.Walk u v} {q : G.Walk v u} (h : ¬ q.Nil)
    (hcyc : (p.append q).IsCycle) : p.IsPath :=
  p.isPath_reverse_iff.mp ((reverse_append _ _ ▸ hcyc.reverse).isPath_of_append_right (by simpa))

/--
theorem `IsCycle.isPath_tail` / 定理 `IsCycle.isPath_tail`

English:
theorem IsCycle.isPath_tail
  given: {p : G.Walk u u} (h : p.IsCycle)
  statement: p.tail.IsPath
  proof: IsPath.mk' p.support_tail_of_not_nil h.not_nil ▸ h.support_nodup

中文:
定理 是环.isPath_tail
  条件: {p : G.途径 u u} (h : p.是环)
  结论: p.tail.是道路
  证明: IsPath.mk' p.support_tail_of_not_nil h.not_nil ▸ h.support_nodup

Depends on / 依赖: IsPath, IsPath.mk, h.not_nil, h.support_nodup, not_nil, p.support_tail_of_not_nil, support_nodup, support_tail_of_not_nil
-/
theorem IsCycle.isPath_tail {p : G.Walk u u} (h : p.IsCycle) : p.tail.IsPath :=
IsPath.mk' p.support_tail_of_not_nil h.not_nil ▸ h.support_nodup

/--
lemma `IsPath.tail` / 引理 `IsPath.tail`

English:
lemma IsPath.tail
  given: {p : G.Walk u v} (hp : p.IsPath)
  statement: p.tail.IsPath
  proof: by
  cases p with
  | nil => simp
  | cons hadj p =>
    simp_all [Walk.isPath_def]

中文:
引理 是道路.tail
  条件: {p : G.途径 u v} (hp : p.是道路)
  结论: p.tail.是道路
  证明: by
  cases p with
  | nil => simp
  | cons hadj p =>
    simp_all [Walk.isPath_def]

Depends on / 依赖: Walk.isPath_def, isPath_def
-/
lemma IsPath.tail {p : G.Walk u v} (hp : p.IsPath) : p.tail.IsPath := by
  cases p with
  | nil => simp
  | cons hadj p =>
    simp_all [Walk.isPath_def]

/--
theorem `IsCycle.isPath_dropLast` / 定理 `IsCycle.isPath_dropLast`

English:
theorem IsCycle.isPath_dropLast
  given: {p : G.Walk u u} (h : p.IsCycle)
  statement: p.dropLast.IsPath
  proof: .mk' p.support_dropLast h.not_nil ▸ h.nodup_dropLast_support

中文:
定理 是环.isPath_dropLast
  条件: {p : G.途径 u u} (h : p.是环)
  结论: p.dropLast.是道路
  证明: .mk' p.support_dropLast h.not_nil ▸ h.nodup_dropLast_support

Depends on / 依赖: h.nodup_dropLast_support, h.not_nil, nodup_dropLast_support, not_nil, p.support_dropLast, support_dropLast
-/
theorem IsCycle.isPath_dropLast {p : G.Walk u u} (h : p.IsCycle) : p.dropLast.IsPath :=
.mk' p.support_dropLast h.not_nil ▸ h.nodup_dropLast_support

/--
theorem `IsPath.dropLast` / 定理 `IsPath.dropLast`

English:
theorem IsPath.dropLast
  given: (hp : p.IsPath)
  statement: p.dropLast.IsPath
  proof: hp.take _

中文:
定理 是道路.dropLast
  条件: (hp : p.是道路)
  结论: p.dropLast.是道路
  证明: hp.take _

Depends on / 依赖: hp.take
-/
theorem IsPath.dropLast (hp : p.IsPath) : p.dropLast.IsPath :=
  hp.take _

/--
theorem `IsCycle.isPath_drop` / 定理 `IsCycle.isPath_drop`

English:
theorem IsCycle.isPath_drop
  given: {u n} {p : G.Walk u u} (h : p.IsCycle) (hn : 0 < n)
  proof: by
  replace h : (p.drop 1).IsPath := h.isPath_tail
  rw [← Nat.add_sub_of_le hn]; rw [drop_add_eq]
  simp [h.drop (n - 1), -drop_drop]

中文:
定理 是环.isPath_drop
  条件: {u n} {p : G.途径 u u} (h : p.是环) (hn : 0 < n)
  证明: by
  replace h : (p.drop 1).IsPath := h.isPath_tail
  rw [← Nat.add_sub_of_le hn]; rw [drop_add_eq]
  simp [h.drop (n - 1), -drop_drop]

Depends on / 依赖: IsPath, Nat.add_sub_of_le, add_sub_of_le, drop_add_eq, drop_drop, h.drop, h.isPath_tail, isPath_tail, p.drop, replace
-/
theorem IsCycle.isPath_drop {u n} {p : G.Walk u u} (h : p.IsCycle) (hn : 0 < n) :
    (p.drop n).IsPath := by
  replace h : (p.drop 1).IsPath := h.isPath_tail
  rw [← Nat.add_sub_of_le hn]; rw [drop_add_eq]
  simp [h.drop (n - 1), -drop_drop]

/--
theorem `IsCycle.isPath_take` / 定理 `IsCycle.isPath_take`

English:
theorem IsCycle.isPath_take
  given: {u n} {p : G.Walk u u} (h : p.IsCycle) (hn : n < p.length)
  proof: by
  replace h : (p.take (p.length - 1)).IsPath := h.isPath_dropLast
  suffices ((p.take (p.length - 1)).take n).IsPath by
    rwa [take_take, isPath_copy, show min (p.length - 1) n = n by omega] at this
  exact h.take n

中文:
定理 是环.isPath_take
  条件: {u n} {p : G.途径 u u} (h : p.是环) (hn : n < p.length)
  证明: by
  replace h : (p.take (p.length - 1)).IsPath := h.isPath_dropLast
  suffices ((p.take (p.length - 1)).take n).IsPath by
    rwa [take_take, isPath_copy, show min (p.length - 1) n = n by omega] at this
  exact h.take n

Depends on / 依赖: IsPath, h.isPath_dropLast, h.take, isPath_copy, isPath_dropLast, length, p.length, p.take, replace, take_take
-/
theorem IsCycle.isPath_take {u n} {p : G.Walk u u} (h : p.IsCycle) (hn : n < p.length) :
    (p.take n).IsPath := by
  replace h : (p.take (p.length - 1)).IsPath := h.isPath_dropLast
  suffices ((p.take (p.length - 1)).take n).IsPath by
    rwa [take_take, isPath_copy, show min (p.length - 1) n = n by omega] at this
  exact h.take n

/--
lemma `exists_isTrail_forall_isTrail_length_le_length` / 引理 `exists_isTrail_forall_isTrail_length_le_length`

English:
lemma exists_isTrail_forall_isTrail_length_le_length
  statement: (G : SimpleGraph V) [N : Nonempty V]
  proof: by
  have := Fintype.ofFinite G.edgeSet
  let s := {n | exists (u v : V) (p : G.Walk u v), p.IsTrail ∧ p.length = n}
  have : s.Finite := Set.Finite.subset (Set.finite_le_nat G.edgeFinset.card)
    fun n ⟨_, _, _, hp, hn⟩ => hn ▸ hp.length_le_card_edgeFinset
  obtain ⟨x⟩ := N
  obtain ⟨_, ⟨⟨u, v, p,

中文:
引理 存在_isTrail_对任意_isTrail_length_le_length
  结论: (G : 简单图 V) [N : 非空 V]
  证明: by
  have := Fintype.ofFinite G.edgeSet
  let s := {n | exists (u v : V) (p : G.Walk u v), p.IsTrail ∧ p.length = n}
  have : s.Finite := Set.Finite.subset (Set.finite_le_nat G.edgeFinset.card)
    fun n ⟨_, _, _, hp, hn⟩ => hn ▸ hp.length_le_card_edgeFinset
  obtain ⟨x⟩ := N
  obtain ⟨_, ⟨⟨u, v, p,

Depends on / 依赖: Eq.refl, Finite, Fintype, Fintype.ofFinite, G.Walk, G.edgeFinset.card, G.edgeSet, IsTrail, Set.Finite.subset, Set.finite_le_nat, Walk.nil, edgeFinset, edgeSet, exists_maximal, finite_le_nat, hp.length_le_card_edgeFinset, length, length_le_card_edgeFinset, ofFinite, p.IsTrail
-/
lemma exists_isTrail_forall_isTrail_length_le_length (G : SimpleGraph V) [N : Nonempty V]
    [Finite G.edgeSet] :
    exists (u v : V) (p : G.Walk u v) (_ : p.IsTrail),
      forall (u' v' : V) (p' : G.Walk u' v') (_ : p'.IsTrail), p'.length <= p.length := by
  have := Fintype.ofFinite G.edgeSet
  let s := {n | exists (u v : V) (p : G.Walk u v), p.IsTrail ∧ p.length = n}
  have : s.Finite := Set.Finite.subset (Set.finite_le_nat G.edgeFinset.card)
    fun n ⟨_, _, _, hp, hn⟩ => hn ▸ hp.length_le_card_edgeFinset
  obtain ⟨x⟩ := N
  obtain ⟨_, ⟨⟨u, v, p, hp, _⟩, hn⟩⟩ := this.exists_maximal ⟨0, ⟨x, x, Walk.nil, by simp⟩⟩
  refine ⟨u, v, p, hp, fun u' v' p' hp' => ?_⟩
  have := hn ⟨u', v', p', hp', Eq.refl p'.length⟩
  lia

/--
lemma `exists_isPath_forall_isPath_length_le_length` / 引理 `exists_isPath_forall_isPath_length_le_length`

English:
lemma exists_isPath_forall_isPath_length_le_length
  statement: (G : SimpleGraph V) [N : Nonempty V]
  proof: by
  have := Fintype.ofFinite G.edgeSet
  let s := {n | exists (u v : V) (p : G.Walk u v), p.IsPath ∧ p.length = n}
  have : s.Finite := Set.Finite.subset (Set.finite_le_nat G.edgeFinset.card)
    fun n ⟨_, _, _, hp, hn⟩ => hn ▸ hp.isTrail.length_le_card_edgeFinset
  obtain ⟨x⟩ := N
  obtain ⟨_, ⟨⟨u

中文:
引理 存在_isPath_对任意_isPath_length_le_length
  结论: (G : 简单图 V) [N : 非空 V]
  证明: by
  have := Fintype.ofFinite G.edgeSet
  let s := {n | exists (u v : V) (p : G.Walk u v), p.IsPath ∧ p.length = n}
  have : s.Finite := Set.Finite.subset (Set.finite_le_nat G.edgeFinset.card)
    fun n ⟨_, _, _, hp, hn⟩ => hn ▸ hp.isTrail.length_le_card_edgeFinset
  obtain ⟨x⟩ := N
  obtain ⟨_, ⟨⟨u

Depends on / 依赖: Eq.refl, Finite, Fintype, Fintype.ofFinite, G.Walk, G.edgeFinset.card, G.edgeSet, IsPath, Set.Finite.subset, Set.finite_le_nat, Walk.nil, edgeFinset, edgeSet, exists_maximal, finite_le_nat, hp.isTrail.length_le_card_edgeFinset, isTrail, length, length_le_card_edgeFinset, ofFinite
-/
lemma exists_isPath_forall_isPath_length_le_length (G : SimpleGraph V) [N : Nonempty V]
    [Finite G.edgeSet] :
    exists (u v : V) (p : G.Walk u v) (_ : p.IsPath),
      forall (u' v' : V) (p' : G.Walk u' v') (_ : p'.IsPath), p'.length <= p.length := by
  have := Fintype.ofFinite G.edgeSet
  let s := {n | exists (u v : V) (p : G.Walk u v), p.IsPath ∧ p.length = n}
  have : s.Finite := Set.Finite.subset (Set.finite_le_nat G.edgeFinset.card)
    fun n ⟨_, _, _, hp, hn⟩ => hn ▸ hp.isTrail.length_le_card_edgeFinset
  obtain ⟨x⟩ := N
  obtain ⟨_, ⟨⟨u, v, p, hp, _⟩, hn⟩⟩ := this.exists_maximal ⟨0, ⟨x, x, Walk.nil, by simp⟩⟩
  refine ⟨u, v, p, hp, fun u' v' p' hp' => ?_⟩
  have := hn ⟨u', v', p', hp', Eq.refl p'.length⟩
  lia


/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: V] {u v
  body: by
  rw [isPath_def]
  infer_instance

中文:
实例 [DecidableEq
  签名: V] {u v
  定义体: by
  rw [isPath_def]
  infer_instance

Depends on / 依赖: infer_instance, isPath_def
-/
instance [DecidableEq V] {u v : V} (p : G.Walk u v) : Decidable p.IsPath := by
  rw [isPath_def]
  infer_instance

/--
theorem `IsPath.length_lt` / 定理 `IsPath.length_lt`

English:
theorem IsPath.length_lt
  given: [Fintype V] {u v : V} {p : G.Walk u v} (hp : p.IsPath)
  proof: by
  rw [Nat.lt_iff_add_one_le]; rw [← length_support]
  exact hp.support_nodup.length_le_card

中文:
定理 是道路.length_lt
  条件: [有限类型 V] {u v : V} {p : G.途径 u v} (hp : p.是道路)
  证明: by
  rw [Nat.lt_iff_add_one_le]; rw [← length_support]
  exact hp.support_nodup.length_le_card

Depends on / 依赖: Nat.lt_iff_add_one_le, hp.support_nodup.length_le_card, length_le_card, length_support, lt_iff_add_one_le, support_nodup
-/
theorem IsPath.length_lt [Fintype V] {u v : V} {p : G.Walk u v} (hp : p.IsPath) :
    p.length < Fintype.card V := by
  rw [Nat.lt_iff_add_one_le]; rw [← length_support]
  exact hp.support_nodup.length_le_card

/--
lemma `IsPath.getVert_injOn` / 引理 `IsPath.getVert_injOn`

English:
lemma IsPath.getVert_injOn
  given: {p : G.Walk u v} (hp : p.IsPath)
  proof: by
  intro n hn m hm hnm
  induction p generalizing n m with
  | nil => simp_all
  | @cons v w u h p ihp =>
    simp only [length_cons, Set.mem_ofPred_eq] at hn hm hnm
    by_cases hn0 : n = 0 <;> by_cases hm0 : m = 0
    · lia
    · simp only [hn0, getVert_zero, Walk.getVert_cons p h hm0] at hnm
  

中文:
引理 是道路.getVert_injOn
  条件: {p : G.途径 u v} (hp : p.是道路)
  证明: by
  intro n hn m hm hnm
  induction p generalizing n m with
  | nil => simp_all
  | @cons v w u h p ihp =>
    simp only [length_cons, Set.mem_ofPred_eq] at hn hm hnm
    by_cases hn0 : n = 0 <;> by_cases hm0 : m = 0
    · lia
    · simp only [hn0, getVert_zero, Walk.getVert_cons p h hm0] at hnm
  

Depends on / 依赖: Set.mem_ofPred_eq, Walk.getVert_cons, Walk.mem_support_iff_exists_getVert.mpr, generalizing, getVert_cons, getVert_zero, hnm.symm, length_cons, mem_ofPred_eq, mem_support_iff_exists_getVert, p.support, support
-/
lemma IsPath.getVert_injOn {p : G.Walk u v} (hp : p.IsPath) :
    Set.InjOn p.getVert {i | i <= p.length} := by
  intro n hn m hm hnm
  induction p generalizing n m with
  | nil => simp_all
  | @cons v w u h p ihp =>
    simp only [length_cons, Set.mem_ofPred_eq] at hn hm hnm
    by_cases hn0 : n = 0 <;> by_cases hm0 : m = 0
    · lia
    · simp only [hn0, getVert_zero, Walk.getVert_cons p h hm0] at hnm
      have hvp : v ∉ p.support := by aesop
      exact (hvp (Walk.mem_support_iff_exists_getVert.mpr ⟨(m - 1), ⟨hnm.symm, by lia⟩⟩)).elim
    · simp only [hm0, Walk.getVert_cons p h hn0] at hnm
      have hvp : v ∉ p.support := by simp_all
      exact (hvp (Walk.mem_support_iff_exists_getVert.mpr ⟨(n - 1), ⟨hnm, by lia⟩⟩)).elim
    · simp only [Walk.getVert_cons _ _ hn0, Walk.getVert_cons _ _ hm0] at hnm
      have := ihp hp.of_cons (by lia : (n - 1) <= p.length)
        (by lia : (m - 1) <= p.length) hnm
      lia

/--
lemma `IsPath.getVert_eq_start_iff_of_not_nil` / 引理 `IsPath.getVert_eq_start_iff_of_not_nil`

English:
lemma IsPath.getVert_eq_start_iff_of_not_nil
  given: {i : Nat} {p : G.Walk u w} (hp : p.IsPath) (h : ¬p.Nil)
  proof: by
  refine ⟨fun h => ?_, by simp_all⟩
  by_cases h' : i <= p.length
  · apply hp.getVert_injOn (by rw [Set.mem_ofPred]; lia) (by rw [Set.mem_ofPred]; lia)
    simp [h]
  · rw [p.getVert_of_length_le (le_of_not_ge h')] at h
    subst h
    simp_all

中文:
引理 是道路.getVert_eq_start_iff_of_not_nil
  条件: {i : 自然数} {p : G.途径 u w} (hp : p.是道路) (h : ¬p.Nil)
  证明: by
  refine ⟨fun h => ?_, by simp_all⟩
  by_cases h' : i <= p.length
  · apply hp.getVert_injOn (by rw [Set.mem_ofPred]; lia) (by rw [Set.mem_ofPred]; lia)
    simp [h]
  · rw [p.getVert_of_length_le (le_of_not_ge h')] at h
    subst h
    simp_all

Depends on / 依赖: Set.mem_ofPred, getVert_injOn, getVert_of_length_le, hp.getVert_injOn, le_of_not_ge, length, mem_ofPred, p.getVert_of_length_le, p.length
-/
lemma IsPath.getVert_eq_start_iff_of_not_nil {i : Nat} {p : G.Walk u w} (hp : p.IsPath) (h : ¬p.Nil) :
    p.getVert i = u ↔ i = 0 := by
  refine ⟨fun h => ?_, by simp_all⟩
  by_cases h' : i <= p.length
  · apply hp.getVert_injOn (by rw [Set.mem_ofPred]; lia) (by rw [Set.mem_ofPred]; lia)
    simp [h]
  · rw [p.getVert_of_length_le (le_of_not_ge h')] at h
    subst h
    simp_all

/--
lemma `IsPath.getVert_eq_start_iff` / 引理 `IsPath.getVert_eq_start_iff`

English:
lemma IsPath.getVert_eq_start_iff
  given: {i : Nat} {p : G.Walk u w} (hp : p.IsPath) (hi : i <= p.length)
  proof: by
  cases p
  · simpa using hi
  · exact hp.getVert_eq_start_iff_of_not_nil not_nil_cons

中文:
引理 是道路.getVert_eq_start_iff
  条件: {i : 自然数} {p : G.途径 u w} (hp : p.是道路) (hi : i <= p.length)
  证明: by
  cases p
  · simpa using hi
  · exact hp.getVert_eq_start_iff_of_not_nil not_nil_cons

Depends on / 依赖: getVert_eq_start_iff_of_not_nil, hp.getVert_eq_start_iff_of_not_nil, not_nil_cons
-/
lemma IsPath.getVert_eq_start_iff {i : Nat} {p : G.Walk u w} (hp : p.IsPath) (hi : i <= p.length) :
    p.getVert i = u ↔ i = 0 := by
  cases p
  · simpa using hi
  · exact hp.getVert_eq_start_iff_of_not_nil not_nil_cons

/--
lemma `IsPath.getVert_eq_end_iff` / 引理 `IsPath.getVert_eq_end_iff`

English:
lemma IsPath.getVert_eq_end_iff
  given: {i : Nat} {p : G.Walk u w} (hp : p.IsPath) (hi : i <= p.length)
  proof: by
  have := hp.reverse.getVert_eq_start_iff (by lia : p.reverse.length - i <= p.reverse.length)
  simp only [length_reverse, getVert_reverse, show p.length - (p.length - i) = i by lia] at this
  rw [this]
  lia

中文:
引理 是道路.getVert_eq_end_iff
  条件: {i : 自然数} {p : G.途径 u w} (hp : p.是道路) (hi : i <= p.length)
  证明: by
  have := hp.reverse.getVert_eq_start_iff (by lia : p.reverse.length - i <= p.reverse.length)
  simp only [length_reverse, getVert_reverse, show p.length - (p.length - i) = i by lia] at this
  rw [this]
  lia

Depends on / 依赖: getVert_eq_start_iff, getVert_reverse, hp.reverse.getVert_eq_start_iff, length, length_reverse, p.length, p.reverse.length, reverse
-/
lemma IsPath.getVert_eq_end_iff {i : Nat} {p : G.Walk u w} (hp : p.IsPath) (hi : i <= p.length) :
    p.getVert i = w ↔ i = p.length := by
  have := hp.reverse.getVert_eq_start_iff (by lia : p.reverse.length - i <= p.reverse.length)
  simp only [length_reverse, getVert_reverse, show p.length - (p.length - i) = i by lia] at this
  rw [this]
  lia

/--
lemma `IsPath.getVert_injOn_iff` / 引理 `IsPath.getVert_injOn_iff`

English:
lemma IsPath.getVert_injOn_iff
  given: (p : G.Walk u v)
  statement: Set.InjOn p.getVert {i | i <= p.length} ↔
  proof: by
  refine ⟨?_, fun a => a.getVert_injOn⟩
  induction p with
  | nil => simp
  | cons h q ih =>
    intro hinj
    rw [cons_isPath_iff]
    refine ⟨ih (by
      intro n hn m hm hnm
      simp only [Set.mem_ofPred_eq] at hn hm
      have := hinj
        (by rw [length_cons]; lia : n + 1 <= (q.cons h

中文:
引理 是道路.getVert_injOn_iff
  条件: (p : G.途径 u v)
  结论: 集合.单射限制 p.getVert {i | i <= p.length} ↔
  证明: by
  refine ⟨?_, fun a => a.getVert_injOn⟩
  induction p with
  | nil => simp
  | cons h q ih =>
    intro hinj
    rw [cons_isPath_iff]
    refine ⟨ih (by
      intro n hn m hm hnm
      simp only [Set.mem_ofPred_eq] at hn hm
      have := hinj
        (by rw [length_cons]; lia : n + 1 <= (q.cons h

Depends on / 依赖: Set.mem_ofPred_eq, a.getVert_injOn, cons_isPath_iff, getVert_cons, getVert_injOn, length, length_cons, mem_ofPred_eq, mem_support_iff_exists_getVert, mem_support_iff_exists_getVert.mp, q.cons
-/
lemma IsPath.getVert_injOn_iff (p : G.Walk u v) : Set.InjOn p.getVert {i | i <= p.length} ↔
    p.IsPath := by
  refine ⟨?_, fun a => a.getVert_injOn⟩
  induction p with
  | nil => simp
  | cons h q ih =>
    intro hinj
    rw [cons_isPath_iff]
    refine ⟨ih (by
      intro n hn m hm hnm
      simp only [Set.mem_ofPred_eq] at hn hm
      have := hinj
        (by rw [length_cons]; lia : n + 1 <= (q.cons h).length)
        (by rw [length_cons]; lia : m + 1 <= (q.cons h).length)
        (by simpa [getVert_cons] using hnm)
      lia), fun h' => ?_⟩
    obtain ⟨n, ⟨hn, hnl⟩⟩ := mem_support_iff_exists_getVert.mp h'
    have := hinj
      (by rw [length_cons]; lia : (n + 1) <= (q.cons h).length)
      (by lia : 0 <= (q.cons h).length)
      (by rwa [getVert_cons _ _ n.add_one_ne_zero, getVert_zero])
    lia

/--
theorem `IsPath.eq_snd_of_mem_edges` / 定理 `IsPath.eq_snd_of_mem_edges`

English:
theorem IsPath.eq_snd_of_mem_edges
  given: {p : G.Walk u v} (hp : p.IsPath) (hmem : s(u, w) in p.edges)
  proof: by
have hnil := edges_eq_nil.not.mp List.ne_nil_of_mem hmem
  rw [← cons_tail_eq _ hnil]; rw [edges_cons]; rw [List.mem_cons]; rw [Sym2.eq]; rw [Sym2.rel_iff'] at hmem
  have : u ∉ p.tail.support := by induction p <;> simp_all
  grind [fst_mem_support_of_mem_edges]

中文:
定理 是道路.eq_snd_of_mem_edges
  条件: {p : G.途径 u v} (hp : p.是道路) (hmem : s(u, w) in p.edges)
  证明: by
have hnil := edges_eq_nil.not.mp List.ne_nil_of_mem hmem
  rw [← cons_tail_eq _ hnil]; rw [edges_cons]; rw [List.mem_cons]; rw [Sym2.eq]; rw [Sym2.rel_iff'] at hmem
  have : u ∉ p.tail.support := by induction p <;> simp_all
  grind [fst_mem_support_of_mem_edges]

Depends on / 依赖: List.mem_cons, List.ne_nil_of_mem, Sym2.eq, Sym2.rel_iff, cons_tail_eq, edges_cons, edges_eq_nil, edges_eq_nil.not.mp, fst_mem_support_of_mem_edges, mem_cons, ne_nil_of_mem, p.tail.support, rel_iff, support
-/
theorem IsPath.eq_snd_of_mem_edges {p : G.Walk u v} (hp : p.IsPath) (hmem : s(u, w) in p.edges) :
    w = p.snd := by
have hnil := edges_eq_nil.not.mp List.ne_nil_of_mem hmem
  rw [← cons_tail_eq _ hnil]; rw [edges_cons]; rw [List.mem_cons]; rw [Sym2.eq]; rw [Sym2.rel_iff'] at hmem
  have : u ∉ p.tail.support := by induction p <;> simp_all
  grind [fst_mem_support_of_mem_edges]

/--
theorem `IsPath.eq_penultimate_of_mem_edges` / 定理 `IsPath.eq_penultimate_of_mem_edges`

English:
theorem IsPath.eq_penultimate_of_mem_edges
  statement: {p : G.Walk u v} (hp : p.IsPath)
  proof: by
.eq_snd_of_mem_edges (w := w) .mpr hp simpa [hmem] using isPath_reverse_iff p

中文:
定理 是道路.eq_penultimate_of_mem_edges
  结论: {p : G.途径 u v} (hp : p.是道路)
  证明: by
.eq_snd_of_mem_edges (w := w) .mpr hp simpa [hmem] using isPath_reverse_iff p

Depends on / 依赖: eq_snd_of_mem_edges, isPath_reverse_iff
-/
theorem IsPath.eq_penultimate_of_mem_edges {p : G.Walk u v} (hp : p.IsPath)
    (hmem : s(v, w) in p.edges) : w = p.penultimate := by
.eq_snd_of_mem_edges (w := w) .mpr hp simpa [hmem] using isPath_reverse_iff p

/--
theorem `IsPath.injOn_support_of_isPath_map` / 定理 `IsPath.injOn_support_of_isPath_map`

English:
theorem IsPath.injOn_support_of_isPath_map
  given: (h : (p.map f).IsPath)
  proof: by
  intro u hu v hv hf
  obtain ⟨u, rfl⟩ := List.get_of_mem hu
  obtain ⟨v, rfl⟩ := List.get_of_mem hv
  congr
  have := List.nodup_iff_injective_getElem.mp h.support_nodup
  rw! (castMode := .all) [support_map, List.length_map] at this
  apply this
  simpa

中文:
定理 是道路.injOn_support_of_isPath_map
  条件: (h : (p.map f).是道路)
  证明: by
  intro u hu v hv hf
  obtain ⟨u, rfl⟩ := List.get_of_mem hu
  obtain ⟨v, rfl⟩ := List.get_of_mem hv
  congr
  have := List.nodup_iff_injective_getElem.mp h.support_nodup
  rw! (castMode := .all) [support_map, List.length_map] at this
  apply this
  simpa

Depends on / 依赖: List.get_of_mem, List.length_map, List.nodup_iff_injective_getElem.mp, castMode, get_of_mem, h.support_nodup, length_map, nodup_iff_injective_getElem, support_map, support_nodup
-/
theorem IsPath.injOn_support_of_isPath_map (h : (p.map f).IsPath) :
    Set.InjOn f {w | w in p.support} := by
  intro u hu v hv hf
  obtain ⟨u, rfl⟩ := List.get_of_mem hu
  obtain ⟨v, rfl⟩ := List.get_of_mem hv
  congr
  have := List.nodup_iff_injective_getElem.mp h.support_nodup
  rw! (castMode := .all) [support_map, List.length_map] at this
  apply this
  simpa


-- TODO: These results could possibly be less laborious with a periodic function getCycleVert
/--
lemma `IsCycle.getVert_injOn` / 引理 `IsCycle.getVert_injOn`

English:
lemma IsCycle.getVert_injOn
  given: {p : G.Walk u u} (hpc : p.IsCycle)
  proof: by
  rw [← p.cons_tail_eq hpc.not_nil] at hpc
  intro n hn m hm hnm
  rw [← SimpleGraph.Walk.length_tail_add_one
    (p.not_nil_of_tail_not_nil (not_nil_of_isCycle_cons hpc))]; rw [Set.mem_ofPred] at hn hm
  have := ((Walk.cons_isCycle_iff _ _).mp hpc).1.getVert_injOn
    (by lia : n - 1 <= p.tail.l

中文:
引理 是环.getVert_injOn
  条件: {p : G.途径 u u} (hpc : p.是环)
  证明: by
  rw [← p.cons_tail_eq hpc.not_nil] at hpc
  intro n hn m hm hnm
  rw [← SimpleGraph.Walk.length_tail_add_one
    (p.not_nil_of_tail_not_nil (not_nil_of_isCycle_cons hpc))]; rw [Set.mem_ofPred] at hn hm
  have := ((Walk.cons_isCycle_iff _ _).mp hpc).1.getVert_injOn
    (by lia : n - 1 <= p.tail.l

Depends on / 依赖: Set.mem_ofPred, SimpleGraph, SimpleGraph.Walk.length_tail_add_one, Walk.cons_isCycle_iff, cons_isCycle_iff, cons_tail_eq, getVert_injOn, hpc.not_nil, length, length_tail_add_one, mem_ofPred, not_nil, not_nil_of_isCycle_cons, not_nil_of_tail_not_nil, p.cons_tail_eq, p.not_nil_of_tail_not_nil, p.tail.length
-/
lemma IsCycle.getVert_injOn {p : G.Walk u u} (hpc : p.IsCycle) :
    Set.InjOn p.getVert {i | 1 <= i ∧ i <= p.length} := by
  rw [← p.cons_tail_eq hpc.not_nil] at hpc
  intro n hn m hm hnm
  rw [← SimpleGraph.Walk.length_tail_add_one
    (p.not_nil_of_tail_not_nil (not_nil_of_isCycle_cons hpc))]; rw [Set.mem_ofPred] at hn hm
  have := ((Walk.cons_isCycle_iff _ _).mp hpc).1.getVert_injOn
    (by lia : n - 1 <= p.tail.length) (by lia : m - 1 <= p.tail.length)
    (by simp_all)
  lia

/--
lemma `IsCycle.getVert_injOn'` / 引理 `IsCycle.getVert_injOn'`

English:
lemma IsCycle.getVert_injOn'
  given: {p : G.Walk u u} (hpc : p.IsCycle)
  proof: by
  intro n hn m hm hnm
  simp only [Set.mem_ofPred_eq] at *
  have := hpc.three_le_length
  have : p.length - n = p.length - m := Walk.length_reverse _ ▸ hpc.reverse.getVert_injOn
    (by simp only [Walk.length_reverse, Set.mem_ofPred_eq]; lia)
    (by simp only [Walk.length_reverse, Set.mem_ofPre

中文:
引理 是环.getVert_injOn'
  条件: {p : G.途径 u u} (hpc : p.是环)
  证明: by
  intro n hn m hm hnm
  simp only [Set.mem_ofPred_eq] at *
  have := hpc.three_le_length
  have : p.length - n = p.length - m := Walk.length_reverse _ ▸ hpc.reverse.getVert_injOn
    (by simp only [Walk.length_reverse, Set.mem_ofPred_eq]; lia)
    (by simp only [Walk.length_reverse, Set.mem_ofPre

Depends on / 依赖: Set.mem_ofPred_eq, Walk.getVert_reverse, Walk.length_reverse, getVert_injOn, getVert_reverse, hpc.reverse.getVert_injOn, hpc.three_le_length, length, length_reverse, mem_ofPred_eq, p.length, reverse, three_le_length
-/
lemma IsCycle.getVert_injOn' {p : G.Walk u u} (hpc : p.IsCycle) :
    Set.InjOn p.getVert {i | i <= p.length - 1} := by
  intro n hn m hm hnm
  simp only [Set.mem_ofPred_eq] at *
  have := hpc.three_le_length
  have : p.length - n = p.length - m := Walk.length_reverse _ ▸ hpc.reverse.getVert_injOn
    (by simp only [Walk.length_reverse, Set.mem_ofPred_eq]; lia)
    (by simp only [Walk.length_reverse, Set.mem_ofPred_eq]; lia)
    (by simp [Walk.getVert_reverse, show p.length - (p.length - n) = n by lia, hnm,
      show p.length - (p.length - m) = m by lia])
  lia

/--
lemma `IsCycle.snd_ne_penultimate` / 引理 `IsCycle.snd_ne_penultimate`

English:
lemma IsCycle.snd_ne_penultimate
  given: {p : G.Walk u u} (hp : p.IsCycle)
  statement: p.snd != p.penultimate
  proof: by
  intro h
  have := hp.three_le_length
  apply hp.getVert_injOn (by simp; lia) (by simp; lia) at h
  lia

中文:
引理 是环.snd_ne_penultimate
  条件: {p : G.途径 u u} (hp : p.是环)
  结论: p.snd != p.penultimate
  证明: by
  intro h
  have := hp.three_le_length
  apply hp.getVert_injOn (by simp; lia) (by simp; lia) at h
  lia

Depends on / 依赖: getVert_injOn, hp.getVert_injOn, hp.three_le_length, three_le_length
-/
lemma IsCycle.snd_ne_penultimate {p : G.Walk u u} (hp : p.IsCycle) : p.snd != p.penultimate := by
  intro h
  have := hp.three_le_length
  apply hp.getVert_injOn (by simp; lia) (by simp; lia) at h
  lia

/--
lemma `IsCycle.getVert_endpoint_iff` / 引理 `IsCycle.getVert_endpoint_iff`

English:
lemma IsCycle.getVert_endpoint_iff
  given: {i : Nat} {p : G.Walk u u} (hpc : p.IsCycle) (hl : i <= p.length)
  proof: by
  refine ⟨?_, by aesop⟩
  rw [or_iff_not_imp_left]
  intro h hi
  exact hpc.getVert_injOn (by simp only [Set.mem_ofPred_eq]; lia)
    (by simp only [Set.mem_ofPred_eq]; lia) (h.symm ▸ (Walk.getVert_length p).symm)

中文:
引理 是环.getVert_endpoint_iff
  条件: {i : 自然数} {p : G.途径 u u} (hpc : p.是环) (hl : i <= p.length)
  证明: by
  refine ⟨?_, by aesop⟩
  rw [or_iff_not_imp_left]
  intro h hi
  exact hpc.getVert_injOn (by simp only [Set.mem_ofPred_eq]; lia)
    (by simp only [Set.mem_ofPred_eq]; lia) (h.symm ▸ (Walk.getVert_length p).symm)

Depends on / 依赖: Set.mem_ofPred_eq, Walk.getVert_length, getVert_injOn, getVert_length, h.symm, hpc.getVert_injOn, mem_ofPred_eq, or_iff_not_imp_left
-/
lemma IsCycle.getVert_endpoint_iff {i : Nat} {p : G.Walk u u} (hpc : p.IsCycle) (hl : i <= p.length) :
    p.getVert i = u ↔ i = 0 ∨ i = p.length := by
  refine ⟨?_, by aesop⟩
  rw [or_iff_not_imp_left]
  intro h hi
  exact hpc.getVert_injOn (by simp only [Set.mem_ofPred_eq]; lia)
    (by simp only [Set.mem_ofPred_eq]; lia) (h.symm ▸ (Walk.getVert_length p).symm)

/--
lemma `IsCycle.getVert_sub_one_ne_getVert_add_one` / 引理 `IsCycle.getVert_sub_one_ne_getVert_add_one`

English:
lemma IsCycle.getVert_sub_one_ne_getVert_add_one
  statement: {i : Nat} {p : G.Walk u u} (hpc : p.IsCycle)
  proof: by
  intro h'
  have hl := hpc.three_le_length
  by_cases hi' : i >= p.length - 1
  · rw [p.getVert_of_length_le (by lia : p.length <= i + 1),
      hpc.getVert_endpoint_iff (by lia)] at h'
    lia
  have := hpc.getVert_injOn' (by simp only [Set.mem_ofPred_eq, Nat.sub_le_iff_le_add]; lia)
    (by si

中文:
引理 是环.getVert_sub_one_ne_getVert_add_one
  结论: {i : 自然数} {p : G.途径 u u} (hpc : p.是环)
  证明: by
  intro h'
  have hl := hpc.three_le_length
  by_cases hi' : i >= p.length - 1
  · rw [p.getVert_of_length_le (by lia : p.length <= i + 1),
      hpc.getVert_endpoint_iff (by lia)] at h'
    lia
  have := hpc.getVert_injOn' (by simp only [Set.mem_ofPred_eq, Nat.sub_le_iff_le_add]; lia)
    (by si

Depends on / 依赖: Nat.sub_le_iff_le_add, Set.mem_ofPred_eq, getVert_endpoint_iff, getVert_injOn, getVert_of_length_le, hpc.getVert_endpoint_iff, hpc.getVert_injOn, hpc.three_le_length, length, mem_ofPred_eq, p.getVert_of_length_le, p.length, sub_le_iff_le_add, three_le_length
-/
lemma IsCycle.getVert_sub_one_ne_getVert_add_one {i : Nat} {p : G.Walk u u} (hpc : p.IsCycle)
    (h : i <= p.length) : p.getVert (i - 1) != p.getVert (i + 1) := by
  intro h'
  have hl := hpc.three_le_length
  by_cases hi' : i >= p.length - 1
  · rw [p.getVert_of_length_le (by lia : p.length <= i + 1),
      hpc.getVert_endpoint_iff (by lia)] at h'
    lia
  have := hpc.getVert_injOn' (by simp only [Set.mem_ofPred_eq, Nat.sub_le_iff_le_add]; lia)
    (by simp only [Set.mem_ofPred_eq]; lia) h'
  lia

/--
theorem `isCycle_iff_isPath_tail_and_le_length` / 定理 `isCycle_iff_isPath_tail_and_le_length`

English:
theorem isCycle_iff_isPath_tail_and_le_length
  given: {p : G.Walk u u}
  proof: by
  refine ⟨fun h => ⟨h.isPath_tail, h.three_le_length⟩, fun ⟨h₁, h₂⟩ => ?_⟩
  cases p with
  | nil => simp_all
  | cons h' p =>
    simp only [getVert_cons_succ, tail_cons, isPath_copy, length_cons] at h₁ h₂
.mpr ⟨h₁, fun hh => ?_⟩ refine p.cons_isCycle_iff h'
    have : p.support[0] = p.support[p

中文:
定理 isCycle_iff_isPath_tail_and_le_length
  条件: {p : G.途径 u u}
  证明: by
  refine ⟨fun h => ⟨h.isPath_tail, h.three_le_length⟩, fun ⟨h₁, h₂⟩ => ?_⟩
  cases p with
  | nil => simp_all
  | cons h' p =>
    simp only [getVert_cons_succ, tail_cons, isPath_copy, length_cons] at h₁ h₂
.mpr ⟨h₁, fun hh => ?_⟩ refine p.cons_isCycle_iff h'
    have : p.support[0] = p.support[p

Depends on / 依赖: List.head_eq_getElem_zero, cons_isCycle_iff, eq_penultimate_of_mem_edges, getVert_cons_succ, h.isPath_tail, h.three_le_length, head_eq_getElem_zero, isPath_copy, isPath_iff_injective_get_support, isPath_tail, length, length_cons, p.cons_isCycle_iff, p.isPath_iff_injective_get_support.mp, p.length, p.support, support, tail_cons, three_le_length
-/
theorem isCycle_iff_isPath_tail_and_le_length {p : G.Walk u u} :
    p.IsCycle ↔ p.tail.IsPath ∧ 3 <= p.length := by
  refine ⟨fun h => ⟨h.isPath_tail, h.three_le_length⟩, fun ⟨h₁, h₂⟩ => ?_⟩
  cases p with
  | nil => simp_all
  | cons h' p =>
    simp only [getVert_cons_succ, tail_cons, isPath_copy, length_cons] at h₁ h₂
.mpr ⟨h₁, fun hh => ?_⟩ refine p.cons_isCycle_iff h'
    have : p.support[0] = p.support[p.length - 1] := by
      simp [← List.head_eq_getElem_zero, h₁.eq_penultimate_of_mem_edges hh]
    have := p.isPath_iff_injective_get_support.mp h₁ this
    lia

/-! ### Walk decompositions -/

section WalkDecomp

variable [DecidableEq V]

/--
theorem `IsTrail.takeUntil` / 定理 `IsTrail.takeUntil`

English:
theorem IsTrail.takeUntil
  statement: {u v w : V} {p : G.Walk v w} (hc : p.IsTrail)
  proof: IsTrail.of_append_left (q := p.dropUntil u h) (by rwa [← take_spec _ h] at hc)

中文:
定理 是Trail.takeUntil
  结论: {u v w : V} {p : G.途径 v w} (hc : p.是Trail)
  证明: IsTrail.of_append_left (q := p.dropUntil u h) (by rwa [← take_spec _ h] at hc)
-/
protected theorem IsTrail.takeUntil {u v w : V} {p : G.Walk v w} (hc : p.IsTrail)
    (h : u in p.support) : (p.takeUntil u h).IsTrail :=
  IsTrail.of_append_left (q := p.dropUntil u h) (by rwa [← take_spec _ h] at hc)

/--
theorem `IsTrail.dropUntil` / 定理 `IsTrail.dropUntil`

English:
theorem IsTrail.dropUntil
  statement: {u v w : V} {p : G.Walk v w} (hc : p.IsTrail)
  proof: IsTrail.of_append_right (p := p.takeUntil u h) (q := p.dropUntil u h)
    (by rwa [← take_spec _ h] at hc)

中文:
定理 是Trail.dropUntil
  结论: {u v w : V} {p : G.途径 v w} (hc : p.是Trail)
  证明: IsTrail.of_append_right (p := p.takeUntil u h) (q := p.dropUntil u h)
    (by rwa [← take_spec _ h] at hc)
-/
protected theorem IsTrail.dropUntil {u v w : V} {p : G.Walk v w} (hc : p.IsTrail)
    (h : u in p.support) : (p.dropUntil u h).IsTrail :=
  IsTrail.of_append_right (p := p.takeUntil u h) (q := p.dropUntil u h)
    (by rwa [← take_spec _ h] at hc)

/--
theorem `IsPath.takeUntil` / 定理 `IsPath.takeUntil`

English:
theorem IsPath.takeUntil
  statement: {u v w : V} {p : G.Walk v w} (hc : p.IsPath)
  proof: IsPath.of_append_left (q := p.dropUntil u h) (by rwa [← take_spec _ h] at hc)

中文:
定理 是道路.takeUntil
  结论: {u v w : V} {p : G.途径 v w} (hc : p.是道路)
  证明: IsPath.of_append_left (q := p.dropUntil u h) (by rwa [← take_spec _ h] at hc)
-/
protected theorem IsPath.takeUntil {u v w : V} {p : G.Walk v w} (hc : p.IsPath)
    (h : u in p.support) : (p.takeUntil u h).IsPath :=
  IsPath.of_append_left (q := p.dropUntil u h) (by rwa [← take_spec _ h] at hc)

/--
theorem `IsPath.dropUntil` / 定理 `IsPath.dropUntil`

English:
theorem IsPath.dropUntil
  statement: {u v w : V} {p : G.Walk v w} (hc : p.IsPath)
  proof: IsPath.of_append_right (p := p.takeUntil u h) (q := p.dropUntil u h)
    (by rwa [← take_spec _ h] at hc)

中文:
定理 是道路.dropUntil
  结论: {u v w : V} {p : G.途径 v w} (hc : p.是道路)
  证明: IsPath.of_append_right (p := p.takeUntil u h) (q := p.dropUntil u h)
    (by rwa [← take_spec _ h] at hc)
-/
protected theorem IsPath.dropUntil {u v w : V} {p : G.Walk v w} (hc : p.IsPath)
    (h : u in p.support) : (p.dropUntil u h).IsPath :=
  IsPath.of_append_right (p := p.takeUntil u h) (q := p.dropUntil u h)
    (by rwa [← take_spec _ h] at hc)

/--
lemma `IsTrail.disjoint_edges_takeUntil_dropUntil` / 引理 `IsTrail.disjoint_edges_takeUntil_dropUntil`

English:
lemma IsTrail.disjoint_edges_takeUntil_dropUntil
  statement: {x : V} {w : G.Walk u v} (hw : w.IsTrail)
  proof: List.disjoint_of_nodup_append by simpa [← edges_append] using hw.edges_nodup

中文:
引理 是Trail.disjoint_edges_takeUntil_dropUntil
  结论: {x : V} {w : G.途径 u v} (hw : w.是Trail)
  证明: List.disjoint_of_nodup_append by simpa [← edges_append] using hw.edges_nodup

Depends on / 依赖: List.disjoint_of_nodup_append, disjoint_of_nodup_append, edges_append, edges_nodup, hw.edges_nodup
-/
lemma IsTrail.disjoint_edges_takeUntil_dropUntil {x : V} {w : G.Walk u v} (hw : w.IsTrail)
    (hx : x in w.support) : (w.takeUntil x hx).edges.Disjoint (w.dropUntil x hx).edges :=
List.disjoint_of_nodup_append by simpa [← edges_append] using hw.edges_nodup

/--
lemma `isTrail_rotate` / 引理 `isTrail_rotate`

English:
lemma isTrail_rotate
  given: {c : G.Walk v v} (hu : u in c.support)
  proof: by
  rw [isTrail_def]; rw [isTrail_def]; rw [(c.rotate_edges u hu).perm.nodup_iff]

中文:
引理 isTrail_rotate
  条件: {c : G.途径 v v} (hu : u in c.support)
  证明: by
  rw [isTrail_def]; rw [isTrail_def]; rw [(c.rotate_edges u hu).perm.nodup_iff]
-/
@[simp] lemma isTrail_rotate {c : G.Walk v v} (hu : u in c.support) :
    (c.rotate u hu).IsTrail ↔ c.IsTrail := by
  rw [isTrail_def]; rw [isTrail_def]; rw [(c.rotate_edges u hu).perm.nodup_iff]

/--
lemma `isCircuit_rotate` / 引理 `isCircuit_rotate`

English:
lemma isCircuit_rotate
  given: {c : G.Walk v v} (hu : u in c.support)
  proof: by simp [isCircuit_def]

中文:
引理 isCircuit_rotate
  条件: {c : G.途径 v v} (hu : u in c.support)
  证明: by simp [isCircuit_def]
-/
@[simp] lemma isCircuit_rotate {c : G.Walk v v} (hu : u in c.support) :
    (c.rotate u hu).IsCircuit ↔ c.IsCircuit := by simp [isCircuit_def]

/--
lemma `isCycle_rotate` / 引理 `isCycle_rotate`

English:
lemma isCycle_rotate
  given: {c : G.Walk v v} (hu : u in c.support)
  proof: by simp [isCycle_def, (support_rotate ..).perm.nodup_iff]

protected alias ⟨IsTrail.of_rotate, IsTrail.rotate⟩ := isTrail_rotate
protected alias ⟨IsCircuit.of_rotate, IsCircuit.rotate⟩ := isCircuit_rotate
protected alias ⟨IsCycle.of_rotate, IsCycle.rotate⟩ := isCycle_rotate

中文:
引理 isCycle_rotate
  条件: {c : G.途径 v v} (hu : u in c.support)
  证明: by simp [isCycle_def, (support_rotate ..).perm.nodup_iff]

protected alias ⟨IsTrail.of_rotate, IsTrail.rotate⟩ := isTrail_rotate
protected alias ⟨IsCircuit.of_rotate, IsCircuit.rotate⟩ := isCircuit_rotate
protected alias ⟨IsCycle.of_rotate, IsCycle.rotate⟩ := isCycle_rotate
-/
@[simp] lemma isCycle_rotate {c : G.Walk v v} (hu : u in c.support) :
    (c.rotate u hu).IsCycle ↔ c.IsCycle := by simp [isCycle_def, (support_rotate ..).perm.nodup_iff]

protected alias ⟨IsTrail.of_rotate, IsTrail.rotate⟩ := isTrail_rotate
protected alias ⟨IsCircuit.of_rotate, IsCircuit.rotate⟩ := isCircuit_rotate
protected alias ⟨IsCycle.of_rotate, IsCycle.rotate⟩ := isCycle_rotate

/--
lemma `IsCycle.isPath_takeUntil` / 引理 `IsCycle.isPath_takeUntil`

English:
lemma IsCycle.isPath_takeUntil
  given: {c : G.Walk v v} (hc : c.IsCycle) (h : w in c.support)
  proof: by
  by_cases hvw : v = w
  · subst hvw
    simp
  rw [← isCycle_reverse]; rw [← take_spec c h]; rw [reverse_append] at hc
  exact (c.takeUntil w h).isPath_reverse_iff.mp (hc.isPath_of_append_right (not_nil_of_ne hvw))

中文:
引理 是环.isPath_takeUntil
  条件: {c : G.途径 v v} (hc : c.是环) (h : w in c.support)
  证明: by
  by_cases hvw : v = w
  · subst hvw
    simp
  rw [← isCycle_reverse]; rw [← take_spec c h]; rw [reverse_append] at hc
  exact (c.takeUntil w h).isPath_reverse_iff.mp (hc.isPath_of_append_right (not_nil_of_ne hvw))

Depends on / 依赖: c.takeUntil, hc.isPath_of_append_right, isCycle_reverse, isPath_of_append_right, isPath_reverse_iff, isPath_reverse_iff.mp, not_nil_of_ne, reverse_append, takeUntil, take_spec
-/
lemma IsCycle.isPath_takeUntil {c : G.Walk v v} (hc : c.IsCycle) (h : w in c.support) :
    (c.takeUntil w h).IsPath := by
  by_cases hvw : v = w
  · subst hvw
    simp
  rw [← isCycle_reverse]; rw [← take_spec c h]; rw [reverse_append] at hc
  exact (c.takeUntil w h).isPath_reverse_iff.mp (hc.isPath_of_append_right (not_nil_of_ne hvw))

/--
theorem `IsCycle.count_support` / 定理 `IsCycle.count_support`

English:
theorem IsCycle.count_support
  given: {c : G.Walk v v} (hc : c.IsCycle)
  statement: c.support.count v = 2
  proof: by
have := List.count_eq_one_of_mem hc.support_nodup c.end_mem_tail_support hc.not_nil
  have := c.head_support ▸ List.head?_eq_some_head c.support_ne_nil
  grind

中文:
定理 是环.count_support
  条件: {c : G.途径 v v} (hc : c.是环)
  结论: c.support.count v = 2
  证明: by
have := List.count_eq_one_of_mem hc.support_nodup c.end_mem_tail_support hc.not_nil
  have := c.head_support ▸ List.head?_eq_some_head c.support_ne_nil
  grind

Depends on / 依赖: List.count_eq_one_of_mem, List.head, _eq_some_head, c.end_mem_tail_support, c.head_support, c.support_ne_nil, count_eq_one_of_mem, end_mem_tail_support, hc.not_nil, hc.support_nodup, head_support, not_nil, support_ne_nil, support_nodup
-/
theorem IsCycle.count_support {c : G.Walk v v} (hc : c.IsCycle) : c.support.count v = 2 := by
have := List.count_eq_one_of_mem hc.support_nodup c.end_mem_tail_support hc.not_nil
  have := c.head_support ▸ List.head?_eq_some_head c.support_ne_nil
  grind

/--
theorem `IsCycle.count_support_of_mem` / 定理 `IsCycle.count_support_of_mem`

English:
theorem IsCycle.count_support_of_mem
  statement: {c : G.Walk v v} (hc : c.IsCycle) (hu : u in c.support)
  proof: by
have := List.eq_or_mem_of_mem_cons List.cons_head_tail c.support_ne_nil ▸ hu
have := List.count_eq_one_of_mem hc.support_nodup this.resolve_left head_support _ ▸ hv
  have := c.head_support ▸ List.head?_eq_some_head c.support_ne_nil
  grind

中文:
定理 是环.count_support_of_mem
  结论: {c : G.途径 v v} (hc : c.是环) (hu : u in c.support)
  证明: by
have := List.eq_or_mem_of_mem_cons List.cons_head_tail c.support_ne_nil ▸ hu
have := List.count_eq_one_of_mem hc.support_nodup this.resolve_left head_support _ ▸ hv
  have := c.head_support ▸ List.head?_eq_some_head c.support_ne_nil
  grind

Depends on / 依赖: List.cons_head_tail, List.count_eq_one_of_mem, List.eq_or_mem_of_mem_cons, List.head, _eq_some_head, c.head_support, c.support_ne_nil, cons_head_tail, count_eq_one_of_mem, eq_or_mem_of_mem_cons, hc.support_nodup, head_support, resolve_left, support_ne_nil, support_nodup, this.resolve_left
-/
theorem IsCycle.count_support_of_mem {c : G.Walk v v} (hc : c.IsCycle) (hu : u in c.support)
    (hv : u != v) : c.support.count u = 1 := by
have := List.eq_or_mem_of_mem_cons List.cons_head_tail c.support_ne_nil ▸ hu
have := List.count_eq_one_of_mem hc.support_nodup this.resolve_left head_support _ ▸ hv
  have := c.head_support ▸ List.head?_eq_some_head c.support_ne_nil
  grind

/--
lemma `endpoint_notMem_support_takeUntil` / 引理 `endpoint_notMem_support_takeUntil`

English:
lemma endpoint_notMem_support_takeUntil
  statement: {p : G.Walk u v} (hp : p.IsPath) (hw : w in p.support)
  proof: by
  intro hv
  rw [Walk.mem_support_iff_exists_getVert] at hv
  obtain ⟨n, ⟨hn, hnl⟩⟩ := hv
  rw [getVert_takeUntil hw hnl] at hn
  have := p.length_takeUntil_lt_length hw h.symm
  have : n = p.length := hp.getVert_injOn (by rw [Set.mem_ofPred]; lia) (by simp)
    (hn.symm ▸ p.getVert_length.symm)


中文:
引理 endpoint_notMem_support_takeUntil
  结论: {p : G.途径 u v} (hp : p.是道路) (hw : w in p.support)
  证明: by
  intro hv
  rw [Walk.mem_support_iff_exists_getVert] at hv
  obtain ⟨n, ⟨hn, hnl⟩⟩ := hv
  rw [getVert_takeUntil hw hnl] at hn
  have := p.length_takeUntil_lt_length hw h.symm
  have : n = p.length := hp.getVert_injOn (by rw [Set.mem_ofPred]; lia) (by simp)
    (hn.symm ▸ p.getVert_length.symm)


Depends on / 依赖: Set.mem_ofPred, Walk.mem_support_iff_exists_getVert, getVert_injOn, getVert_length, getVert_takeUntil, h.symm, hn.symm, hp.getVert_injOn, length, length_takeUntil_lt_length, mem_ofPred, mem_support_iff_exists_getVert, p.getVert_length.symm, p.length, p.length_takeUntil_lt_length
-/
lemma endpoint_notMem_support_takeUntil {p : G.Walk u v} (hp : p.IsPath) (hw : w in p.support)
    (h : v != w) : v ∉ (p.takeUntil w hw).support := by
  intro hv
  rw [Walk.mem_support_iff_exists_getVert] at hv
  obtain ⟨n, ⟨hn, hnl⟩⟩ := hv
  rw [getVert_takeUntil hw hnl] at hn
  have := p.length_takeUntil_lt_length hw h.symm
  have : n = p.length := hp.getVert_injOn (by rw [Set.mem_ofPred]; lia) (by simp)
    (hn.symm ▸ p.getVert_length.symm)
  lia

end WalkDecomp

/--
theorem `isPath_iff_isSubwalk_imp_nil` / 定理 `isPath_iff_isSubwalk_imp_nil`

English:
theorem isPath_iff_isSubwalk_imp_nil
  given: {u v} {p : G.Walk u v}
  proof: by
  refine ⟨fun hp v w hwp => ?_, fun h => .mk' ?_⟩
  · simp [w.isPath_iff_nil.mp <| isPath_of_isSubwalk hwp hp]
  · refine List.pairwise_iff_getElem.mpr fun i j _ _ _ _ => ?_
.drop i let p' := p.take j
    have : ¬p'.Nil := by grind [nil_drop_iff, take_length]
.trans p.isSubwalk_take j have : p'.I

中文:
定理 isPath_iff_isSubwalk_imp_nil
  条件: {u v} {p : G.途径 u v}
  证明: by
  refine ⟨fun hp v w hwp => ?_, fun h => .mk' ?_⟩
  · simp [w.isPath_iff_nil.mp <| isPath_of_isSubwalk hwp hp]
  · refine List.pairwise_iff_getElem.mpr fun i j _ _ _ _ => ?_
.drop i let p' := p.take j
    have : ¬p'.Nil := by grind [nil_drop_iff, take_length]
.trans p.isSubwalk_take j have : p'.I

Depends on / 依赖: IsSubwalk, List.pairwise_iff_getElem.mpr, getVert_eq_support_getElem, isPath_iff_nil, isPath_of_isSubwalk, isSubwalk_drop, isSubwalk_take, nil_drop_iff, p.isSubwalk_take, p.take, pairwise_iff_getElem, take_getVert, take_length, w.isPath_iff_nil.mp
-/
theorem isPath_iff_isSubwalk_imp_nil {u v} {p : G.Walk u v} :
    p.IsPath ↔ forall (v : V) (w : G.Walk v v), w.IsSubwalk p -> w.Nil := by
  refine ⟨fun hp v w hwp => ?_, fun h => .mk' ?_⟩
  · simp [w.isPath_iff_nil.mp <| isPath_of_isSubwalk hwp hp]
  · refine List.pairwise_iff_getElem.mpr fun i j _ _ _ _ => ?_
.drop i let p' := p.take j
    have : ¬p'.Nil := by grind [nil_drop_iff, take_length]
.trans p.isSubwalk_take j have : p'.IsSubwalk p := isSubwalk_drop _ i
    grind [take_getVert, getVert_eq_support_getElem]

/--
theorem `IsTrail.isPath_iff_isSubwalk_imp_not_isCycle` / 定理 `IsTrail.isPath_iff_isSubwalk_imp_not_isCycle`

English:
theorem IsTrail.isPath_iff_isSubwalk_imp_not_isCycle
  given: {u v} {p : G.Walk u v} (ht : p.IsTrail)
  proof: by
  refine ⟨by grind [isPath_iff_isSubwalk_imp_nil, IsCycle.not_nil], fun h => ?_⟩
  classical
  match p with
  | .nil => simp
  | .cons hadj p =>
.mpr (h · · <| ·.cons hadj) have hp := isPath_iff_isSubwalk_imp_not_isCycle ht.of_cons
.mpr ⟨hp, fun hup => h u (p.takeUntil u hup |>.cons hadj) ?_ ?_⟩ 

中文:
定理 是Trail.isPath_iff_isSubwalk_imp_not_isCycle
  条件: {u v} {p : G.途径 u v} (ht : p.是Trail)
  证明: by
  refine ⟨by grind [isPath_iff_isSubwalk_imp_nil, IsCycle.not_nil], fun h => ?_⟩
  classical
  match p with
  | .nil => simp
  | .cons hadj p =>
.mpr (h · · <| ·.cons hadj) have hp := isPath_iff_isSubwalk_imp_not_isCycle ht.of_cons
.mpr ⟨hp, fun hup => h u (p.takeUntil u hup |>.cons hadj) ?_ ?_⟩ 

Depends on / 依赖: IsCycle, IsCycle.not_nil, List.prefix_cons_inj, classical, cons_isPath_iff, hp.takeUntil, ht.of_cons, isInfix, isPath_iff_isSubwalk_imp_nil, isPath_iff_isSubwalk_imp_not_isCycle, isSubwalk_iff_support_isInfix, not_nil, of_cons, p.support_takeUntil_prefix_support, p.takeUntil, prefix_cons_inj, support_cons, support_takeUntil_prefix_support, takeUntil
-/
theorem IsTrail.isPath_iff_isSubwalk_imp_not_isCycle {u v} {p : G.Walk u v} (ht : p.IsTrail) :
    p.IsPath ↔ forall (v : V) (w : G.Walk v v), w.IsSubwalk p -> ¬w.IsCycle := by
  refine ⟨by grind [isPath_iff_isSubwalk_imp_nil, IsCycle.not_nil], fun h => ?_⟩
  classical
  match p with
  | .nil => simp
  | .cons hadj p =>
.mpr (h · · <| ·.cons hadj) have hp := isPath_iff_isSubwalk_imp_not_isCycle ht.of_cons
.mpr ⟨hp, fun hup => h u (p.takeUntil u hup |>.cons hadj) ?_ ?_⟩ refine cons_isPath_iff ..
    · rw [isSubwalk_iff_support_isInfix, support_cons, support_cons]
      exact (List.prefix_cons_inj u |>.mpr <| p.support_takeUntil_prefix_support hup).isInfix
.mpr ⟨hp.takeUntil hup, fun he => ?_⟩ · refine cons_isCycle_iff ..
exact ht.edges_nodup.notMem p.edges_takeUntil_subset_edges hup he

end Walk

/-! ### Type of paths -/

/--
Definition of `Path` / `Path` 的定义

English:
abbreviation Path
  signature: (u v : V)
  body: { p : G.Walk u v // p.IsPath }

中文:
缩写 道路
  签名: (u v : V)
  定义体: { p : G.Walk u v // p.IsPath }

Depends on / 依赖: G.Walk, IsPath, p.IsPath
-/
abbrev Path (u v : V) := { p : G.Walk u v // p.IsPath }

namespace Path

variable {G G'}

@[simp]
/--
theorem `isPath` / 定理 `isPath`

English:
theorem isPath
  given: {u v : V} (p : G.Path u v)
  statement: (p : G.Walk u v).IsPath
  proof: p.property

@[simp]

中文:
定理 isPath
  条件: {u v : V} (p : G.道路 u v)
  结论: (p : G.途径 u v).是道路
  证明: p.property

@[simp]
-/
protected theorem isPath {u v : V} (p : G.Path u v) : (p : G.Walk u v).IsPath := p.property

@[simp]
/--
theorem `isTrail` / 定理 `isTrail`

English:
theorem isTrail
  given: {u v : V} (p : G.Path u v)
  statement: (p : G.Walk u v).IsTrail
  proof: p.property.isTrail

中文:
定理 isTrail
  条件: {u v : V} (p : G.道路 u v)
  结论: (p : G.途径 u v).是Trail
  证明: p.property.isTrail
-/
protected theorem isTrail {u v : V} (p : G.Path u v) : (p : G.Walk u v).IsTrail :=
  p.property.isTrail

/-- The length-0 path at a vertex. -/
@[refl, simps]
/--
Definition of `nil` / `nil` 的定义

English:
definition nil
  signature: {u : V}
  body: ⟨Walk.nil, Walk.IsPath.nil⟩

中文:
定义 nil
  签名: {u : V}
  定义体: ⟨Walk.nil, Walk.IsPath.nil⟩
-/
protected def nil {u : V} : G.Path u u :=
  ⟨Walk.nil, Walk.IsPath.nil⟩

/-- The length-1 path between a pair of adjacent vertices. -/
@[simps]
/--
Definition of `singleton` / `singleton` 的定义

English:
definition singleton
  signature: {u v : V} (h : G.Adj u v)
  body: ⟨Walk.cons h Walk.nil, by simp [h.ne]⟩

中文:
定义 singleton
  签名: {u v : V} (h : G.伴随 u v)
  定义体: ⟨Walk.cons h Walk.nil, by simp [h.ne]⟩

Depends on / 依赖: Walk.cons, Walk.nil, h.ne
-/
def singleton {u v : V} (h : G.Adj u v) : G.Path u v :=
  ⟨Walk.cons h Walk.nil, by simp [h.ne]⟩

/--
theorem `mk'_mem_edges_singleton` / 定理 `mk'_mem_edges_singleton`

English:
theorem mk'_mem_edges_singleton
  given: {u v : V} (h : G.Adj u v)
  proof: by simp [singleton]

中文:
定理 mk'_mem_edges_singleton
  条件: {u v : V} (h : G.伴随 u v)
  证明: by simp [singleton]

Depends on / 依赖: singleton
-/
theorem mk'_mem_edges_singleton {u v : V} (h : G.Adj u v) :
    s(u, v) in (singleton h : G.Walk u v).edges := by simp [singleton]

/-- The reverse of a path is another path. See also `SimpleGraph.Walk.reverse`. -/
@[symm, simps]
/--
Definition of `reverse` / `reverse` 的定义

English:
definition reverse
  signature: {u v : V} (p : G.Path u v)
  body: ⟨Walk.reverse p, p.property.reverse⟩

中文:
定义 reverse
  签名: {u v : V} (p : G.道路 u v)
  定义体: ⟨Walk.reverse p, p.property.reverse⟩

Depends on / 依赖: Walk.reverse, p.property.reverse, property, reverse
-/
def reverse {u v : V} (p : G.Path u v) : G.Path v u :=
  ⟨Walk.reverse p, p.property.reverse⟩

/--
theorem `count_support_eq_one` / 定理 `count_support_eq_one`

English:
theorem count_support_eq_one
  statement: [DecidableEq V] {u v w : V} {p : G.Path u v}
  proof: List.count_eq_one_of_mem p.property.support_nodup hw

中文:
定理 count_support_eq_one
  结论: [DecidableEq V] {u v w : V} {p : G.道路 u v}
  证明: List.count_eq_one_of_mem p.property.support_nodup hw

Depends on / 依赖: List.count_eq_one_of_mem, count_eq_one_of_mem, p.property.support_nodup, property, support_nodup
-/
theorem count_support_eq_one [DecidableEq V] {u v w : V} {p : G.Path u v}
    (hw : w in (p : G.Walk u v).support) : (p : G.Walk u v).support.count w = 1 :=
  List.count_eq_one_of_mem p.property.support_nodup hw

/--
theorem `count_edges_eq_one` / 定理 `count_edges_eq_one`

English:
theorem count_edges_eq_one
  statement: [DecidableEq V] {u v : V} {p : G.Path u v} (e : Sym2 V)
  proof: List.count_eq_one_of_mem p.property.isTrail.edges_nodup hw

@[simp]

中文:
定理 count_edges_eq_one
  结论: [DecidableEq V] {u v : V} {p : G.道路 u v} (e : Sym2 V)
  证明: List.count_eq_one_of_mem p.property.isTrail.edges_nodup hw

@[simp]

Depends on / 依赖: List.count_eq_one_of_mem, count_eq_one_of_mem, edges_nodup, isTrail, p.property.isTrail.edges_nodup, property
-/
theorem count_edges_eq_one [DecidableEq V] {u v : V} {p : G.Path u v} (e : Sym2 V)
    (hw : e in (p : G.Walk u v).edges) : (p : G.Walk u v).edges.count e = 1 :=
  List.count_eq_one_of_mem p.property.isTrail.edges_nodup hw

@[simp]
/--
theorem `nodup_support` / 定理 `nodup_support`

English:
theorem nodup_support
  given: {u v : V} (p : G.Path u v)
  statement: (p : G.Walk u v).support.Nodup
  proof: (Walk.isPath_def _).mp p.property

中文:
定理 nodup_support
  条件: {u v : V} (p : G.道路 u v)
  结论: (p : G.途径 u v).support.Nodup
  证明: (Walk.isPath_def _).mp p.property

Depends on / 依赖: Walk.isPath_def, isPath_def, p.property, property
-/
theorem nodup_support {u v : V} (p : G.Path u v) : (p : G.Walk u v).support.Nodup :=
  (Walk.isPath_def _).mp p.property

/--
theorem `loop_eq` / 定理 `loop_eq`

English:
theorem loop_eq
  given: {v : V} (p : G.Path v v)
  statement: p = Path.nil
  proof: by
  obtain ⟨_ | _, h⟩ := p
  · rfl
  · simp at h

中文:
定理 loop_eq
  条件: {v : V} (p : G.道路 v v)
  结论: p = 道路.nil
  证明: by
  obtain ⟨_ | _, h⟩ := p
  · rfl
  · simp at h
-/
theorem loop_eq {v : V} (p : G.Path v v) : p = Path.nil := by
  obtain ⟨_ | _, h⟩ := p
  · rfl
  · simp at h

/--
theorem `notMem_edges_of_loop` / 定理 `notMem_edges_of_loop`

English:
theorem notMem_edges_of_loop
  given: {v : V} {e : Sym2 V} {p : G.Path v v}
  proof: by simp [p.loop_eq]

中文:
定理 notMem_edges_of_loop
  条件: {v : V} {e : Sym2 V} {p : G.道路 v v}
  证明: by simp [p.loop_eq]

Depends on / 依赖: loop_eq, p.loop_eq
-/
theorem notMem_edges_of_loop {v : V} {e : Sym2 V} {p : G.Path v v} :
    e ∉ (p : G.Walk v v).edges := by simp [p.loop_eq]

/--
theorem `cons_isCycle` / 定理 `cons_isCycle`

English:
theorem cons_isCycle
  statement: {u v : V} (p : G.Path v u) (h : G.Adj u v)
  proof: by
  simp [Walk.isCycle_def, Walk.isTrail_cons, he]

中文:
定理 cons_isCycle
  结论: {u v : V} (p : G.道路 v u) (h : G.伴随 u v)
  证明: by
  simp [Walk.isCycle_def, Walk.isTrail_cons, he]

Depends on / 依赖: Walk.isCycle_def, Walk.isTrail_cons, isCycle_def, isTrail_cons
-/
theorem cons_isCycle {u v : V} (p : G.Path v u) (h : G.Adj u v)
    (he : s(u, v) ∉ (p : G.Walk v u).edges) : (Walk.cons h ↑p).IsCycle := by
  simp [Walk.isCycle_def, Walk.isTrail_cons, he]

end Path


/-! ### Walks to paths -/

namespace Walk

variable {G} {u v : V}

/--
theorem `IsPath.length_eq_one_of_mem_edges` / 定理 `IsPath.length_eq_one_of_mem_edges`

English:
theorem IsPath.length_eq_one_of_mem_edges
  given: {p : G.Walk u v} (hp : p.IsPath) (h : s(u, v) in p.edges)
  proof: by
  suffices p.length - 1 = 0 by grind [length_edges]
  rw [← hp.getVert_eq_start_iff <| p.length.sub_le 1]
  exact (hp.eq_penultimate_of_mem_edges <| Sym2.eq_swap ▸ h).symm

中文:
定理 是道路.length_eq_one_of_mem_edges
  条件: {p : G.途径 u v} (hp : p.是道路) (h : s(u, v) in p.edges)
  证明: by
  suffices p.length - 1 = 0 by grind [length_edges]
  rw [← hp.getVert_eq_start_iff <| p.length.sub_le 1]
  exact (hp.eq_penultimate_of_mem_edges <| Sym2.eq_swap ▸ h).symm

Depends on / 依赖: Sym2.eq_swap, eq_penultimate_of_mem_edges, eq_swap, getVert_eq_start_iff, hp.eq_penultimate_of_mem_edges, hp.getVert_eq_start_iff, length, length_edges, p.length, p.length.sub_le, sub_le
-/
theorem IsPath.length_eq_one_of_mem_edges {p : G.Walk u v} (hp : p.IsPath) (h : s(u, v) in p.edges) :
    p.length = 1 := by
  suffices p.length - 1 = 0 by grind [length_edges]
  rw [← hp.getVert_eq_start_iff <| p.length.sub_le 1]
  exact (hp.eq_penultimate_of_mem_edges <| Sym2.eq_swap ▸ h).symm

/--
theorem `IsPath.eq_adj_toWalk_of_mem_edges` / 定理 `IsPath.eq_adj_toWalk_of_mem_edges`

English:
theorem IsPath.eq_adj_toWalk_of_mem_edges
  given: {p : G.Walk u v} (hp : p.IsPath) (h : s(u, v) in p.edges)
  proof: by
apply p.ext_getVert_le_length by simp [hp.length_eq_one_of_mem_edges h]
  intro _ hl
  cases Nat.le_one_iff_eq_zero_or_eq_one.mp (hp.length_eq_one_of_mem_edges h ▸ hl) with
  | inl hl => simp [hl]
  | inr hl =>
    rw [hl]; rw [getVert_cons_succ]; rw [getVert_zero]; rw [← hp.length_eq_one_of_mem_

中文:
定理 是道路.eq_adj_toWalk_of_mem_edges
  条件: {p : G.途径 u v} (hp : p.是道路) (h : s(u, v) in p.edges)
  证明: by
apply p.ext_getVert_le_length by simp [hp.length_eq_one_of_mem_edges h]
  intro _ hl
  cases Nat.le_one_iff_eq_zero_or_eq_one.mp (hp.length_eq_one_of_mem_edges h ▸ hl) with
  | inl hl => simp [hl]
  | inr hl =>
    rw [hl]; rw [getVert_cons_succ]; rw [getVert_zero]; rw [← hp.length_eq_one_of_mem_

Depends on / 依赖: Nat.le_one_iff_eq_zero_or_eq_one.mp, ext_getVert_le_length, getVert_cons_succ, getVert_length, getVert_zero, hp.length_eq_one_of_mem_edges, le_one_iff_eq_zero_or_eq_one, length_eq_one_of_mem_edges, p.ext_getVert_le_length
-/
theorem IsPath.eq_adj_toWalk_of_mem_edges {p : G.Walk u v} (hp : p.IsPath) (h : s(u, v) in p.edges) :
    p = (p.adj_of_mem_edges h).toWalk := by
apply p.ext_getVert_le_length by simp [hp.length_eq_one_of_mem_edges h]
  intro _ hl
  cases Nat.le_one_iff_eq_zero_or_eq_one.mp (hp.length_eq_one_of_mem_edges h ▸ hl) with
  | inl hl => simp [hl]
  | inr hl =>
    rw [hl]; rw [getVert_cons_succ]; rw [getVert_zero]; rw [← hp.length_eq_one_of_mem_edges h]; rw [getVert_length]

/--
theorem `IsPath.disjoint_edges_of_disjoint_support` / 定理 `IsPath.disjoint_edges_of_disjoint_support`

English:
theorem IsPath.disjoint_edges_of_disjoint_support
  statement: {p : G.Walk u v} {q : G.Walk v u} (hp : p.IsPath)
  proof: by
  simp only [List.disjoint_left] at hd ⊢
  contrapose! hd
  obtain ⟨⟨a, b⟩, hep, heq⟩ := hd
have := p.mem_support_iff.mp p.fst_mem_support_of_mem_edges hep
have := p.mem_support_iff.mp p.snd_mem_support_of_mem_edges hep
have := q.mem_support_iff.mp q.fst_mem_support_of_mem_edges heq
have := q.mem

中文:
定理 是道路.disjoint_edges_of_disjoint_support
  结论: {p : G.途径 u v} {q : G.途径 v u} (hp : p.是道路)
  证明: by
  simp only [List.disjoint_left] at hd ⊢
  contrapose! hd
  obtain ⟨⟨a, b⟩, hep, heq⟩ := hd
have := p.mem_support_iff.mp p.fst_mem_support_of_mem_edges hep
have := p.mem_support_iff.mp p.snd_mem_support_of_mem_edges hep
have := q.mem_support_iff.mp q.fst_mem_support_of_mem_edges heq
have := q.mem

Depends on / 依赖: List.disjoint_left, adj_of_mem_edges, contrapose, disjoint_left, fst_mem_support_of_mem_edges, length_eq_one_of_mem_edges, mem_support_iff, p.adj_of_mem_edges, p.fst_mem_support_of_mem_edges, p.mem_support_iff.mp, p.snd_mem_support_of_mem_edges, q.fst_mem_support_of_mem_edges, q.mem_support_iff.mp, q.snd_mem_support_of_mem_edges, snd_mem_support_of_mem_edges
-/
theorem IsPath.disjoint_edges_of_disjoint_support {p : G.Walk u v} {q : G.Walk v u} (hp : p.IsPath)
    (hd : p.support.tail.Disjoint q.support.tail) (hl : p.length != 1) :
    p.edges.Disjoint q.edges := by
  simp only [List.disjoint_left] at hd ⊢
  contrapose! hd
  obtain ⟨⟨a, b⟩, hep, heq⟩ := hd
have := p.mem_support_iff.mp p.fst_mem_support_of_mem_edges hep
have := p.mem_support_iff.mp p.snd_mem_support_of_mem_edges hep
have := q.mem_support_iff.mp q.fst_mem_support_of_mem_edges heq
have := q.mem_support_iff.mp q.snd_mem_support_of_mem_edges heq
  grind [p.adj_of_mem_edges hep |>.ne, length_eq_one_of_mem_edges]

/--
lemma `IsPath.isCycle_append` / 引理 `IsPath.isCycle_append`

English:
lemma IsPath.isCycle_append
  statement: {p : G.Walk u v} {q : G.Walk v u} (hp : p.IsPath) (hq : q.IsPath)
  proof: by
  rw [isCycle_def]; rw [isTrail_append]
  refine ⟨⟨hp.isTrail, hq.isTrail, ?_⟩, ?_, ?_⟩
  · grind [IsPath.disjoint_edges_of_disjoint_support, List.Disjoint.symm]
  · grind [nil_append_iff]
  · rw [tail_support_append, List.nodup_append']
    exact ⟨hp.support_nodup.tail, hq.support_nodup.tail, h⟩

中文:
引理 是道路.isCycle_append
  结论: {p : G.途径 u v} {q : G.途径 v u} (hp : p.是道路) (hq : q.是道路)
  证明: by
  rw [isCycle_def]; rw [isTrail_append]
  refine ⟨⟨hp.isTrail, hq.isTrail, ?_⟩, ?_, ?_⟩
  · grind [IsPath.disjoint_edges_of_disjoint_support, List.Disjoint.symm]
  · grind [nil_append_iff]
  · rw [tail_support_append, List.nodup_append']
    exact ⟨hp.support_nodup.tail, hq.support_nodup.tail, h⟩

Depends on / 依赖: Disjoint, IsPath, IsPath.disjoint_edges_of_disjoint_support, List.Disjoint.symm, List.nodup_append, disjoint_edges_of_disjoint_support, hp.isTrail, hp.support_nodup.tail, hq.isTrail, hq.support_nodup.tail, isCycle_def, isTrail, isTrail_append, nil_append_iff, nodup_append, support_nodup, tail_support_append
-/
lemma IsPath.isCycle_append {p : G.Walk u v} {q : G.Walk v u} (hp : p.IsPath) (hq : q.IsPath)
    (h : p.support.tail.Disjoint q.support.tail) (hn : 1 < p.length ∨ 1 < q.length) :
    (p.append q).IsCycle := by
  rw [isCycle_def]; rw [isTrail_append]
  refine ⟨⟨hp.isTrail, hq.isTrail, ?_⟩, ?_, ?_⟩
  · grind [IsPath.disjoint_edges_of_disjoint_support, List.Disjoint.symm]
  · grind [nil_append_iff]
  · rw [tail_support_append, List.nodup_append']
    exact ⟨hp.support_nodup.tail, hq.support_nodup.tail, h⟩

/--
theorem `IsPath.exists_isCycle_of_ne` / 定理 `IsPath.exists_isCycle_of_ne`

English:
theorem IsPath.exists_isCycle_of_ne
  statement: {p q : G.Walk u v} (hp : p.IsPath) (hq : q.IsPath)
  proof: by
  induction hs : p.length using Nat.strongRec generalizing u v with | ind s ih =>
  by_cases! hw : exists w, w in p.support ∧ w in q.support ∧ w != u ∧ w != v
  · classical
    have ⟨w, hwp, hwq, hwu, hwv⟩ := hw
    by_cases! p.takeUntil w hwp != q.takeUntil w hwq
    · have := ih _ (hs ▸ length_

中文:
定理 是道路.存在_isCycle_of_ne
  结论: {p q : G.途径 u v} (hp : p.是道路) (hq : q.是道路)
  证明: by
  induction hs : p.length using Nat.strongRec generalizing u v with | ind s ih =>
  by_cases! hw : exists w, w in p.support ∧ w in q.support ∧ w != u ∧ w != v
  · classical
    have ⟨w, hwp, hwq, hwu, hwv⟩ := hw
    by_cases! p.takeUntil w hwp != q.takeUntil w hwq
    · have := ih _ (hs ▸ length_

Depends on / 依赖: IsSubwalk, IsSubwalk.trans, Nat.strongRec, classical, dropUntil, generalizing, hp.dropUntil, hp.takeUntil, hq.dropUntil, hq.takeUntil, isSubwalk_takeUntil, length, length_dropUntil_lt_length, length_takeUntil_lt_length, p.length, p.support, p.takeUntil, q.support, q.takeUntil, strongRec
-/
theorem IsPath.exists_isCycle_of_ne {p q : G.Walk u v} (hp : p.IsPath) (hq : q.IsPath)
    (h : p != q) :
    exists (u' v' : V) (p' q' : G.Walk u' v'),
      p'.IsSubwalk p ∧ q'.IsSubwalk q ∧ (p'.append q'.reverse).IsCycle := by
  induction hs : p.length using Nat.strongRec generalizing u v with | ind s ih =>
  by_cases! hw : exists w, w in p.support ∧ w in q.support ∧ w != u ∧ w != v
  · classical
    have ⟨w, hwp, hwq, hwu, hwv⟩ := hw
    by_cases! p.takeUntil w hwp != q.takeUntil w hwq
    · have := ih _ (hs ▸ length_takeUntil_lt_length hwp hwv) (hp.takeUntil hwp) (hq.takeUntil hwq)
      grind [isSubwalk_takeUntil, IsSubwalk.trans]
    · have := ih _ (hs ▸ length_dropUntil_lt_length hwp hwu) (hp.dropUntil hwp) (hq.dropUntil hwq)
 by grind [take_spec]
      grind [isSubwalk_dropUntil, IsSubwalk.trans]
  · refine ⟨u, v, p, q, p.isSubwalk_rfl, q.isSubwalk_rfl, ?_⟩
    refine hp.isCycle_append (isPath_reverse_iff q |>.mpr hq) (fun _ => ?_) ?_
    · grind [dropLast_support_concat, IsPath.support_nodup, support_reverse, cons_tail_support]
    · grind [length_reverse, eq_of_length_le_one]

open List in
/--
theorem `IsPath.exists_isCycle_sublist_of_ne` / 定理 `IsPath.exists_isCycle_sublist_of_ne`

English:
theorem IsPath.exists_isCycle_sublist_of_ne
  statement: {p q : G.Walk u v} (hp : p.IsPath)
  proof: by
  have ⟨u', v', p', q', hp', hq', hcyc⟩ := hp.exists_isCycle_of_ne hq h
  use u', hp'.support_subset p'.start_mem_support, hq'.support_subset q'.start_mem_support
  refine ⟨_, hcyc, ?_⟩
  rw [support_append]; rw [support_reverse]
refine .append ?_ .tail .reverse ?_
.sublist · exact isSubwalk_iff_

中文:
定理 是道路.存在_isCycle_sublist_of_ne
  结论: {p q : G.途径 u v} (hp : p.是道路)
  证明: by
  have ⟨u', v', p', q', hp', hq', hcyc⟩ := hp.exists_isCycle_of_ne hq h
  use u', hp'.support_subset p'.start_mem_support, hq'.support_subset q'.start_mem_support
  refine ⟨_, hcyc, ?_⟩
  rw [support_append]; rw [support_reverse]
refine .append ?_ .tail .reverse ?_
.sublist · exact isSubwalk_iff_

Depends on / 依赖: append, exists_isCycle_of_ne, hp.exists_isCycle_of_ne, isSubwalk_iff_support_isInfix, isSubwalk_iff_support_isInfix.mp, reverse, start_mem_support, sublist, support_append, support_reverse, support_subset
-/
theorem IsPath.exists_isCycle_sublist_of_ne {p q : G.Walk u v} (hp : p.IsPath)
    (hq : q.IsPath) (h : p != q) :
    exists w, w in p.support ∧ w in q.support ∧
      exists c : G.Walk w w, c.IsCycle ∧ c.support <+ (p.support ++ q.support.reverse.tail) := by
  have ⟨u', v', p', q', hp', hq', hcyc⟩ := hp.exists_isCycle_of_ne hq h
  use u', hp'.support_subset p'.start_mem_support, hq'.support_subset q'.start_mem_support
  refine ⟨_, hcyc, ?_⟩
  rw [support_append]; rw [support_reverse]
refine .append ?_ .tail .reverse ?_
.sublist · exact isSubwalk_iff_support_isInfix.mp hp'
.sublist · exact isSubwalk_iff_support_isInfix.mp hq'

/--
theorem `IsPath.exists_isCycle_length_le_add_of_ne` / 定理 `IsPath.exists_isCycle_length_le_add_of_ne`

English:
theorem IsPath.exists_isCycle_length_le_add_of_ne
  statement: {p q : G.Walk u v} (hp : p.IsPath)
  proof: by
  obtain ⟨w, hw₁, hw₂, c, hc₁, hc₂⟩ := hp.exists_isCycle_sublist_of_ne hq h
  use w, hw₁, hw₂, c, hc₁, by grind [hc₂.length_le]

中文:
定理 是道路.存在_isCycle_length_le_add_of_ne
  结论: {p q : G.途径 u v} (hp : p.是道路)
  证明: by
  obtain ⟨w, hw₁, hw₂, c, hc₁, hc₂⟩ := hp.exists_isCycle_sublist_of_ne hq h
  use w, hw₁, hw₂, c, hc₁, by grind [hc₂.length_le]

Depends on / 依赖: exists_isCycle_sublist_of_ne, hp.exists_isCycle_sublist_of_ne, length_le
-/
theorem IsPath.exists_isCycle_length_le_add_of_ne {p q : G.Walk u v} (hp : p.IsPath)
    (hq : q.IsPath) (h : p != q) :
    exists w, w in p.support ∧ w in q.support ∧
      exists c : G.Walk w w, c.IsCycle ∧ c.length <= p.length + q.length := by
  obtain ⟨w, hw₁, hw₂, c, hc₁, hc₂⟩ := hp.exists_isCycle_sublist_of_ne hq h
  use w, hw₁, hw₂, c, hc₁, by grind [hc₂.length_le]

variable [DecidableEq V] {u' v' : V}

/--
Definition of `bypass` / `bypass` 的定义

English:
definition bypass
  signature: {u v : V}
  body: p.bypass
    if hs : u in p'.support then
      p'.dropUntil u hs
    else
      cons ha p'

@[simp]

中文:
定义 bypass
  签名: {u v : V}
  定义体: p.bypass
    if hs : u in p'.support then
      p'.dropUntil u hs
    else
      cons ha p'

@[simp]

Depends on / 依赖: bypass, p.bypass
-/
def bypass {u v : V} : G.Walk u v -> G.Walk u v
  | nil => nil
  | cons ha p =>
    let p' := p.bypass
    if hs : u in p'.support then
      p'.dropUntil u hs
    else
      cons ha p'

@[simp]
/--
theorem `bypass_copy` / 定理 `bypass_copy`

English:
theorem bypass_copy
  given: (p : G.Walk u v) (hu : u = u') (hv : v = v')
  proof: by
  subst_vars
  rfl

中文:
定理 bypass_copy
  条件: (p : G.途径 u v) (hu : u = u') (hv : v = v')
  证明: by
  subst_vars
  rfl
-/
theorem bypass_copy (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).bypass = p.bypass.copy hu hv := by
  subst_vars
  rfl

/--
theorem `bypass_isPath` / 定理 `bypass_isPath`

English:
theorem bypass_isPath
  given: (p : G.Walk u v)
  statement: p.bypass.IsPath
  proof: by
  induction p with
  | nil => simp!
  | cons _ p' ih =>
    simp only [bypass]
    split_ifs with hs
    · exact ih.dropUntil hs
    · simp [*, cons_isPath_iff]

中文:
定理 bypass_isPath
  条件: (p : G.途径 u v)
  结论: p.bypass.是道路
  证明: by
  induction p with
  | nil => simp!
  | cons _ p' ih =>
    simp only [bypass]
    split_ifs with hs
    · exact ih.dropUntil hs
    · simp [*, cons_isPath_iff]

Depends on / 依赖: bypass, cons_isPath_iff, dropUntil, ih.dropUntil, split_ifs
-/
theorem bypass_isPath (p : G.Walk u v) : p.bypass.IsPath := by
  induction p with
  | nil => simp!
  | cons _ p' ih =>
    simp only [bypass]
    split_ifs with hs
    · exact ih.dropUntil hs
    · simp [*, cons_isPath_iff]

/--
Definition of `toPath` / `toPath` 的定义

English:
definition toPath
  signature: (p : G.Walk u v)
  body: ⟨p.bypass, p.bypass_isPath⟩

中文:
定义 toPath
  签名: (p : G.途径 u v)
  定义体: ⟨p.bypass, p.bypass_isPath⟩

Depends on / 依赖: bypass, bypass_isPath, p.bypass, p.bypass_isPath
-/
def toPath (p : G.Walk u v) : G.Path u v :=
  ⟨p.bypass, p.bypass_isPath⟩

open List in
/--
theorem `support_bypass_sublist_support` / 定理 `support_bypass_sublist_support`

English:
theorem support_bypass_sublist_support
  given: (p : G.Walk u v)
  statement: p.bypass.support <+ p.support
  proof: by
  induction p with
  | nil => simp!
  | cons _ _ ih =>
    dsimp! only
    split_ifs
.cons _ .sublist.trans ih · exact support_dropUntil_suffix_support ..
    · simpa

中文:
定理 support_bypass_sublist_support
  条件: (p : G.途径 u v)
  结论: p.bypass.support <+ p.support
  证明: by
  induction p with
  | nil => simp!
  | cons _ _ ih =>
    dsimp! only
    split_ifs
.cons _ .sublist.trans ih · exact support_dropUntil_suffix_support ..
    · simpa

Depends on / 依赖: split_ifs, sublist, sublist.trans, support_dropUntil_suffix_support
-/
theorem support_bypass_sublist_support (p : G.Walk u v) : p.bypass.support <+ p.support := by
  induction p with
  | nil => simp!
  | cons _ _ ih =>
    dsimp! only
    split_ifs
.cons _ .sublist.trans ih · exact support_dropUntil_suffix_support ..
    · simpa

/--
theorem `support_bypass_subset_support` / 定理 `support_bypass_subset_support`

English:
theorem support_bypass_subset_support
  given: (p : G.Walk u v)
  statement: p.bypass.support subseteq p.support
  proof: p.support_bypass_sublist_support.subset

@[deprecated (since := "2026-05-25")] alias support_bypass_subset := support_bypass_subset_support

中文:
定理 support_bypass_subset_support
  条件: (p : G.途径 u v)
  结论: p.bypass.support subseteq p.support
  证明: p.support_bypass_sublist_support.subset

@[deprecated (since := "2026-05-25")] alias support_bypass_subset := support_bypass_subset_support

Depends on / 依赖: p.support_bypass_sublist_support.subset, subset, support_bypass_sublist_support
-/
theorem support_bypass_subset_support (p : G.Walk u v) : p.bypass.support subseteq p.support :=
  p.support_bypass_sublist_support.subset

@[deprecated (since := "2026-05-25")] alias support_bypass_subset := support_bypass_subset_support

/--
theorem `support_toPath_subset_support` / 定理 `support_toPath_subset_support`

English:
theorem support_toPath_subset_support
  given: (p : G.Walk u v)
  proof: p.support_bypass_subset_support

@[deprecated (since := "2026-05-25")] alias support_toPath_subset := support_toPath_subset_support

中文:
定理 support_toPath_subset_support
  条件: (p : G.途径 u v)
  证明: p.support_bypass_subset_support

@[deprecated (since := "2026-05-25")] alias support_toPath_subset := support_toPath_subset_support

Depends on / 依赖: p.support_bypass_subset_support, support_bypass_subset_support
-/
theorem support_toPath_subset_support (p : G.Walk u v) :
    (p.toPath : G.Walk u v).support subseteq p.support :=
  p.support_bypass_subset_support

@[deprecated (since := "2026-05-25")] alias support_toPath_subset := support_toPath_subset_support

open List in
/--
theorem `darts_bypass_sublist_darts` / 定理 `darts_bypass_sublist_darts`

English:
theorem darts_bypass_sublist_darts
  given: (p : G.Walk u v)
  statement: p.bypass.darts <+ p.darts
  proof: by
  induction p with
  | nil => simp!
  | cons _ _ ih =>
    dsimp! only
    split_ifs
.cons _ .sublist.trans ih · exact darts_dropUntil_suffix_darts ..
    · simpa

中文:
定理 darts_bypass_sublist_darts
  条件: (p : G.途径 u v)
  结论: p.bypass.darts <+ p.darts
  证明: by
  induction p with
  | nil => simp!
  | cons _ _ ih =>
    dsimp! only
    split_ifs
.cons _ .sublist.trans ih · exact darts_dropUntil_suffix_darts ..
    · simpa

Depends on / 依赖: darts_dropUntil_suffix_darts, split_ifs, sublist, sublist.trans
-/
theorem darts_bypass_sublist_darts (p : G.Walk u v) : p.bypass.darts <+ p.darts := by
  induction p with
  | nil => simp!
  | cons _ _ ih =>
    dsimp! only
    split_ifs
.cons _ .sublist.trans ih · exact darts_dropUntil_suffix_darts ..
    · simpa

/--
theorem `darts_bypass_subset_darts` / 定理 `darts_bypass_subset_darts`

English:
theorem darts_bypass_subset_darts
  given: (p : G.Walk u v)
  statement: p.bypass.darts subseteq p.darts
  proof: p.darts_bypass_sublist_darts.subset

@[deprecated (since := "2026-05-25")] alias darts_bypass_subset := darts_bypass_subset_darts

中文:
定理 darts_bypass_subset_darts
  条件: (p : G.途径 u v)
  结论: p.bypass.darts subseteq p.darts
  证明: p.darts_bypass_sublist_darts.subset

@[deprecated (since := "2026-05-25")] alias darts_bypass_subset := darts_bypass_subset_darts

Depends on / 依赖: darts_bypass_sublist_darts, p.darts_bypass_sublist_darts.subset, subset
-/
theorem darts_bypass_subset_darts (p : G.Walk u v) : p.bypass.darts subseteq p.darts :=
  p.darts_bypass_sublist_darts.subset

@[deprecated (since := "2026-05-25")] alias darts_bypass_subset := darts_bypass_subset_darts

open List in
/--
theorem `edges_bypass_sublist_edges` / 定理 `edges_bypass_sublist_edges`

English:
theorem edges_bypass_sublist_edges
  given: (p : G.Walk u v)
  statement: p.bypass.edges <+ p.edges
  proof: p.darts_bypass_sublist_darts.map _

中文:
定理 edges_bypass_sublist_edges
  条件: (p : G.途径 u v)
  结论: p.bypass.edges <+ p.edges
  证明: p.darts_bypass_sublist_darts.map _

Depends on / 依赖: darts_bypass_sublist_darts, p.darts_bypass_sublist_darts.map
-/
theorem edges_bypass_sublist_edges (p : G.Walk u v) : p.bypass.edges <+ p.edges :=
  p.darts_bypass_sublist_darts.map _

/--
theorem `edges_bypass_subset_edges` / 定理 `edges_bypass_subset_edges`

English:
theorem edges_bypass_subset_edges
  given: (p : G.Walk u v)
  statement: p.bypass.edges subseteq p.edges
  proof: p.edges_bypass_sublist_edges.subset

@[deprecated (since := "2026-05-25")] alias edges_bypass_subset := edges_bypass_subset_edges

中文:
定理 edges_bypass_subset_edges
  条件: (p : G.途径 u v)
  结论: p.bypass.edges subseteq p.edges
  证明: p.edges_bypass_sublist_edges.subset

@[deprecated (since := "2026-05-25")] alias edges_bypass_subset := edges_bypass_subset_edges

Depends on / 依赖: edges_bypass_sublist_edges, p.edges_bypass_sublist_edges.subset, subset
-/
theorem edges_bypass_subset_edges (p : G.Walk u v) : p.bypass.edges subseteq p.edges :=
  p.edges_bypass_sublist_edges.subset

@[deprecated (since := "2026-05-25")] alias edges_bypass_subset := edges_bypass_subset_edges

/--
theorem `length_bypass_le_length` / 定理 `length_bypass_le_length`

English:
theorem length_bypass_le_length
  given: (p : G.Walk u v)
  statement: p.bypass.length <= p.length
  proof: by
  simpa using p.darts_bypass_sublist_darts.length_le

@[deprecated (since := "2026-05-25")] alias length_bypass_le := length_bypass_le_length

中文:
定理 length_bypass_le_length
  条件: (p : G.途径 u v)
  结论: p.bypass.length <= p.length
  证明: by
  simpa using p.darts_bypass_sublist_darts.length_le

@[deprecated (since := "2026-05-25")] alias length_bypass_le := length_bypass_le_length

Depends on / 依赖: darts_bypass_sublist_darts, length_le, p.darts_bypass_sublist_darts.length_le
-/
theorem length_bypass_le_length (p : G.Walk u v) : p.bypass.length <= p.length := by
  simpa using p.darts_bypass_sublist_darts.length_le

@[deprecated (since := "2026-05-25")] alias length_bypass_le := length_bypass_le_length

/--
lemma `bypass_eq_self_of_length_le_length_bypass` / 引理 `bypass_eq_self_of_length_le_length_bypass`

English:
lemma bypass_eq_self_of_length_le_length_bypass
  given: (p : G.Walk u v) (h : p.length <= p.bypass.length)
  proof: ext_support p.support_bypass_sublist_support.eq_of_length_le by simpa using h

@[deprecated (since := "2026-05-25")]
alias bypass_eq_self_of_length_le := bypass_eq_self_of_length_le_length_bypass

@[grind ->]

中文:
引理 bypass_eq_self_of_length_le_length_bypass
  条件: (p : G.途径 u v) (h : p.length <= p.bypass.length)
  证明: ext_support p.support_bypass_sublist_support.eq_of_length_le by simpa using h

@[deprecated (since := "2026-05-25")]
alias bypass_eq_self_of_length_le := bypass_eq_self_of_length_le_length_bypass

@[grind ->]

Depends on / 依赖: eq_of_length_le, ext_support, p.support_bypass_sublist_support.eq_of_length_le, support_bypass_sublist_support
-/
lemma bypass_eq_self_of_length_le_length_bypass (p : G.Walk u v) (h : p.length <= p.bypass.length) :
    p.bypass = p :=
ext_support p.support_bypass_sublist_support.eq_of_length_le by simpa using h

@[deprecated (since := "2026-05-25")]
alias bypass_eq_self_of_length_le := bypass_eq_self_of_length_le_length_bypass

@[grind ->]
/--
lemma `IsPath.bypass_eq_self` / 引理 `IsPath.bypass_eq_self`

English:
lemma IsPath.bypass_eq_self
  given: {p : G.Walk u v} (hp : p.IsPath)
  statement: p.bypass = p
  proof: by
  induction p <;> simp_all [cons_isPath_iff, bypass]

中文:
引理 是道路.bypass_eq_self
  条件: {p : G.途径 u v} (hp : p.是道路)
  结论: p.bypass = p
  证明: by
  induction p <;> simp_all [cons_isPath_iff, bypass]

Depends on / 依赖: bypass, cons_isPath_iff
-/
lemma IsPath.bypass_eq_self {p : G.Walk u v} (hp : p.IsPath) : p.bypass = p := by
  induction p <;> simp_all [cons_isPath_iff, bypass]

/--
theorem `darts_toPath_subset_darts` / 定理 `darts_toPath_subset_darts`

English:
theorem darts_toPath_subset_darts
  given: (p : G.Walk u v)
  statement: (p.toPath : G.Walk u v).darts subseteq p.darts
  proof: p.darts_bypass_subset_darts

@[deprecated (since := "2026-05-25")] alias darts_toPath_subset := darts_toPath_subset_darts

中文:
定理 darts_toPath_subset_darts
  条件: (p : G.途径 u v)
  结论: (p.toPath : G.途径 u v).darts subseteq p.darts
  证明: p.darts_bypass_subset_darts

@[deprecated (since := "2026-05-25")] alias darts_toPath_subset := darts_toPath_subset_darts

Depends on / 依赖: darts_bypass_subset_darts, p.darts_bypass_subset_darts
-/
theorem darts_toPath_subset_darts (p : G.Walk u v) : (p.toPath : G.Walk u v).darts subseteq p.darts :=
  p.darts_bypass_subset_darts

@[deprecated (since := "2026-05-25")] alias darts_toPath_subset := darts_toPath_subset_darts

/--
theorem `edges_toPath_subset_edges` / 定理 `edges_toPath_subset_edges`

English:
theorem edges_toPath_subset_edges
  given: (p : G.Walk u v)
  statement: (p.toPath : G.Walk u v).edges subseteq p.edges
  proof: p.edges_bypass_subset_edges

@[deprecated (since := "2026-05-25")] alias edges_toPath_subset := edges_toPath_subset_edges

中文:
定理 edges_toPath_subset_edges
  条件: (p : G.途径 u v)
  结论: (p.toPath : G.途径 u v).edges subseteq p.edges
  证明: p.edges_bypass_subset_edges

@[deprecated (since := "2026-05-25")] alias edges_toPath_subset := edges_toPath_subset_edges

Depends on / 依赖: edges_bypass_subset_edges, p.edges_bypass_subset_edges
-/
theorem edges_toPath_subset_edges (p : G.Walk u v) : (p.toPath : G.Walk u v).edges subseteq p.edges :=
  p.edges_bypass_subset_edges

@[deprecated (since := "2026-05-25")] alias edges_toPath_subset := edges_toPath_subset_edges

/--
Definition of `cycleBypass` / `cycleBypass` 的定义

English:
definition cycleBypass
  signature: : G.Walk v v -> G.Walk v v

中文:
定义 cycleBypass
  签名: : G.途径 v v -> G.途径 v v
-/
def cycleBypass : G.Walk v v -> G.Walk v v
  | .nil => .nil
  | .cons hvv' w => .cons hvv' w.bypass

/--
lemma `cycleBypass_nil` / 引理 `cycleBypass_nil`

English:
lemma cycleBypass_nil
  statement: (.nil : G.Walk v v).cycleBypass = .nil
  proof: rfl

中文:
引理 cycleBypass_nil
  结论: (.nil : G.途径 v v).cycleBypass = .nil
  证明: rfl
-/
@[simp] lemma cycleBypass_nil : (.nil : G.Walk v v).cycleBypass = .nil := rfl

open List in
/--
theorem `support_cycleBypass_sublist_support` / 定理 `support_cycleBypass_sublist_support`

English:
theorem support_cycleBypass_sublist_support
  statement: forall (w : G.Walk v v), w.cycleBypass.support <+ w.support

中文:
定理 support_cycleBypass_sublist_support
  结论: 对任意 (w : G.途径 v v), w.cycleBypass.support <+ w.support
-/
theorem support_cycleBypass_sublist_support : forall (w : G.Walk v v), w.cycleBypass.support <+ w.support
  | .nil => .refl _
  | .cons _ w => w.support_bypass_sublist_support.cons_cons _

open List in
/--
theorem `darts_cycleBypass_sublist_darts` / 定理 `darts_cycleBypass_sublist_darts`

English:
theorem darts_cycleBypass_sublist_darts
  statement: forall (w : G.Walk v v), w.cycleBypass.darts <+ w.darts

中文:
定理 darts_cycleBypass_sublist_darts
  结论: 对任意 (w : G.途径 v v), w.cycleBypass.darts <+ w.darts
-/
theorem darts_cycleBypass_sublist_darts : forall (w : G.Walk v v), w.cycleBypass.darts <+ w.darts
  | .nil => .refl _
  | .cons _ w => w.darts_bypass_sublist_darts.cons_cons _

open List in
/--
theorem `edges_cycleBypass_sublist_edges` / 定理 `edges_cycleBypass_sublist_edges`

English:
theorem edges_cycleBypass_sublist_edges
  statement: forall (w : G.Walk v v), w.cycleBypass.edges <+ w.edges

中文:
定理 edges_cycleBypass_sublist_edges
  结论: 对任意 (w : G.途径 v v), w.cycleBypass.edges <+ w.edges
-/
theorem edges_cycleBypass_sublist_edges : forall (w : G.Walk v v), w.cycleBypass.edges <+ w.edges
  | .nil => .refl _
  | .cons _ w => w.edges_bypass_sublist_edges.cons_cons _

/--
lemma `edges_cycleBypass_subset_edges` / 引理 `edges_cycleBypass_subset_edges`

English:
lemma edges_cycleBypass_subset_edges
  given: (w : G.Walk v v)
  statement: w.cycleBypass.edges subseteq w.edges
  proof: w.edges_cycleBypass_sublist_edges.subset

@[deprecated (since := "2026-05-25")]
alias edges_cycleBypass_subset := edges_cycleBypass_subset_edges

中文:
引理 edges_cycleBypass_subset_edges
  条件: (w : G.途径 v v)
  结论: w.cycleBypass.edges subseteq w.edges
  证明: w.edges_cycleBypass_sublist_edges.subset

@[deprecated (since := "2026-05-25")]
alias edges_cycleBypass_subset := edges_cycleBypass_subset_edges

Depends on / 依赖: edges_cycleBypass_sublist_edges, subset, w.edges_cycleBypass_sublist_edges.subset
-/
lemma edges_cycleBypass_subset_edges (w : G.Walk v v) : w.cycleBypass.edges subseteq w.edges :=
  w.edges_cycleBypass_sublist_edges.subset

@[deprecated (since := "2026-05-25")]
alias edges_cycleBypass_subset := edges_cycleBypass_subset_edges

/--
lemma `length_cycleBypass_le_length` / 引理 `length_cycleBypass_le_length`

English:
lemma length_cycleBypass_le_length
  given: (w : G.Walk v v)
  statement: w.cycleBypass.length <= w.length
  proof: by
  simpa using w.darts_cycleBypass_sublist_darts.length_le

中文:
引理 length_cycleBypass_le_length
  条件: (w : G.途径 v v)
  结论: w.cycleBypass.length <= w.length
  证明: by
  simpa using w.darts_cycleBypass_sublist_darts.length_le

Depends on / 依赖: darts_cycleBypass_sublist_darts, length_le, w.darts_cycleBypass_sublist_darts.length_le
-/
lemma length_cycleBypass_le_length (w : G.Walk v v) : w.cycleBypass.length <= w.length := by
  simpa using w.darts_cycleBypass_sublist_darts.length_le

/--
lemma `IsCircuit.isCycle_cycleBypass` / 引理 `IsCircuit.isCycle_cycleBypass`

English:
lemma IsCircuit.isCycle_cycleBypass
  statement: forall {w : G.Walk v v}, w.IsCircuit -> w.cycleBypass.IsCycle

中文:
引理 是Circuit.isCycle_cycleBypass
  结论: 对任意 {w : G.途径 v v}, w.是Circuit -> w.cycleBypass.是环

Depends on / 依赖: and_true, bypass_isPath, cycleBypass, edges_bypass_subset_edges, isCircuit_def, isTrail, isTrail.cons, isTrail_cons, ne_eq, not_false_eq_true, reduceCtorEq, support_nodup
-/
lemma IsCircuit.isCycle_cycleBypass : forall {w : G.Walk v v}, w.IsCircuit -> w.cycleBypass.IsCycle
  | .cons (v := v') hvv' w, hw => by
    dsimp [cycleBypass]
    refine ⟨⟨(bypass_isPath _).isTrail.cons _ fun hvv' => ?_, by simp⟩, ?_⟩
    · simp only [isCircuit_def, isTrail_cons, ne_eq, reduceCtorEq, not_false_eq_true,
        and_true] at hw
exact hw.2 edges_bypass_subset_edges _ hvv'
    · simpa using (bypass_isPath _).support_nodup

/--
lemma `IsTrail.isCycle_cycleBypass` / 引理 `IsTrail.isCycle_cycleBypass`

English:
lemma IsTrail.isCycle_cycleBypass
  given: {w : G.Walk v v} (hw : w != .nil) (hw' : w.IsTrail)
  proof: (w.isCircuit_def.mpr ⟨hw', hw⟩).isCycle_cycleBypass

中文:
引理 是Trail.isCycle_cycleBypass
  条件: {w : G.途径 v v} (hw : w != .nil) (hw' : w.是Trail)
  证明: (w.isCircuit_def.mpr ⟨hw', hw⟩).isCycle_cycleBypass

Depends on / 依赖: isCircuit_def, isCycle_cycleBypass, w.isCircuit_def.mpr
-/
lemma IsTrail.isCycle_cycleBypass {w : G.Walk v v} (hw : w != .nil) (hw' : w.IsTrail) :
    w.cycleBypass.IsCycle :=
  (w.isCircuit_def.mpr ⟨hw', hw⟩).isCycle_cycleBypass

end Walk

/-! ### Mapping paths -/

namespace Walk

variable {G G'} {f : G ->g G'} {u v : V} {p : G.Walk u v}

/--
theorem `IsTrail.of_map` / 定理 `IsTrail.of_map`

English:
theorem IsTrail.of_map
  given: (hp : (p.map f).IsTrail)
  statement: p.IsTrail
  proof: by
  rw [isTrail_def]
  rw [isTrail_def]; rw [edges_map] at hp
  exact hp.of_map

中文:
定理 是Trail.of_map
  条件: (hp : (p.map f).是Trail)
  结论: p.是Trail
  证明: by
  rw [isTrail_def]
  rw [isTrail_def]; rw [edges_map] at hp
  exact hp.of_map
-/
protected theorem IsTrail.of_map (hp : (p.map f).IsTrail) : p.IsTrail := by
  rw [isTrail_def]
  rw [isTrail_def]; rw [edges_map] at hp
  exact hp.of_map

/--
theorem `isTrail_map_iff_of_injective` / 定理 `isTrail_map_iff_of_injective`

English:
theorem isTrail_map_iff_of_injective
  given: (hinj : Function.Injective f)
  proof: by
  rw [isTrail_def]; rw [isTrail_def]; rw [edges_map]; rw [List.nodup_map_iff <| Sym2.map.injective hinj]

@[deprecated (since := "2026-06-16")]
alias map_isTrail_iff_of_injective := isTrail_map_iff_of_injective

alias ⟨_, IsTrail.map⟩ := isTrail_map_iff_of_injective

@[deprecated (since := "2026-

中文:
定理 isTrail_map_iff_of_injective
  条件: (hinj : 函数.单射 f)
  证明: by
  rw [isTrail_def]; rw [isTrail_def]; rw [edges_map]; rw [List.nodup_map_iff <| Sym2.map.injective hinj]

@[deprecated (since := "2026-06-16")]
alias map_isTrail_iff_of_injective := isTrail_map_iff_of_injective

alias ⟨_, IsTrail.map⟩ := isTrail_map_iff_of_injective

@[deprecated (since := "2026-

Depends on / 依赖: List.nodup_map_iff, Sym2.map.injective, edges_map, injective, isTrail_def, nodup_map_iff
-/
theorem isTrail_map_iff_of_injective (hinj : Function.Injective f) :
    (p.map f).IsTrail ↔ p.IsTrail := by
  rw [isTrail_def]; rw [isTrail_def]; rw [edges_map]; rw [List.nodup_map_iff <| Sym2.map.injective hinj]

@[deprecated (since := "2026-06-16")]
alias map_isTrail_iff_of_injective := isTrail_map_iff_of_injective

alias ⟨_, IsTrail.map⟩ := isTrail_map_iff_of_injective

@[deprecated (since := "2026-06-16")] alias map_isTrail_of_injective := IsTrail.map

/--
theorem `IsPath.of_map` / 定理 `IsPath.of_map`

English:
theorem IsPath.of_map
  given: (hp : (p.map f).IsPath)
  statement: p.IsPath
  proof: by
  rw [isPath_def]
  rw [isPath_def]; rw [support_map] at hp
  exact hp.of_map

中文:
定理 是道路.of_map
  条件: (hp : (p.map f).是道路)
  结论: p.是道路
  证明: by
  rw [isPath_def]
  rw [isPath_def]; rw [support_map] at hp
  exact hp.of_map
-/
protected theorem IsPath.of_map (hp : (p.map f).IsPath) : p.IsPath := by
  rw [isPath_def]
  rw [isPath_def]; rw [support_map] at hp
  exact hp.of_map

/--
theorem `isPath_map_iff_of_injective` / 定理 `isPath_map_iff_of_injective`

English:
theorem isPath_map_iff_of_injective
  given: (hinj : Function.Injective f)
  proof: by
  rw [isPath_def]; rw [isPath_def]; rw [support_map]; rw [List.nodup_map_iff hinj]

@[deprecated (since := "2026-06-16")]
alias map_isPath_iff_of_injective := isPath_map_iff_of_injective

alias ⟨_, IsPath.map⟩ := isPath_map_iff_of_injective

@[deprecated (since := "2026-06-16")] alias map_isPath_

中文:
定理 isPath_map_iff_of_injective
  条件: (hinj : 函数.单射 f)
  证明: by
  rw [isPath_def]; rw [isPath_def]; rw [support_map]; rw [List.nodup_map_iff hinj]

@[deprecated (since := "2026-06-16")]
alias map_isPath_iff_of_injective := isPath_map_iff_of_injective

alias ⟨_, IsPath.map⟩ := isPath_map_iff_of_injective

@[deprecated (since := "2026-06-16")] alias map_isPath_

Depends on / 依赖: List.nodup_map_iff, isPath_def, nodup_map_iff, support_map
-/
theorem isPath_map_iff_of_injective (hinj : Function.Injective f) :
    (p.map f).IsPath ↔ p.IsPath := by
  rw [isPath_def]; rw [isPath_def]; rw [support_map]; rw [List.nodup_map_iff hinj]

@[deprecated (since := "2026-06-16")]
alias map_isPath_iff_of_injective := isPath_map_iff_of_injective

alias ⟨_, IsPath.map⟩ := isPath_map_iff_of_injective

@[deprecated (since := "2026-06-16")] alias map_isPath_of_injective := IsPath.map

/--
theorem `IsCircuit.of_map` / 定理 `IsCircuit.of_map`

English:
theorem IsCircuit.of_map
  given: {p : G.Walk u u} (hp : (p.map f).IsCircuit)
  statement: p.IsCircuit
  proof: by
  rw [isCircuit_def]; rw [ne_eq]; rw [eq_nil_iff_nil]
  rw [isCircuit_def]; rw [ne_eq]; rw [eq_nil_iff_nil]; rw [nil_map_iff] at hp
  exact hp.imp_left .of_map

中文:
定理 是Circuit.of_map
  条件: {p : G.途径 u u} (hp : (p.map f).是Circuit)
  结论: p.是Circuit
  证明: by
  rw [isCircuit_def]; rw [ne_eq]; rw [eq_nil_iff_nil]
  rw [isCircuit_def]; rw [ne_eq]; rw [eq_nil_iff_nil]; rw [nil_map_iff] at hp
  exact hp.imp_left .of_map
-/
protected theorem IsCircuit.of_map {p : G.Walk u u} (hp : (p.map f).IsCircuit) : p.IsCircuit := by
  rw [isCircuit_def]; rw [ne_eq]; rw [eq_nil_iff_nil]
  rw [isCircuit_def]; rw [ne_eq]; rw [eq_nil_iff_nil]; rw [nil_map_iff] at hp
  exact hp.imp_left .of_map

/--
theorem `isCircuit_map_iff_of_injective` / 定理 `isCircuit_map_iff_of_injective`

English:
theorem isCircuit_map_iff_of_injective
  given: {p : G.Walk u u} (hinj : Function.Injective f)
  proof: by
  rw [isCircuit_def]; rw [isCircuit_def]; rw [isTrail_map_iff_of_injective hinj]; rw [ne_eq]; rw [ne_eq]; rw [eq_nil_iff_nil]; rw [eq_nil_iff_nil]; rw [nil_map_iff]

alias ⟨_, IsCircuit.map⟩ := isCircuit_map_iff_of_injective

中文:
定理 isCircuit_map_iff_of_injective
  条件: {p : G.途径 u u} (hinj : 函数.单射 f)
  证明: by
  rw [isCircuit_def]; rw [isCircuit_def]; rw [isTrail_map_iff_of_injective hinj]; rw [ne_eq]; rw [ne_eq]; rw [eq_nil_iff_nil]; rw [eq_nil_iff_nil]; rw [nil_map_iff]

alias ⟨_, IsCircuit.map⟩ := isCircuit_map_iff_of_injective

Depends on / 依赖: eq_nil_iff_nil, isCircuit_def, isTrail_map_iff_of_injective, ne_eq, nil_map_iff
-/
theorem isCircuit_map_iff_of_injective {p : G.Walk u u} (hinj : Function.Injective f) :
    (p.map f).IsCircuit ↔ p.IsCircuit := by
  rw [isCircuit_def]; rw [isCircuit_def]; rw [isTrail_map_iff_of_injective hinj]; rw [ne_eq]; rw [ne_eq]; rw [eq_nil_iff_nil]; rw [eq_nil_iff_nil]; rw [nil_map_iff]

alias ⟨_, IsCircuit.map⟩ := isCircuit_map_iff_of_injective

/--
theorem `IsCycle.of_map` / 定理 `IsCycle.of_map`

English:
theorem IsCycle.of_map
  given: {p : G.Walk u u} (hp : (p.map f).IsCycle)
  statement: p.IsCycle
  proof: by
  rw [isCycle_def]; rw [ne_eq]; rw [eq_nil_iff_nil]
  rw [isCycle_def]; rw [ne_eq]; rw [eq_nil_iff_nil]; rw [nil_map_iff]; rw [support_map]; rw [← List.map_tail] at hp
exact hp.imp .of_map .imp_right .of_map f

中文:
定理 是环.of_map
  条件: {p : G.途径 u u} (hp : (p.map f).是环)
  结论: p.是环
  证明: by
  rw [isCycle_def]; rw [ne_eq]; rw [eq_nil_iff_nil]
  rw [isCycle_def]; rw [ne_eq]; rw [eq_nil_iff_nil]; rw [nil_map_iff]; rw [support_map]; rw [← List.map_tail] at hp
exact hp.imp .of_map .imp_right .of_map f
-/
protected theorem IsCycle.of_map {p : G.Walk u u} (hp : (p.map f).IsCycle) : p.IsCycle := by
  rw [isCycle_def]; rw [ne_eq]; rw [eq_nil_iff_nil]
  rw [isCycle_def]; rw [ne_eq]; rw [eq_nil_iff_nil]; rw [nil_map_iff]; rw [support_map]; rw [← List.map_tail] at hp
exact hp.imp .of_map .imp_right .of_map f

/--
theorem `isCycle_map_iff_of_injective` / 定理 `isCycle_map_iff_of_injective`

English:
theorem isCycle_map_iff_of_injective
  given: {p : G.Walk u u} (hinj : Function.Injective f)
  proof: by
  rw [isCycle_def]; rw [isCycle_def]; rw [isTrail_map_iff_of_injective hinj]; rw [ne_eq]; rw [ne_eq]; rw [eq_nil_iff_nil]; rw [eq_nil_iff_nil]; rw [nil_map_iff]; rw [support_map]; rw [← List.map_tail]; rw [List.nodup_map_iff hinj]

@[deprecated (since := "2026-06-16")]
alias map_isCycle_iff_of_in

中文:
定理 isCycle_map_iff_of_injective
  条件: {p : G.途径 u u} (hinj : 函数.单射 f)
  证明: by
  rw [isCycle_def]; rw [isCycle_def]; rw [isTrail_map_iff_of_injective hinj]; rw [ne_eq]; rw [ne_eq]; rw [eq_nil_iff_nil]; rw [eq_nil_iff_nil]; rw [nil_map_iff]; rw [support_map]; rw [← List.map_tail]; rw [List.nodup_map_iff hinj]

@[deprecated (since := "2026-06-16")]
alias map_isCycle_iff_of_in

Depends on / 依赖: List.map_tail, List.nodup_map_iff, eq_nil_iff_nil, isCycle_def, isTrail_map_iff_of_injective, map_tail, ne_eq, nil_map_iff, nodup_map_iff, support_map
-/
theorem isCycle_map_iff_of_injective {p : G.Walk u u} (hinj : Function.Injective f) :
    (p.map f).IsCycle ↔ p.IsCycle := by
  rw [isCycle_def]; rw [isCycle_def]; rw [isTrail_map_iff_of_injective hinj]; rw [ne_eq]; rw [ne_eq]; rw [eq_nil_iff_nil]; rw [eq_nil_iff_nil]; rw [nil_map_iff]; rw [support_map]; rw [← List.map_tail]; rw [List.nodup_map_iff hinj]

@[deprecated (since := "2026-06-16")]
alias map_isCycle_iff_of_injective := isCycle_map_iff_of_injective

alias ⟨_, IsCycle.map⟩ := isCycle_map_iff_of_injective

@[simp]
/--
theorem `isTrail_mapLe` / 定理 `isTrail_mapLe`

English:
theorem isTrail_mapLe
  given: {G G' : SimpleGraph V} (h : G <= G') {u v : V} {p : G.Walk u v}
  proof: isTrail_map_iff_of_injective Function.injective_id

@[deprecated (since := "2026-06-16")] alias mapLe_isTrail := isTrail_mapLe

alias ⟨IsTrail.of_mapLe, IsTrail.mapLe⟩ := isTrail_mapLe

@[simp]

中文:
定理 isTrail_mapLe
  条件: {G G' : 简单图 V} (h : G <= G') {u v : V} {p : G.途径 u v}
  证明: isTrail_map_iff_of_injective Function.injective_id

@[deprecated (since := "2026-06-16")] alias mapLe_isTrail := isTrail_mapLe

alias ⟨IsTrail.of_mapLe, IsTrail.mapLe⟩ := isTrail_mapLe

@[simp]

Depends on / 依赖: Function, Function.injective_id, injective_id, isTrail_map_iff_of_injective
-/
theorem isTrail_mapLe {G G' : SimpleGraph V} (h : G <= G') {u v : V} {p : G.Walk u v} :
    (p.mapLe h).IsTrail ↔ p.IsTrail :=
  isTrail_map_iff_of_injective Function.injective_id

@[deprecated (since := "2026-06-16")] alias mapLe_isTrail := isTrail_mapLe

alias ⟨IsTrail.of_mapLe, IsTrail.mapLe⟩ := isTrail_mapLe

@[simp]
/--
theorem `isPath_mapLe` / 定理 `isPath_mapLe`

English:
theorem isPath_mapLe
  given: {G G' : SimpleGraph V} (h : G <= G') {u v : V} {p : G.Walk u v}
  proof: isPath_map_iff_of_injective Function.injective_id

@[deprecated (since := "2026-06-16")] alias mapLe_isPath := isPath_mapLe

alias ⟨IsPath.of_mapLe, IsPath.mapLe⟩ := isPath_mapLe

@[simp]

中文:
定理 isPath_mapLe
  条件: {G G' : 简单图 V} (h : G <= G') {u v : V} {p : G.途径 u v}
  证明: isPath_map_iff_of_injective Function.injective_id

@[deprecated (since := "2026-06-16")] alias mapLe_isPath := isPath_mapLe

alias ⟨IsPath.of_mapLe, IsPath.mapLe⟩ := isPath_mapLe

@[simp]

Depends on / 依赖: Function, Function.injective_id, injective_id, isPath_map_iff_of_injective
-/
theorem isPath_mapLe {G G' : SimpleGraph V} (h : G <= G') {u v : V} {p : G.Walk u v} :
    (p.mapLe h).IsPath ↔ p.IsPath :=
  isPath_map_iff_of_injective Function.injective_id

@[deprecated (since := "2026-06-16")] alias mapLe_isPath := isPath_mapLe

alias ⟨IsPath.of_mapLe, IsPath.mapLe⟩ := isPath_mapLe

@[simp]
/--
theorem `isCircuit_mapLe` / 定理 `isCircuit_mapLe`

English:
theorem isCircuit_mapLe
  given: {G G' : SimpleGraph V} (h : G <= G') {u : V} {p : G.Walk u u}
  proof: isCircuit_map_iff_of_injective Function.injective_id

alias ⟨IsCircuit.of_mapLe, IsCircuit.mapLe⟩ := isCircuit_mapLe

@[simp]

中文:
定理 isCircuit_mapLe
  条件: {G G' : 简单图 V} (h : G <= G') {u : V} {p : G.途径 u u}
  证明: isCircuit_map_iff_of_injective Function.injective_id

alias ⟨IsCircuit.of_mapLe, IsCircuit.mapLe⟩ := isCircuit_mapLe

@[simp]

Depends on / 依赖: Function, Function.injective_id, injective_id, isCircuit_map_iff_of_injective
-/
theorem isCircuit_mapLe {G G' : SimpleGraph V} (h : G <= G') {u : V} {p : G.Walk u u} :
    (p.mapLe h).IsCircuit ↔ p.IsCircuit :=
  isCircuit_map_iff_of_injective Function.injective_id

alias ⟨IsCircuit.of_mapLe, IsCircuit.mapLe⟩ := isCircuit_mapLe

@[simp]
/--
theorem `isCycle_mapLe` / 定理 `isCycle_mapLe`

English:
theorem isCycle_mapLe
  given: {G G' : SimpleGraph V} (h : G <= G') {u : V} {p : G.Walk u u}
  proof: isCycle_map_iff_of_injective Function.injective_id

@[deprecated (since := "2026-06-16")] alias mapLe_isCycle := isCycle_mapLe

alias ⟨IsCycle.of_mapLe, IsCycle.mapLe⟩ := isCycle_mapLe

中文:
定理 isCycle_mapLe
  条件: {G G' : 简单图 V} (h : G <= G') {u : V} {p : G.途径 u u}
  证明: isCycle_map_iff_of_injective Function.injective_id

@[deprecated (since := "2026-06-16")] alias mapLe_isCycle := isCycle_mapLe

alias ⟨IsCycle.of_mapLe, IsCycle.mapLe⟩ := isCycle_mapLe

Depends on / 依赖: Function, Function.injective_id, injective_id, isCycle_map_iff_of_injective
-/
theorem isCycle_mapLe {G G' : SimpleGraph V} (h : G <= G') {u : V} {p : G.Walk u u} :
    (p.mapLe h).IsCycle ↔ p.IsCycle :=
  isCycle_map_iff_of_injective Function.injective_id

@[deprecated (since := "2026-06-16")] alias mapLe_isCycle := isCycle_mapLe

alias ⟨IsCycle.of_mapLe, IsCycle.mapLe⟩ := isCycle_mapLe

end Walk

namespace Path

variable {G G'}

/-- Given an injective graph homomorphism, map paths to paths. -/
@[simps]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : G ->g G') (hinj : Function.Injective f) {u v : V} (p : G.Path u v)
  body: ⟨Walk.map f p, p.isPath.map hinj⟩

中文:
定义 map
  签名: (f : G ->g G') (hinj : 函数.单射 f) {u v : V} (p : G.道路 u v)
  定义体: ⟨Walk.map f p, p.isPath.map hinj⟩
-/
protected def map (f : G ->g G') (hinj : Function.Injective f) {u v : V} (p : G.Path u v) :
    G'.Path (f u) (f v) :=
  ⟨Walk.map f p, p.isPath.map hinj⟩

/--
theorem `map_injective` / 定理 `map_injective`

English:
theorem map_injective
  given: {f : G ->g G'} (hinj : Function.Injective f) (u v : V)
  proof: by
  rintro ⟨p, hp⟩ ⟨p', hp'⟩ h
  simp only [Path.map, Subtype.mk.injEq] at h
  simp [Walk.map_injective_of_injective hinj u v h]

中文:
定理 map_injective
  条件: {f : G ->g G'} (hinj : 函数.单射 f) (u v : V)
  证明: by
  rintro ⟨p, hp⟩ ⟨p', hp'⟩ h
  simp only [Path.map, Subtype.mk.injEq] at h
  simp [Walk.map_injective_of_injective hinj u v h]

Depends on / 依赖: Path.map, Subtype, Subtype.mk.injEq, Walk.map_injective_of_injective, map_injective_of_injective
-/
theorem map_injective {f : G ->g G'} (hinj : Function.Injective f) (u v : V) :
    Function.Injective (Path.map f hinj : G.Path u v -> G'.Path (f u) (f v)) := by
  rintro ⟨p, hp⟩ ⟨p', hp'⟩ h
  simp only [Path.map, Subtype.mk.injEq] at h
  simp [Walk.map_injective_of_injective hinj u v h]

/-- Given a graph embedding, map paths to paths. -/
@[simps!]
/--
Definition of `mapEmbedding` / `mapEmbedding` 的定义

English:
definition mapEmbedding
  signature: (f : G ↪g G') {u v : V} (p : G.Path u v)
  body: Path.map f.toHom f.injective p

中文:
定义 mapEmbedding
  签名: (f : G ↪g G') {u v : V} (p : G.道路 u v)
  定义体: Path.map f.toHom f.injective p
-/
protected def mapEmbedding (f : G ↪g G') {u v : V} (p : G.Path u v) : G'.Path (f u) (f v) :=
  Path.map f.toHom f.injective p

/--
theorem `mapEmbedding_injective` / 定理 `mapEmbedding_injective`

English:
theorem mapEmbedding_injective
  given: (f : G ↪g G') (u v : V)
  proof: map_injective f.injective u v

中文:
定理 mapEmbedding_injective
  条件: (f : G ↪g G') (u v : V)
  证明: map_injective f.injective u v

Depends on / 依赖: f.injective, injective, map_injective
-/
theorem mapEmbedding_injective (f : G ↪g G') (u v : V) :
    Function.Injective (Path.mapEmbedding f : G.Path u v -> G'.Path (f u) (f v)) :=
  map_injective f.injective u v

end Path

/-! ### Transferring between graphs -/

namespace Walk

variable {G} {u v : V} {H : SimpleGraph V}
variable {p : G.Walk u v}

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `IsPath.transfer` / 定理 `IsPath.transfer`

English:
theorem IsPath.transfer
  given: (hp) (pp : p.IsPath)
  proof: by
  induction p with
  | nil => simp
  | cons _ _ ih =>
    simp only [Walk.transfer, cons_isPath_iff, support_transfer _] at pp ⊢
    exact ⟨ih _ pp.1, pp.2⟩

中文:
定理 是道路.transfer
  条件: (hp) (pp : p.是道路)
  证明: by
  induction p with
  | nil => simp
  | cons _ _ ih =>
    simp only [Walk.transfer, cons_isPath_iff, support_transfer _] at pp ⊢
    exact ⟨ih _ pp.1, pp.2⟩
-/
protected theorem IsPath.transfer (hp) (pp : p.IsPath) :
    (p.transfer H hp).IsPath := by
  induction p with
  | nil => simp
  | cons _ _ ih =>
    simp only [Walk.transfer, cons_isPath_iff, support_transfer _] at pp ⊢
    exact ⟨ih _ pp.1, pp.2⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `IsCycle.transfer` / 定理 `IsCycle.transfer`

English:
theorem IsCycle.transfer
  given: {q : G.Walk u u} (qc : q.IsCycle) (hq)
  proof: by
  cases q with
  | nil => simp at qc
  | cons _ q =>
    simp only [edges_cons, List.mem_cons, forall_eq_or_imp] at hq
    simp only [Walk.transfer, cons_isCycle_iff, edges_transfer q hq.2] at qc ⊢
    exact ⟨qc.1.transfer hq.2, qc.2⟩

中文:
定理 是环.transfer
  条件: {q : G.途径 u u} (qc : q.是环) (hq)
  证明: by
  cases q with
  | nil => simp at qc
  | cons _ q =>
    simp only [edges_cons, List.mem_cons, forall_eq_or_imp] at hq
    simp only [Walk.transfer, cons_isCycle_iff, edges_transfer q hq.2] at qc ⊢
    exact ⟨qc.1.transfer hq.2, qc.2⟩
-/
protected theorem IsCycle.transfer {q : G.Walk u u} (qc : q.IsCycle) (hq) :
    (q.transfer H hq).IsCycle := by
  cases q with
  | nil => simp at qc
  | cons _ q =>
    simp only [edges_cons, List.mem_cons, forall_eq_or_imp] at hq
    simp only [Walk.transfer, cons_isCycle_iff, edges_transfer q hq.2] at qc ⊢
    exact ⟨qc.1.transfer hq.2, qc.2⟩

end Walk

/-! ## Deleting edges -/

namespace Walk

variable {v w : V}

/--
theorem `IsPath.toDeleteEdges` / 定理 `IsPath.toDeleteEdges`

English:
theorem IsPath.toDeleteEdges
  statement: (s : Set (Sym2 V))
  proof: h.transfer _

中文:
定理 是道路.toDeleteEdges
  结论: (s : 集合 (Sym2 V))
  证明: h.transfer _
-/
protected theorem IsPath.toDeleteEdges (s : Set (Sym2 V))
    {p : G.Walk v w} (h : p.IsPath) (hp) : (p.toDeleteEdges s hp).IsPath :=
  h.transfer _

/--
theorem `IsCycle.toDeleteEdges` / 定理 `IsCycle.toDeleteEdges`

English:
theorem IsCycle.toDeleteEdges
  statement: (s : Set (Sym2 V))
  proof: h.transfer _

@[simp]

中文:
定理 是环.toDeleteEdges
  结论: (s : 集合 (Sym2 V))
  证明: h.transfer _

@[simp]
-/
protected theorem IsCycle.toDeleteEdges (s : Set (Sym2 V))
    {p : G.Walk v v} (h : p.IsCycle) (hp) : (p.toDeleteEdges s hp).IsCycle :=
  h.transfer _

@[simp]
/--
theorem `toDeleteEdges_copy` / 定理 `toDeleteEdges_copy`

English:
theorem toDeleteEdges_copy
  statement: {v u u' v' : V} (s : Set (Sym2 V))
  proof: by
  subst_vars
  rfl

中文:
定理 toDeleteEdges_copy
  结论: {v u u' v' : V} (s : 集合 (Sym2 V))
  证明: by
  subst_vars
  rfl
-/
theorem toDeleteEdges_copy {v u u' v' : V} (s : Set (Sym2 V))
    (p : G.Walk u v) (hu : u = u') (hv : v = v') (h) :
    (p.copy hu hv).toDeleteEdges s h =
      (p.toDeleteEdges s (by subst_vars; exact h)).copy hu hv := by
  subst_vars
  rfl

end Walk

end SimpleGraph
