/-
Copyright (c) 2021 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Kyle Miller
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

/-!
# Graph partitions

This module provides an interface for dealing with partitions on simple graphs. A partition of
a graph `G`, with vertices `V`, is a set `P` of disjoint nonempty subsets of `V` such that:

* The union of the subsets in `P` is `V`.

* Each element of `P` is an independent set. (Each subset contains no pair of adjacent vertices.)

Graph partitions are graph colorings that do not name their colors. They are adjoint in the
following sense. Given a graph coloring, there is an associated partition from the set of color
classes, and given a partition, there is an associated graph coloring from using the partition's
subsets as colors. Going from graph colorings to partitions and back makes a coloring "canonical":
all colors are given a canonical name and unused colors are removed. Going from partitions to
graph colorings and back is the identity.

## Main definitions

* `SimpleGraph.Partition` is a structure to represent a partition of a simple graph.

* `SimpleGraph.Partition.PartsCardLe` is whether a given partition is an `n`-partition.
  (a partition with at most `n` parts).

* `SimpleGraph.Partitionable n` is whether a given graph is `n`-partite.

* `SimpleGraph.Partition.toColoring` creates colorings from partitions.

* `SimpleGraph.Coloring.toPartition` creates partitions from colorings.

## Main statements

* `SimpleGraph.partitionable_iff_colorable` is that `n`-partitionability and
  `n`-colorability are equivalent.

-/

@[expose] public section

assert_not_exists Field

universe u v

namespace SimpleGraph

variable {V : Type u} (G : SimpleGraph V)

/--
Definition of `Partition` / `Partition` 的定义

English:
structure Partition
  parameters: where
  axioms and operations (3):
    - parts : Set (Set V)
    - isPartition : Setoid.IsPartition parts
    - independent : forall s in parts, IsAntichain G.Adj s

中文:
结构 Partition
  参数: where
  公理与运算 (3 个):
    - parts : Set (Set V)
    - isPartition : Setoid.IsPartition parts
    - independent : 对任意 s in parts, IsAntichain G.Adj s
-/
structure Partition where
  /-- A set of subsets of the vertices `V` of `G`. -/
  parts : Set (Set V)
  /-- A proof that `parts` is a proper partition of `V`. -/
  isPartition : Setoid.IsPartition parts
  /-- A proof that each element of `parts` doesn't have a pair of adjacent vertices. -/
  independent : forall s in parts, IsAntichain G.Adj s

/--
Definition of `Partition.PartsCardLe` / `Partition.PartsCardLe` 的定义

English:
definition Partition.PartsCardLe
  signature: {G : SimpleGraph V} (P : G.Partition) (n : Nat)
  body: exists h : P.parts.Finite, h.toFinset.card <= n

中文:
定义 Partition.PartsCardLe
  签名: {G : SimpleGraph V} (P : G.Partition) (n : 自然数)
  定义体: exists h : P.parts.Finite, h.toFinset.card <= n

Depends on / 依赖: Finite, P.parts.Finite, h.toFinset.card, toFinset
-/
def Partition.PartsCardLe {G : SimpleGraph V} (P : G.Partition) (n : Nat) : Prop :=
  exists h : P.parts.Finite, h.toFinset.card <= n

/--
Definition of `Partitionable` / `Partitionable` 的定义

English:
definition Partitionable
  signature: (n : Nat)
  body: exists P : G.Partition, P.PartsCardLe n

中文:
定义 Partitionable
  签名: (n : 自然数)
  定义体: exists P : G.Partition, P.PartsCardLe n

Depends on / 依赖: G.Partition, P.PartsCardLe, Partition, PartsCardLe
-/
def Partitionable (n : Nat) : Prop := exists P : G.Partition, P.PartsCardLe n

namespace Partition

variable {G}
variable (P : G.Partition)

-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/--
Definition of `partOfVertex` / `partOfVertex` 的定义

English:
definition partOfVertex
  signature: (v : V)
  body: Classical.choose (P.isPartition.2 v)

中文:
定义 partOfVertex
  签名: (v : V)
  定义体: Classical.choose (P.isPartition.2 v)

Depends on / 依赖: Classical, Classical.choose, P.isPartition, isPartition
-/
noncomputable def partOfVertex (v : V) : Set V := Classical.choose (P.isPartition.2 v)

/--
theorem `partOfVertex_mem` / 定理 `partOfVertex_mem`

English:
theorem partOfVertex_mem
  given: (v : V)
  statement: P.partOfVertex v in P.parts
  proof: by
  obtain ⟨h, -⟩ := (P.isPartition.2 v).choose_spec.1
  exact h

中文:
定理 partOfVertex_mem
  条件: (v : V)
  结论: P.partOfVertex v in P.parts
  证明: by
  obtain ⟨h, -⟩ := (P.isPartition.2 v).choose_spec.1
  exact h

Depends on / 依赖: P.isPartition, choose_spec, isPartition
-/
theorem partOfVertex_mem (v : V) : P.partOfVertex v in P.parts := by
  obtain ⟨h, -⟩ := (P.isPartition.2 v).choose_spec.1
  exact h

/--
theorem `mem_partOfVertex` / 定理 `mem_partOfVertex`

English:
theorem mem_partOfVertex
  given: (v : V)
  statement: v in P.partOfVertex v
  proof: by
  obtain ⟨⟨_, h⟩, _⟩ := (P.isPartition.2 v).choose_spec
  exact h

中文:
定理 mem_partOfVertex
  条件: (v : V)
  结论: v in P.partOfVertex v
  证明: by
  obtain ⟨⟨_, h⟩, _⟩ := (P.isPartition.2 v).choose_spec
  exact h

Depends on / 依赖: P.isPartition, choose_spec, isPartition
-/
theorem mem_partOfVertex (v : V) : v in P.partOfVertex v := by
  obtain ⟨⟨_, h⟩, _⟩ := (P.isPartition.2 v).choose_spec
  exact h

/--
theorem `partOfVertex_ne_of_adj` / 定理 `partOfVertex_ne_of_adj`

English:
theorem partOfVertex_ne_of_adj
  given: {v w : V} (h : G.Adj v w)
  statement: P.partOfVertex v != P.partOfVertex w
  proof: by
  intro hn
  have hw := P.mem_partOfVertex w
  rw [← hn] at hw
  exact P.independent _ (P.partOfVertex_mem v) (P.mem_partOfVertex v) hw (G.ne_of_adj h) h

中文:
定理 partOfVertex_ne_of_adj
  条件: {v w : V} (h : G.Adj v w)
  结论: P.partOfVertex v != P.partOfVertex w
  证明: by
  intro hn
  have hw := P.mem_partOfVertex w
  rw [← hn] at hw
  exact P.independent _ (P.partOfVertex_mem v) (P.mem_partOfVertex v) hw (G.ne_of_adj h) h

Depends on / 依赖: G.ne_of_adj, P.independent, P.mem_partOfVertex, P.partOfVertex_mem, independent, mem_partOfVertex, ne_of_adj, partOfVertex_mem
-/
theorem partOfVertex_ne_of_adj {v w : V} (h : G.Adj v w) : P.partOfVertex v != P.partOfVertex w := by
  intro hn
  have hw := P.mem_partOfVertex w
  rw [← hn] at hw
  exact P.independent _ (P.partOfVertex_mem v) (P.mem_partOfVertex v) hw (G.ne_of_adj h) h

-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/--
Definition of `toColoring` / `toColoring` 的定义

English:
definition toColoring
  signature: : G.Coloring P.parts
  body: Coloring.mk (fun v => ⟨P.partOfVertex v, P.partOfVertex_mem v⟩) fun hvw => by
    rw [Ne]; rw [Subtype.mk_eq_mk]
    exact P.partOfVertex_ne_of_adj hvw

中文:
定义 toColoring
  签名: : G.Coloring P.parts
  定义体: Coloring.mk (fun v => ⟨P.partOfVertex v, P.partOfVertex_mem v⟩) fun hvw => by
    rw [Ne]; rw [Subtype.mk_eq_mk]
    exact P.partOfVertex_ne_of_adj hvw

Depends on / 依赖: Coloring, Coloring.mk, P.partOfVertex, P.partOfVertex_mem, P.partOfVertex_ne_of_adj, Subtype, Subtype.mk_eq_mk, mk_eq_mk, partOfVertex, partOfVertex_mem, partOfVertex_ne_of_adj
-/
noncomputable def toColoring : G.Coloring P.parts :=
  Coloring.mk (fun v => ⟨P.partOfVertex v, P.partOfVertex_mem v⟩) fun hvw => by
    rw [Ne]; rw [Subtype.mk_eq_mk]
    exact P.partOfVertex_ne_of_adj hvw

-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/--
Definition of `toColoring'` / `toColoring'` 的定义

English:
definition toColoring'
  signature: : G.Coloring (Set V)
  body: Coloring.mk P.partOfVertex fun hvw => P.partOfVertex_ne_of_adj hvw

中文:
定义 toColoring'
  签名: : G.Coloring (Set V)
  定义体: Coloring.mk P.partOfVertex fun hvw => P.partOfVertex_ne_of_adj hvw

Depends on / 依赖: Coloring, Coloring.mk, P.partOfVertex, P.partOfVertex_ne_of_adj, partOfVertex, partOfVertex_ne_of_adj
-/
noncomputable def toColoring' : G.Coloring (Set V) :=
  Coloring.mk P.partOfVertex fun hvw => P.partOfVertex_ne_of_adj hvw

/--
theorem `colorable` / 定理 `colorable`

English:
theorem colorable
  given: [Fintype P.parts]
  statement: G.Colorable (Fintype.card P.parts)
  proof: P.toColoring.colorable

中文:
定理 colorable
  条件: [Fintype P.parts]
  结论: G.Colorable (Fintype.card P.parts)
  证明: P.toColoring.colorable

Depends on / 依赖: P.toColoring.colorable, colorable, toColoring
-/
theorem colorable [Fintype P.parts] : G.Colorable (Fintype.card P.parts) :=
  P.toColoring.colorable

end Partition

variable {G}

/-- Creates a partition from a coloring. -/
@[simps]
/--
Definition of `Coloring.toPartition` / `Coloring.toPartition` 的定义

English:
definition Coloring.toPartition
  signature: {α : Type v} (C : G.Coloring α)
  body: C.colorClasses
  isPartition := C.colorClasses_isPartition
  independent := by
    rintro s ⟨c, rfl⟩
    apply C.isIndepSet_colorClass

中文:
定义 Coloring.toPartition
  签名: {α : 类型v} (C : G.Coloring α)
  定义体: C.colorClasses
  isPartition := C.colorClasses_isPartition
  independent := by
    rintro s ⟨c, rfl⟩
    apply C.isIndepSet_colorClass

Depends on / 依赖: C.colorClasses, colorClasses
-/
def Coloring.toPartition {α : Type v} (C : G.Coloring α) : G.Partition where
  parts := C.colorClasses
  isPartition := C.colorClasses_isPartition
  independent := by
    rintro s ⟨c, rfl⟩
    apply C.isIndepSet_colorClass

namespace Partition
/-- The partition where every vertex is in its own part. -/
@[simps]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Partition G)
  body: ⟨G.selfColoring.toPartition⟩

中文:
实例 :
  签名: Inhabited (Partition G)
  定义体: ⟨G.selfColoring.toPartition⟩

Depends on / 依赖: G.selfColoring.toPartition, selfColoring, toPartition
-/
instance : Inhabited (Partition G) := ⟨G.selfColoring.toPartition⟩
end Partition

set_option backward.isDefEq.respectTransparency false in
/--
theorem `partitionable_iff_colorable` / 定理 `partitionable_iff_colorable`

English:
theorem partitionable_iff_colorable
  given: {n : Nat}
  statement: G.Partitionable n ↔ G.Colorable n
  proof: by
  constructor
  · rintro ⟨P, hf, hc⟩
    have : Fintype P.parts := hf.fintype
    rw [Set.Finite.card_toFinset hf] at hc
    apply P.colorable.mono hc
  · rintro ⟨C⟩
    refine ⟨C.toPartition, C.colorClasses_finite, le_trans ?_ (Fintype.card_fin n).le⟩
    generalize_proofs h
    change Set.Finit

中文:
定理 partitionable_iff_colorable
  条件: {n : 自然数}
  结论: G.Partitionable n ↔ G.Colorable n
  证明: by
  constructor
  · rintro ⟨P, hf, hc⟩
    have : Fintype P.parts := hf.fintype
    rw [Set.Finite.card_toFinset hf] at hc
    apply P.colorable.mono hc
  · rintro ⟨C⟩
    refine ⟨C.toPartition, C.colorClasses_finite, le_trans ?_ (Fintype.card_fin n).le⟩
    generalize_proofs h
    change Set.Finit

Depends on / 依赖: C.card_colorClasses_le, C.colorClasses, C.colorClasses_finite, C.colorClasses_finite.fintype, C.toPartition, Coloring, Coloring.colorClasses, Finite, Fintype, Fintype.card_fin, P.colorable.mono, P.parts, Set.Finite, Set.Finite.card_toFinset, card_colorClasses_le, card_fin, card_toFinset, colorClasses, colorClasses_finite, colorable
-/
theorem partitionable_iff_colorable {n : Nat} : G.Partitionable n ↔ G.Colorable n := by
  constructor
  · rintro ⟨P, hf, hc⟩
    have : Fintype P.parts := hf.fintype
    rw [Set.Finite.card_toFinset hf] at hc
    apply P.colorable.mono hc
  · rintro ⟨C⟩
    refine ⟨C.toPartition, C.colorClasses_finite, le_trans ?_ (Fintype.card_fin n).le⟩
    generalize_proofs h
    change Set.Finite (Coloring.colorClasses C) at h
    have : Fintype C.colorClasses := C.colorClasses_finite.fintype
    rw [h.card_toFinset]
    exact C.card_colorClasses_le

end SimpleGraph
