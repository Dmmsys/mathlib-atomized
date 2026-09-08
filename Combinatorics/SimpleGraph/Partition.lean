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

Graph partitions are graph colorings that do not name their colors.  They are adjoint in the
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

/-- A `Partition` of a simple graph `G` is a structure constituted by:
* `parts`: a set of subsets of the vertices `V` of `G`.
* `isPartition`: a proof that `parts` is a proper partition of `V`.
* `independent`: a proof that each element of `parts` doesn't have a pair of adjacent vertices.
-/
/-
**SimpleGraph.Partition** 是 Mathlib 中的一个归纳类型，位于命名空间 `SimpleGraph`。
形式化陈述：{V : Type u} → SimpleGraph V → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Partition` of a simple graph `G` is a structure constituted by:
* `parts`: a set of subsets of the vertices `V` of `G`.
* `isPartition`: a proof that `parts` is a proper partition of `V`.
* `independent`: a proof that each element of `parts` doesn't have a pair of adj
acent vertices.
-/
structure Partition where
  /-- A set of subsets of the vertices `V` of `G`. -/
  parts : Set (Set V)
  /-- A proof that `parts` is a proper partition of `V`. -/
  isPartition : Setoid.IsPartition parts
  /-- A proof that each element of `parts` doesn't have a pair of adjacent vertices. -/
  independent : ∀ s ∈ parts, IsAntichain G.Adj s

/-- Whether a partition `P` has at most `n` parts. A graph with a partition
satisfying this predicate called `n`-partite. (See `SimpleGraph.Partitionable`.) -/
/-
**SimpleGraph.Partition.PartsCardLe** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Parti
tion`。
形式化陈述：{V : Type u} → {G : SimpleGraph V} → G.Partition → ℕ → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Whether a partition `P` has at most `n` parts. A graph with a partition
satisfying this predicate called `n`-partite. (See `SimpleGraph.Partitionable`.)
-/
def Partition.PartsCardLe {G : SimpleGraph V} (P : G.Partition) (n : ℕ) : Prop :=
  ∃ h : P.parts.Finite, h.toFinset.card ≤ n

/-- Whether a graph is `n`-partite, which is whether its vertex set
can be partitioned in at most `n` independent sets. -/
/-
**SimpleGraph.Partitionable** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：Partitionable (n : Nat) : Prop
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Whether a graph is `n`-partite, which is whether its vertex set
can be partitioned in at most `n` independent sets.
-/
def Partitionable (n : ℕ) : Prop := ∃ P : G.Partition, P.PartsCardLe n

namespace Partition

variable {G}
variable (P : G.Partition)

/-- The part in the partition that `v` belongs to. -/
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/-
**SimpleGraph.Partition.partOfVertex** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Part
ition`。
形式化陈述：partOfVertex (v : V) : Set V
参数：v : V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def partOfVertex (v : V) : Set V := Classical.choose (P.isPartition.2 v)
/-
**SimpleGraph.Partition.partOfVertex_mem** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.
Partition`。
形式化陈述：partOfVertex_mem (v : V) : P.partOfVertex v in P.parts
参数：v : V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `SimpleGraph.Partition.isPartition`：∀ {V : Type u} {G : SimpleGraph V} (s
elf : G.Partition), Setoid.IsPartition self.parts
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem partOfVertex_mem (v : V) : P.partOfVertex v ∈ P.parts := by
  obtain ⟨h, -⟩ := (P.isPartition.2 v).choose_spec.1
  exact h
/-
**SimpleGraph.Partition.mem_partOfVertex** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.
Partition`。
形式化陈述：mem_partOfVertex (v : V) : v in P.partOfVertex v
参数：v : V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `SimpleGraph.Partition.isPartition`：∀ {V : Type u} {G : SimpleGraph V} (s
elf : G.Partition), Setoid.IsPartition self.parts
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem mem_partOfVertex (v : V) : v ∈ P.partOfVertex v := by
  obtain ⟨⟨_, h⟩, _⟩ := (P.isPartition.2 v).choose_spec
  exact h
/-
**SimpleGraph.Partition.partOfVertex_ne_of_adj** 是 Mathlib 中的一个定理，位于命名空间 `Simple
Graph.Partition`。
形式化陈述：partOfVertex_ne_of_adj {v w : V} (h : G.Adj v w) : P.partOfVertex v != P.p
artOfVertex w
参数：h : G.Adj v w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Partition.mem_partOfVertex`：mem_partOfVertex (v : V) : v in 
P.partOfVertex v
· 使用定理 `SimpleGraph.Partition.independent`：∀ {V : Type u} {G : SimpleGraph V} (s
elf : G.Partition), ∀ s ∈ self.parts, IsAntichain G.Adj s
· 使用定理 `SimpleGraph.Partition.partOfVertex_mem`：partOfVertex_mem (v : V) : P.par
tOfVertex v in P.parts
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.ne_of_adj`：ne_of_adj (h : G.Adj a b) : a != b
-/
theorem partOfVertex_ne_of_adj {v w : V} (h : G.Adj v w) : P.partOfVertex v ≠ P.partOfVertex w := by
  intro hn
  have hw := P.mem_partOfVertex w
  rw [← hn] at hw
  exact P.independent _ (P.partOfVertex_mem v) (P.mem_partOfVertex v) hw (G.ne_of_adj h) h

/-- Create a coloring using the parts themselves as the colors.
Each vertex is colored by the part it's contained in. -/
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/-
**SimpleGraph.Partition.toColoring** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Partit
ion`。
形式化陈述：toColoring : G.Coloring P.parts
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Partition.partOfVertex_mem`：partOfVertex_mem (v : V) : P.par
tOfVertex v in P.parts
-/
noncomputable def toColoring : G.Coloring P.parts :=
  Coloring.mk (fun v ↦ ⟨P.partOfVertex v, P.partOfVertex_mem v⟩) fun hvw ↦ by
    rw [Ne, Subtype.mk_eq_mk]
    exact P.partOfVertex_ne_of_adj hvw

/-- Like `SimpleGraph.Partition.toColoring` but uses `Set V` as the coloring type. -/
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/-
**SimpleGraph.Partition.toColoring'** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Parti
tion`。
形式化陈述：toColoring' : G.Coloring (Set V)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Partition.partOfVertex_ne_of_adj`：partOfVertex_ne_of_adj {v 
w : V} (h : G.Adj v w) : P.partOfVertex v != P.partOfVertex w
-/
noncomputable def toColoring' : G.Coloring (Set V) :=
  Coloring.mk P.partOfVertex fun hvw ↦ P.partOfVertex_ne_of_adj hvw
/-
**SimpleGraph.Partition.colorable** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Partiti
on`。
形式化陈述：colorable [Fintype P.parts] : G.Colorable (Fintype.card P.parts)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Coloring.colorable`：∀ {V : Type u} {G : SimpleGraph V} {α : 
Type u_2} [inst : Fintype α] (C : G.Coloring α), G.Colorable (Fintype.card α)
-/
theorem colorable [Fintype P.parts] : G.Colorable (Fintype.card P.parts) :=
  P.toColoring.colorable

end Partition

variable {G}

/-- Creates a partition from a coloring. -/
@[simps]
/-
**SimpleGraph.Coloring.toPartition** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Colori
ng`。
形式化陈述：{V : Type u} → {G : SimpleGraph V} → {α : Type v} → G.Coloring α → G.Parti
tion
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Coloring.colorClasses_isPartition`：∀ {V : Type u} {G : Simpl
eGraph V} {α : Type u_2} (C : G.Coloring α), Setoid.IsPartition C.colorClasses

--- 原说明 ---
Creates a partition from a coloring.
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
/-
**SimpleGraph.Partition.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph.Partition`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The partition where every vertex is in its own part.
-/
instance : Inhabited (Partition G) := ⟨G.selfColoring.toPartition⟩
end Partition

set_option backward.isDefEq.respectTransparency false in
/-
**SimpleGraph.partitionable_iff_colorable** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph
`。
形式化陈述：partitionable_iff_colorable {n : Nat} : G.Partitionable n ↔ G.Colorable n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Colorable.mono`：∀ {V : Type u} {G : SimpleGraph V} {n m : ℕ}
, n ≤ m → G.Colorable n → G.Colorable m
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Finite.card_toFinset`：∀ {α : Type u} {s : Set α} [inst : Fintype ↑s]
 (h : s.Finite), h.toFinset.card = Fintype.card ↑s
· 使用定理 `SimpleGraph.Partition.colorable`：colorable [Fintype P.parts] : G.Colorab
le (Fintype.card P.parts)
· 使用定理 `SimpleGraph.Coloring.colorClasses_finite`：∀ {V : Type u} {G : SimpleGrap
h V} {α : Type u_2} (C : G.Coloring α) [Finite α], C.colorClasses.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `SimpleGraph.Coloring.card_colorClasses_le`：∀ {V : Type u} {G : SimpleGra
ph V} {α : Type u_2} (C : G.Coloring α) [inst : Fintype α]   [inst_1 : Fintype ↑
C.colorClasses], Fintype.card ↑…
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
-/
theorem partitionable_iff_colorable {n : ℕ} : G.Partitionable n ↔ G.Colorable n := by
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

