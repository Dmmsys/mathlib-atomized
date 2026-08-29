/-
Copyright (c) 2021 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Kyle Miller
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Data.Setoid.Partition
public import Mathlib.Order.Antichain
public import Mathlib.Order.Lattice.Nat

/-!
# Graph Coloring

This module defines colorings of simple graphs (also known as proper colorings in the literature).
A graph coloring is the attribution of "colors" to all of its vertices such that adjacent vertices
have different colors.
A coloring can be represented as a homomorphism into a complete graph, whose vertices represent
the colors.

## Main definitions

* `G.Coloring α` is the type of `α`-colorings of a simple graph `G`,
  with `α` being the set of available colors. The type is defined to
  be homomorphisms from `G` into the complete graph on `α`, and
  colorings have a coercion to `V → α`.

* `G.Colorable n` is the proposition that `G` is `n`-colorable, which
  is whether there exists a coloring with at most *n* colors.

* `G.chromaticNumber` is the minimal `n` such that `G` is `n`-colorable,
  or `⊤` if it cannot be colored with finitely many colors.
  (Cardinal-valued chromatic numbers are more niche, so we stick to `ℕ∞`.)
  We write `G.chromaticNumber ≠ ⊤` to mean a graph is colorable with finitely many colors.

* `C.colorClass c` is the set of vertices colored by `c : α` in the coloring `C : G.Coloring α`.

* `C.colorClasses` is the set containing all color classes.

## TODO

  * Gather material from:
    * https://github.com/leanprover-community/mathlib/blob/simple_graph_matching/src/combinatorics/simple_graph/coloring.lean
    * https://github.com/kmill/lean-graphcoloring/blob/master/src/graph.lean

  * Trees

  * Planar graphs

  * Chromatic polynomials

  * develop API for partial colorings, likely as colorings of subgraphs (`H.coe.Coloring α`)
-/

@[expose] public section

assert_not_exists Field

open Fintype Function

universe u v

namespace SimpleGraph

variable {V : Type u} (G : SimpleGraph V) {n : Nat}
/--
Definition of `Coloring` / `Coloring` 的定义

English:
abbreviation Coloring
  signature: (α : Type v)
  body: G ->g completeGraph α

中文:
缩写 染色
  签名: (α : 类型v)
  定义体: G ->g completeGraph α

Depends on / 依赖: completeGraph
-/
abbrev Coloring (α : Type v) := G ->g completeGraph α

variable {G}
variable {ι α β : Type*} (C : G.Coloring α)

/--
theorem `Coloring.valid` / 定理 `Coloring.valid`

English:
theorem Coloring.valid
  given: {v w : V} (h : G.Adj v w)
  statement: C v != C w
  proof: C.map_rel h

中文:
定理 染色.valid
  条件: {v w : V} (h : G.伴随 v w)
  结论: C v != C w
  证明: C.map_rel h

Depends on / 依赖: C.map_rel, map_rel
-/
theorem Coloring.valid {v w : V} (h : G.Adj v w) : C v != C w :=
  C.map_rel h

/--
lemma `Coloring.injective_comp_of_pairwise_adj` / 引理 `Coloring.injective_comp_of_pairwise_adj`

English:
lemma Coloring.injective_comp_of_pairwise_adj
  statement: (C : G.Coloring α) (f : ι -> V)
  proof: Function.injective_iff_pairwise_ne.2 hf.mono fun _ _ => C.valid

中文:
引理 染色.injective_comp_of_pairwise_adj
  结论: (C : G.染色 α) (f : ι -> V)
  证明: Function.injective_iff_pairwise_ne.2 hf.mono fun _ _ => C.valid

Depends on / 依赖: C.valid, Function, Function.injective_iff_pairwise_ne, hf.mono, injective_iff_pairwise_ne
-/
lemma Coloring.injective_comp_of_pairwise_adj (C : G.Coloring α) (f : ι -> V)
    (hf : Pairwise fun i j => G.Adj (f i) (f j)) : (C ∘ f).Injective :=
Function.injective_iff_pairwise_ne.2 hf.mono fun _ _ => C.valid

/-- Construct a term of `SimpleGraph.Coloring` using a function that
assigns vertices to colors and a proof that it is as proper coloring.

(Note: this is a definitionally the constructor for `SimpleGraph.Hom`,
but with a syntactically better proper coloring hypothesis.)
-/
@[match_pattern]
/--
Definition of `Coloring.mk` / `Coloring.mk` 的定义

English:
definition Coloring.mk
  signature: (color : V -> α) (valid : forall {v w : V}, G.Adj v w -> color v != color w)
  body: ⟨color, @valid⟩

中文:
定义 染色.mk
  签名: (color : V -> α) (valid : 对任意 {v w : V}, G.伴随 v w -> color v != color w)
  定义体: ⟨color, @valid⟩
-/
def Coloring.mk (color : V -> α) (valid : forall {v w : V}, G.Adj v w -> color v != color w) :
    G.Coloring α :=
  ⟨color, @valid⟩

/--
Definition of `Coloring.colorClass` / `Coloring.colorClass` 的定义

English:
definition Coloring.colorClass
  signature: (c : α)
  body: { v : V | C v = c }

中文:
定义 染色.colorClass
  签名: (c : α)
  定义体: { v : V | C v = c }
-/
def Coloring.colorClass (c : α) : Set V := { v : V | C v = c }

/--
Definition of `Coloring.colorClasses` / `Coloring.colorClasses` 的定义

English:
definition Coloring.colorClasses
  signature: : Set (Set V)
  body: (Setoid.ker C).classes

中文:
定义 染色.colorClasses
  签名: : 集合 (集合 V)
  定义体: (Setoid.ker C).classes

Depends on / 依赖: Setoid, Setoid.ker, classes
-/
def Coloring.colorClasses : Set (Set V) := (Setoid.ker C).classes

/--
theorem `Coloring.mem_colorClass` / 定理 `Coloring.mem_colorClass`

English:
theorem Coloring.mem_colorClass
  given: (v : V)
  statement: v in C.colorClass (C v)
  proof: rfl

中文:
定理 染色.mem_colorClass
  条件: (v : V)
  结论: v in C.colorClass (C v)
  证明: rfl
-/
theorem Coloring.mem_colorClass (v : V) : v in C.colorClass (C v) := rfl

/--
theorem `Coloring.colorClasses_isPartition` / 定理 `Coloring.colorClasses_isPartition`

English:
theorem Coloring.colorClasses_isPartition
  statement: Setoid.IsPartition C.colorClasses
  proof: Setoid.isPartition_classes (Setoid.ker C)

中文:
定理 染色.colorClasses_isPartition
  结论: 集合等价关系.IsPartition C.colorClasses
  证明: Setoid.isPartition_classes (Setoid.ker C)

Depends on / 依赖: Setoid, Setoid.isPartition_classes, Setoid.ker, isPartition_classes
-/
theorem Coloring.colorClasses_isPartition : Setoid.IsPartition C.colorClasses :=
  Setoid.isPartition_classes (Setoid.ker C)

/--
theorem `Coloring.mem_colorClasses` / 定理 `Coloring.mem_colorClasses`

English:
theorem Coloring.mem_colorClasses
  given: {v : V}
  statement: C.colorClass (C v) in C.colorClasses
  proof: ⟨v, rfl⟩

中文:
定理 染色.mem_colorClasses
  条件: {v : V}
  结论: C.colorClass (C v) in C.colorClasses
  证明: ⟨v, rfl⟩
-/
theorem Coloring.mem_colorClasses {v : V} : C.colorClass (C v) in C.colorClasses :=
  ⟨v, rfl⟩

/--
theorem `Coloring.colorClasses_finite` / 定理 `Coloring.colorClasses_finite`

English:
theorem Coloring.colorClasses_finite
  given: [Finite α]
  statement: C.colorClasses.Finite
  proof: Setoid.finite_classes_ker _

中文:
定理 染色.colorClasses_finite
  条件: [有限 α]
  结论: C.colorClasses.有限
  证明: Setoid.finite_classes_ker _

Depends on / 依赖: Setoid, Setoid.finite_classes_ker, finite_classes_ker
-/
theorem Coloring.colorClasses_finite [Finite α] : C.colorClasses.Finite :=
  Setoid.finite_classes_ker _

/--
theorem `Coloring.card_colorClasses_le` / 定理 `Coloring.card_colorClasses_le`

English:
theorem Coloring.card_colorClasses_le
  given: [Fintype α] [Fintype C.colorClasses]
  proof: by
  simp only [colorClasses]
  convert! Setoid.card_classes_ker_le C

中文:
定理 染色.card_colorClasses_le
  条件: [有限类型 α] [有限类型 C.colorClasses]
  证明: by
  simp only [colorClasses]
  convert! Setoid.card_classes_ker_le C

Depends on / 依赖: Setoid, Setoid.card_classes_ker_le, card_classes_ker_le, colorClasses, convert
-/
theorem Coloring.card_colorClasses_le [Fintype α] [Fintype C.colorClasses] :
    Fintype.card C.colorClasses <= Fintype.card α := by
  simp only [colorClasses]
  convert! Setoid.card_classes_ker_le C

/--
theorem `Coloring.not_adj_of_mem_colorClass` / 定理 `Coloring.not_adj_of_mem_colorClass`

English:
theorem Coloring.not_adj_of_mem_colorClass
  statement: {c : α} {v w : V} (hv : v in C.colorClass c)
  proof: fun h => C.valid h (Eq.trans hv (Eq.symm hw))

中文:
定理 染色.not_adj_of_mem_colorClass
  结论: {c : α} {v w : V} (hv : v in C.colorClass c)
  证明: fun h => C.valid h (Eq.trans hv (Eq.symm hw))

Depends on / 依赖: C.valid, Eq.symm, Eq.trans
-/
theorem Coloring.not_adj_of_mem_colorClass {c : α} {v w : V} (hv : v in C.colorClass c)
    (hw : w in C.colorClass c) : ¬G.Adj v w := fun h => C.valid h (Eq.trans hv (Eq.symm hw))

/--
theorem `Coloring.isIndepSet_colorClass` / 定理 `Coloring.isIndepSet_colorClass`

English:
theorem Coloring.isIndepSet_colorClass
  given: (c : α)
  statement: G.IsIndepSet C.colorClass c
  proof: fun _ hv _ hw _ => C.not_adj_of_mem_colorClass hv hw

@[deprecated isIndepSet_colorClass (since := "2026-02-07")]

中文:
定理 染色.isIndepSet_colorClass
  条件: (c : α)
  结论: G.IsIndepSet C.colorClass c
  证明: fun _ hv _ hw _ => C.not_adj_of_mem_colorClass hv hw

@[deprecated isIndepSet_colorClass (since := "2026-02-07")]

Depends on / 依赖: C.not_adj_of_mem_colorClass, not_adj_of_mem_colorClass
-/
theorem Coloring.isIndepSet_colorClass (c : α) : G.IsIndepSet C.colorClass c :=
  fun _ hv _ hw _ => C.not_adj_of_mem_colorClass hv hw

@[deprecated isIndepSet_colorClass (since := "2026-02-07")]
/--
theorem `Coloring.color_classes_independent` / 定理 `Coloring.color_classes_independent`

English:
theorem Coloring.color_classes_independent
  given: (c : α)
  statement: IsAntichain G.Adj (C.colorClass c)
  proof: C.isIndepSet_colorClass c

中文:
定理 染色.color_classes_independent
  条件: (c : α)
  结论: IsAntichain G.伴随 (C.colorClass c)
  证明: C.isIndepSet_colorClass c

Depends on / 依赖: C.isIndepSet_colorClass, isIndepSet_colorClass
-/
theorem Coloring.color_classes_independent (c : α) : IsAntichain G.Adj (C.colorClass c) :=
  C.isIndepSet_colorClass c

/--
Definition of `Coloring.comap` / `Coloring.comap` 的定义

English:
abbreviation Coloring.comap
  signature: {V' : Type*} {G' : SimpleGraph V'} {α : Type*} (C : G'.Coloring α)
  body: C.comp f

中文:
缩写 染色.comap
  签名: {V' : 类型} {G' : 简单图 V'} {α : 类型} (C : G'.染色 α)
  定义体: C.comp f

Depends on / 依赖: C.comp
-/
abbrev Coloring.comap {V' : Type*} {G' : SimpleGraph V'} {α : Type*} (C : G'.Coloring α)
    (f : G ->g G') : G.Coloring α :=
  C.comp f

-- TODO make this computable
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Fintype
  signature: V] [Fintype α] : Fintype (Coloring G α)
  body: by
  classical
  change Fintype (RelHom G.Adj (completeGraph α).Adj)
  apply Fintype.ofInjective _ RelHom.coe_fn_injective

中文:
实例 [有限类型
  签名: V] [有限类型 α] : 有限类型 (染色 G α)
  定义体: by
  classical
  change Fintype (RelHom G.Adj (completeGraph α).Adj)
  apply Fintype.ofInjective _ RelHom.coe_fn_injective

Depends on / 依赖: Fintype, Fintype.ofInjective, G.Adj, RelHom, RelHom.coe_fn_injective, classical, coe_fn_injective, completeGraph, ofInjective
-/
noncomputable instance [Fintype V] [Fintype α] : Fintype (Coloring G α) := by
  classical
  change Fintype (RelHom G.Adj (completeGraph α).Adj)
  apply Fintype.ofInjective _ RelHom.coe_fn_injective

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: α] {c
  body: inferInstanceAs DecidablePred (· in { v | C v = c })

中文:
实例 [DecidableEq
  签名: α] {c
  定义体: inferInstanceAs DecidablePred (· in { v | C v = c })

Depends on / 依赖: DecidablePred
-/
instance [DecidableEq α] {c : α} :
    DecidablePred (· in C.colorClass c) :=
inferInstanceAs DecidablePred (· in { v | C v = c })

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: <| G.Coloring α] [Nontrivial α] [Nonempty V] : Nontrivial G.Coloring α
  body: by
  classical
have ⟨C⟩ := ‹Nonempty G.Coloring α›
  have ⟨v⟩ := ‹Nonempty V›
.mp inferInstance have ⟨c, hc⟩ := nontrivial_iff_exists_ne (C v)
  refine ⟨(Iso.completeGraph <| Equiv.swap (C v) c).toHom.comp C, C, fun h => hc ?_⟩
  have := congrFun (congrArg RelHom.toFun h) v
  dsimp [Iso.completeGraph] at this
  grind

中文:
实例 [非空
  签名: <| G.染色 α] [非平凡 α] [非空 V] : 非平凡 G.染色 α
  定义体: by
  classical
have ⟨C⟩ := ‹Nonempty G.Coloring α›
  have ⟨v⟩ := ‹Nonempty V›
.mp inferInstance have ⟨c, hc⟩ := nontrivial_iff_exists_ne (C v)
  refine ⟨(Iso.completeGraph <| Equiv.swap (C v) c).toHom.comp C, C, fun h => hc ?_⟩
  have := congrFun (congrArg RelHom.toFun h) v
  dsimp [Iso.completeGraph] at this
  grind

Depends on / 依赖: Coloring, Equiv.swap, G.Coloring, Iso.completeGraph, Nonempty, RelHom, RelHom.toFun, classical, completeGraph, nontrivial_iff_exists_ne, toHom.comp
-/
instance [Nonempty <| G.Coloring α] [Nontrivial α] [Nonempty V] : Nontrivial G.Coloring α := by
  classical
have ⟨C⟩ := ‹Nonempty G.Coloring α›
  have ⟨v⟩ := ‹Nonempty V›
.mp inferInstance have ⟨c, hc⟩ := nontrivial_iff_exists_ne (C v)
  refine ⟨(Iso.completeGraph <| Equiv.swap (C v) c).toHom.comp C, C, fun h => hc ?_⟩
  have := congrFun (congrArg RelHom.toFun h) v
  dsimp [Iso.completeGraph] at this
  grind

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: <| G.Coloring α] [Infinite α] [Nonempty V] : Infinite G.Coloring α
  body: by
  classical
have ⟨C⟩ := ‹Nonempty G.Coloring α›
  have ⟨v⟩ := ‹Nonempty V›
  let f c := (Iso.completeGraph <| Equiv.swap (C v) c).toHom.comp C
  refine Infinite.of_injective f fun a b h => ?_
  have := congrFun (congrArg RelHom.toFun h) v
  dsimp [f, Iso.completeGraph] at this
  grind

中文:
实例 [非空
  签名: <| G.染色 α] [无限 α] [非空 V] : 无限 G.染色 α
  定义体: by
  classical
have ⟨C⟩ := ‹Nonempty G.Coloring α›
  have ⟨v⟩ := ‹Nonempty V›
  let f c := (Iso.completeGraph <| Equiv.swap (C v) c).toHom.comp C
  refine Infinite.of_injective f fun a b h => ?_
  have := congrFun (congrArg RelHom.toFun h) v
  dsimp [f, Iso.completeGraph] at this
  grind

Depends on / 依赖: Coloring, Equiv.swap, G.Coloring, Infinite, Infinite.of_injective, Iso.completeGraph, Nonempty, RelHom, RelHom.toFun, classical, completeGraph, of_injective, toHom.comp
-/
instance [Nonempty <| G.Coloring α] [Infinite α] [Nonempty V] : Infinite G.Coloring α := by
  classical
have ⟨C⟩ := ‹Nonempty G.Coloring α›
  have ⟨v⟩ := ‹Nonempty V›
  let f c := (Iso.completeGraph <| Equiv.swap (C v) c).toHom.comp C
  refine Infinite.of_injective f fun a b h => ?_
  have := congrFun (congrArg RelHom.toFun h) v
  dsimp [f, Iso.completeGraph] at this
  grind

variable (G) in
/--
Definition of `Colorable` / `Colorable` 的定义

English:
definition Colorable
  signature: (n : Nat)
  body: Nonempty (G.Coloring (Fin n))

中文:
定义 Colorable
  签名: (n : 自然数)
  定义体: Nonempty (G.Coloring (Fin n))

Depends on / 依赖: Coloring, G.Coloring, Nonempty
-/
def Colorable (n : Nat) : Prop := Nonempty (G.Coloring (Fin n))

/--
Definition of `Coloring.ofIsEmpty` / `Coloring.ofIsEmpty` 的定义

English:
definition Coloring.ofIsEmpty
  signature: [IsEmpty V]
  body: .mk isEmptyElim fun {v} => isEmptyElim v

中文:
定义 染色.ofIsEmpty
  签名: [是空 V]
  定义体: .mk isEmptyElim fun {v} => isEmptyElim v

Depends on / 依赖: isEmptyElim
-/
def Coloring.ofIsEmpty [IsEmpty V] : G.Coloring α := .mk isEmptyElim fun {v} => isEmptyElim v

/--
theorem `Colorable.of_isEmpty` / 定理 `Colorable.of_isEmpty`

English:
theorem Colorable.of_isEmpty
  given: [IsEmpty V] (n : Nat)
  statement: G.Colorable n
  proof: ⟨.ofIsEmpty⟩

@[deprecated (since := "2026-01-03")] alias coloringOfIsEmpty := Coloring.ofIsEmpty
@[deprecated (since := "2026-01-03")] alias colorableOfIsEmpty := Colorable.of_isEmpty

@[simp]

中文:
定理 Colorable.of_isEmpty
  条件: [是空 V] (n : 自然数)
  结论: G.Colorable n
  证明: ⟨.ofIsEmpty⟩

@[deprecated (since := "2026-01-03")] alias coloringOfIsEmpty := Coloring.ofIsEmpty
@[deprecated (since := "2026-01-03")] alias colorableOfIsEmpty := Colorable.of_isEmpty

@[simp]

Depends on / 依赖: ofIsEmpty
-/
theorem Colorable.of_isEmpty [IsEmpty V] (n : Nat) : G.Colorable n := ⟨.ofIsEmpty⟩

@[deprecated (since := "2026-01-03")] alias coloringOfIsEmpty := Coloring.ofIsEmpty
@[deprecated (since := "2026-01-03")] alias colorableOfIsEmpty := Colorable.of_isEmpty

@[simp]
/--
lemma `colorable_zero_iff` / 引理 `colorable_zero_iff`

English:
lemma colorable_zero_iff
  statement: G.Colorable 0 ↔ IsEmpty V
  proof: ⟨fun ⟨C⟩ => Function.isEmpty C, fun _ => .of_isEmpty 0⟩

alias ⟨Colorable.isEmpty, _⟩ := colorable_zero_iff

@[deprecated (since := "2026-04-24")] alias isEmpty_of_colorable_zero := Colorable.isEmpty

@[simp]

中文:
引理 colorable_zero_iff
  结论: G.Colorable 0 ↔ 是空 V
  证明: ⟨fun ⟨C⟩ => Function.isEmpty C, fun _ => .of_isEmpty 0⟩

alias ⟨Colorable.isEmpty, _⟩ := colorable_zero_iff

@[deprecated (since := "2026-04-24")] alias isEmpty_of_colorable_zero := Colorable.isEmpty

@[simp]

Depends on / 依赖: Function, Function.isEmpty, isEmpty, of_isEmpty
-/
lemma colorable_zero_iff : G.Colorable 0 ↔ IsEmpty V :=
  ⟨fun ⟨C⟩ => Function.isEmpty C, fun _ => .of_isEmpty 0⟩

alias ⟨Colorable.isEmpty, _⟩ := colorable_zero_iff

@[deprecated (since := "2026-04-24")] alias isEmpty_of_colorable_zero := Colorable.isEmpty

@[simp]
/--
theorem `colorable_one_iff` / 定理 `colorable_one_iff`

English:
theorem colorable_one_iff
  statement: G.Colorable 1 ↔ G = ⊥
  proof: by
  refine ⟨fun ⟨C⟩ => eq_bot_iff_forall_not_adj.mpr fun u v h => ?_, fun h => h ▸ ⟨0, by simp⟩⟩
exact C.map_rel h Subsingleton.elim ..

中文:
定理 colorable_one_iff
  结论: G.Colorable 1 ↔ G = ⊥
  证明: by
  refine ⟨fun ⟨C⟩ => eq_bot_iff_forall_not_adj.mpr fun u v h => ?_, fun h => h ▸ ⟨0, by simp⟩⟩
exact C.map_rel h Subsingleton.elim ..

Depends on / 依赖: C.map_rel, Subsingleton, Subsingleton.elim, eq_bot_iff_forall_not_adj, eq_bot_iff_forall_not_adj.mpr, map_rel
-/
theorem colorable_one_iff : G.Colorable 1 ↔ G = ⊥ := by
  refine ⟨fun ⟨C⟩ => eq_bot_iff_forall_not_adj.mpr fun u v h => ?_, fun h => h ▸ ⟨0, by simp⟩⟩
exact C.map_rel h Subsingleton.elim ..

/--
Definition of `Coloring.homMap` / `Coloring.homMap` 的定义

English:
abbreviation Coloring.homMap
  signature: {α : Type*} (f : G.Coloring α)
  body: .map f G f.map_adj

中文:
缩写 染色.homMap
  签名: {α : 类型} (f : G.染色 α)
  定义体: .map f G f.map_adj

Depends on / 依赖: f.map_adj, map_adj
-/
abbrev Coloring.homMap {α : Type*} (f : G.Coloring α) : G ->g G.map f :=
  .map f G f.map_adj

/--
theorem `Colorable.map` / 定理 `Colorable.map`

English:
theorem Colorable.map
  given: (f : V ↪ β) [NeZero n] (hc : G.Colorable n)
  statement: (G.map f).Colorable n
  proof: by
  obtain ⟨C⟩ := hc
  use extend f C (const β default)
  intro a b ⟨_, _, _, hadj, ha, hb⟩
  rw [← ha]; rw [f.injective.extend_apply]; rw [← hb]; rw [f.injective.extend_apply]
  exact C.valid hadj

中文:
定理 Colorable.map
  条件: (f : V ↪ β) [NeZero n] (hc : G.Colorable n)
  结论: (G.map f).Colorable n
  证明: by
  obtain ⟨C⟩ := hc
  use extend f C (const β default)
  intro a b ⟨_, _, _, hadj, ha, hb⟩
  rw [← ha]; rw [f.injective.extend_apply]; rw [← hb]; rw [f.injective.extend_apply]
  exact C.valid hadj

Depends on / 依赖: C.valid, extend, extend_apply, f.injective.extend_apply, injective
-/
theorem Colorable.map (f : V ↪ β) [NeZero n] (hc : G.Colorable n) : (G.map f).Colorable n := by
  obtain ⟨C⟩ := hc
  use extend f C (const β default)
  intro a b ⟨_, _, _, hadj, ha, hb⟩
  rw [← ha]; rw [f.injective.extend_apply]; rw [← hb]; rw [f.injective.extend_apply]
  exact C.valid hadj

/--
lemma `Colorable.card_le_of_pairwise_adj` / 引理 `Colorable.card_le_of_pairwise_adj`

English:
lemma Colorable.card_le_of_pairwise_adj
  statement: (hG : G.Colorable n) (f : ι -> V)
  proof: by
  obtain ⟨C⟩ := hG
  simpa using Nat.card_le_card_of_injective _ (C.injective_comp_of_pairwise_adj f hf)

中文:
引理 Colorable.card_le_of_pairwise_adj
  结论: (hG : G.Colorable n) (f : ι -> V)
  证明: by
  obtain ⟨C⟩ := hG
  simpa using Nat.card_le_card_of_injective _ (C.injective_comp_of_pairwise_adj f hf)

Depends on / 依赖: C.injective_comp_of_pairwise_adj, Nat.card_le_card_of_injective, card_le_card_of_injective, injective_comp_of_pairwise_adj
-/
lemma Colorable.card_le_of_pairwise_adj (hG : G.Colorable n) (f : ι -> V)
    (hf : Pairwise fun i j => G.Adj (f i) (f j)) : Nat.card ι <= n := by
  obtain ⟨C⟩ := hG
  simpa using Nat.card_le_card_of_injective _ (C.injective_comp_of_pairwise_adj f hf)

variable (G) in
/--
Definition of `selfColoring` / `selfColoring` 的定义

English:
definition selfColoring
  signature: : G.Coloring V
  body: Coloring.mk id fun {_ _} => G.ne_of_adj

中文:
定义 selfColoring
  签名: : G.染色 V
  定义体: Coloring.mk id fun {_ _} => G.ne_of_adj

Depends on / 依赖: Coloring, Coloring.mk, G.ne_of_adj, ne_of_adj
-/
def selfColoring : G.Coloring V := Coloring.mk id fun {_ _} => G.ne_of_adj

variable (G) in
/--
Definition of `chromaticNumber` / `chromaticNumber` 的定义

English:
definition chromaticNumber
  signature: : Nat∞
  body: ⨅ n in Set.ofPred G.Colorable, (n : Nat∞)

中文:
定义 chromaticNumber
  签名: : 自然数∞
  定义体: ⨅ n in Set.ofPred G.Colorable, (n : Nat∞)

Depends on / 依赖: Colorable, G.Colorable, Set.ofPred, ofPred
-/
noncomputable def chromaticNumber : Nat∞ := ⨅ n in Set.ofPred G.Colorable, (n : Nat∞)

/--
lemma `le_chromaticNumber_iff_colorable` / 引理 `le_chromaticNumber_iff_colorable`

English:
lemma le_chromaticNumber_iff_colorable
  statement: n <= G.chromaticNumber ↔ forall m, G.Colorable m -> n <= m
  proof: by
  simp [chromaticNumber]

中文:
引理 le_chromaticNumber_iff_colorable
  结论: n <= G.chromaticNumber ↔ 对任意 m, G.Colorable m -> n <= m
  证明: by
  simp [chromaticNumber]

Depends on / 依赖: chromaticNumber
-/
lemma le_chromaticNumber_iff_colorable : n <= G.chromaticNumber ↔ forall m, G.Colorable m -> n <= m := by
  simp [chromaticNumber]

/--
lemma `le_chromaticNumber_iff_coloring` / 引理 `le_chromaticNumber_iff_coloring`

English:
lemma le_chromaticNumber_iff_coloring
  proof: by
  simp [le_chromaticNumber_iff_colorable, Colorable]

中文:
引理 le_chromaticNumber_iff_coloring
  证明: by
  simp [le_chromaticNumber_iff_colorable, Colorable]

Depends on / 依赖: Colorable, le_chromaticNumber_iff_colorable
-/
lemma le_chromaticNumber_iff_coloring :
    n <= G.chromaticNumber ↔ forall m, G.Coloring (Fin m) -> n <= m := by
  simp [le_chromaticNumber_iff_colorable, Colorable]

/--
lemma `le_chromaticNumber_of_pairwise_adj` / 引理 `le_chromaticNumber_of_pairwise_adj`

English:
lemma le_chromaticNumber_of_pairwise_adj
  statement: (hn : n <= Nat.card ι) (f : ι -> V)
  proof: le_chromaticNumber_iff_colorable.2 fun _m hm => hn.trans hm.card_le_of_pairwise_adj f hf

中文:
引理 le_chromaticNumber_of_pairwise_adj
  结论: (hn : n <= 自然数.card ι) (f : ι -> V)
  证明: le_chromaticNumber_iff_colorable.2 fun _m hm => hn.trans hm.card_le_of_pairwise_adj f hf

Depends on / 依赖: card_le_of_pairwise_adj, hm.card_le_of_pairwise_adj, hn.trans, le_chromaticNumber_iff_colorable
-/
lemma le_chromaticNumber_of_pairwise_adj (hn : n <= Nat.card ι) (f : ι -> V)
    (hf : Pairwise fun i j => G.Adj (f i) (f j)) : n <= G.chromaticNumber :=
le_chromaticNumber_iff_colorable.2 fun _m hm => hn.trans hm.card_le_of_pairwise_adj f hf

variable (G) in
/--
lemma `chromaticNumber_eq_biInf` / 引理 `chromaticNumber_eq_biInf`

English:
lemma chromaticNumber_eq_biInf
  statement: G.chromaticNumber = ⨅ n in Set.ofPred G.Colorable, (n : Nat∞)
  proof: rfl

中文:
引理 chromaticNumber_eq_biInf
  结论: G.chromaticNumber = ⨅ n in 集合.ofPred G.Colorable, (n : 自然数∞)
  证明: rfl
-/
lemma chromaticNumber_eq_biInf : G.chromaticNumber = ⨅ n in Set.ofPred G.Colorable, (n : Nat∞) := rfl

variable (G) in
/--
lemma `chromaticNumber_eq_iInf` / 引理 `chromaticNumber_eq_iInf`

English:
lemma chromaticNumber_eq_iInf
  statement: G.chromaticNumber = ⨅ n : {m | G.Colorable m}, (n : Nat∞)
  proof: by
  rw [chromaticNumber]; rw [iInf_subtype]

中文:
引理 chromaticNumber_eq_iInf
  结论: G.chromaticNumber = ⨅ n : {m | G.Colorable m}, (n : 自然数∞)
  证明: by
  rw [chromaticNumber]; rw [iInf_subtype]

Depends on / 依赖: chromaticNumber, iInf_subtype
-/
lemma chromaticNumber_eq_iInf : G.chromaticNumber = ⨅ n : {m | G.Colorable m}, (n : Nat∞) := by
  rw [chromaticNumber]; rw [iInf_subtype]

/--
lemma `Colorable.chromaticNumber_eq_sInf` / 引理 `Colorable.chromaticNumber_eq_sInf`

English:
lemma Colorable.chromaticNumber_eq_sInf
  given: (h : G.Colorable n)
  proof: by
  rw [ENat.natCast_sInf]; rw [chromaticNumber]
  exact ⟨_, h⟩

中文:
引理 Colorable.chromaticNumber_eq_sInf
  条件: (h : G.Colorable n)
  证明: by
  rw [ENat.natCast_sInf]; rw [chromaticNumber]
  exact ⟨_, h⟩

Depends on / 依赖: ENat.natCast_sInf, chromaticNumber, natCast_sInf
-/
lemma Colorable.chromaticNumber_eq_sInf (h : G.Colorable n) :
    G.chromaticNumber = sInf {n' : Nat | G.Colorable n'} := by
  rw [ENat.natCast_sInf]; rw [chromaticNumber]
  exact ⟨_, h⟩

variable (G) in
/--
Definition of `recolorOfEmbedding` / `recolorOfEmbedding` 的定义

English:
definition recolorOfEmbedding
  signature: {α β : Type*} (f : α ↪ β)
  body: (Embedding.completeGraph f).toHom.comp C
.mpr f.injective.comp_left RelHom.mk.inj h inj' C C' h := RelHom.mk.injEq C _ C' _

中文:
定义 recolorOfEmbedding
  签名: {α β : 类型} (f : α ↪ β)
  定义体: (Embedding.completeGraph f).toHom.comp C
.mpr f.injective.comp_left RelHom.mk.inj h inj' C C' h := RelHom.mk.injEq C _ C' _

Depends on / 依赖: Embedding, Embedding.completeGraph, completeGraph, toHom.comp
-/
def recolorOfEmbedding {α β : Type*} (f : α ↪ β) : G.Coloring α ↪ G.Coloring β where
  toFun C := (Embedding.completeGraph f).toHom.comp C
.mpr f.injective.comp_left RelHom.mk.inj h inj' C C' h := RelHom.mk.injEq C _ C' _

variable (G) in
/--
lemma `coe_recolorOfEmbedding` / 引理 `coe_recolorOfEmbedding`

English:
lemma coe_recolorOfEmbedding
  given: (f : α ↪ β)
  proof: rfl

中文:
引理 coe_recolorOfEmbedding
  条件: (f : α ↪ β)
  证明: rfl
-/
@[simp] lemma coe_recolorOfEmbedding (f : α ↪ β) :
    ⇑(G.recolorOfEmbedding f) = (Embedding.completeGraph f).toHom.comp := rfl

variable (G) in
/--
Definition of `recolorOfEquiv` / `recolorOfEquiv` 的定义

English:
definition recolorOfEquiv
  signature: {α β : Type*} (f : α ≃ β)
  body: G.recolorOfEmbedding f.toEmbedding
  invFun := G.recolorOfEmbedding f.symm.toEmbedding
  left_inv C := by
    ext v
    apply Equiv.symm_apply_apply
  right_inv C := by
    ext v
    apply Equiv.apply_symm_apply

中文:
定义 recolorOfEquiv
  签名: {α β : 类型} (f : α ≃ β)
  定义体: G.recolorOfEmbedding f.toEmbedding
  invFun := G.recolorOfEmbedding f.symm.toEmbedding
  left_inv C := by
    ext v
    apply Equiv.symm_apply_apply
  right_inv C := by
    ext v
    apply Equiv.apply_symm_apply

Depends on / 依赖: G.recolorOfEmbedding, f.toEmbedding, recolorOfEmbedding, toEmbedding
-/
def recolorOfEquiv {α β : Type*} (f : α ≃ β) : G.Coloring α ≃ G.Coloring β where
  toFun := G.recolorOfEmbedding f.toEmbedding
  invFun := G.recolorOfEmbedding f.symm.toEmbedding
  left_inv C := by
    ext v
    apply Equiv.symm_apply_apply
  right_inv C := by
    ext v
    apply Equiv.apply_symm_apply

variable (G) in
/--
lemma `coe_recolorOfEquiv` / 引理 `coe_recolorOfEquiv`

English:
lemma coe_recolorOfEquiv
  given: (f : α ≃ β)
  proof: rfl

中文:
引理 coe_recolorOfEquiv
  条件: (f : α ≃ β)
  证明: rfl
-/
@[simp] lemma coe_recolorOfEquiv (f : α ≃ β) :
    ⇑(G.recolorOfEquiv f) = (Embedding.completeGraph f).toHom.comp := rfl

variable (G) in
/--
Definition of `recolorOfCardLE` / `recolorOfCardLE` 的定义

English:
definition recolorOfCardLE
  signature: {α β : Type*} [Fintype α] [Fintype β]
  body: G.recolorOfEmbedding (Function.Embedding.nonempty_of_card_le hn).some

中文:
定义 recolorOfCardLE
  签名: {α β : 类型} [有限类型 α] [有限类型 β]
  定义体: G.recolorOfEmbedding (Function.Embedding.nonempty_of_card_le hn).some

Depends on / 依赖: Embedding, Function, Function.Embedding.nonempty_of_card_le, G.recolorOfEmbedding, nonempty_of_card_le, recolorOfEmbedding
-/
noncomputable def recolorOfCardLE {α β : Type*} [Fintype α] [Fintype β]
    (hn : Fintype.card α <= Fintype.card β) : G.Coloring α ↪ G.Coloring β :=
G.recolorOfEmbedding (Function.Embedding.nonempty_of_card_le hn).some

variable (G) in
/--
lemma `coe_recolorOfCardLE` / 引理 `coe_recolorOfCardLE`

English:
lemma coe_recolorOfCardLE
  given: [Fintype α] [Fintype β] (hαβ : card α <= card β)
  proof: rfl

中文:
引理 coe_recolorOfCardLE
  条件: [有限类型 α] [有限类型 β] (hαβ : card α <= card β)
  证明: rfl
-/
@[simp] lemma coe_recolorOfCardLE [Fintype α] [Fintype β] (hαβ : card α <= card β) :
    ⇑(G.recolorOfCardLE hαβ) =
      (Embedding.completeGraph (Embedding.nonempty_of_card_le hαβ).some).toHom.comp := rfl

/--
theorem `Colorable.mono` / 定理 `Colorable.mono`

English:
theorem Colorable.mono
  given: {n m : Nat} (h : n <= m) (hc : G.Colorable n)
  statement: G.Colorable m
  proof: ⟨G.recolorOfCardLE (by simp [h]) hc.some⟩

中文:
定理 Colorable.mono
  条件: {n m : 自然数} (h : n <= m) (hc : G.Colorable n)
  结论: G.Colorable m
  证明: ⟨G.recolorOfCardLE (by simp [h]) hc.some⟩

Depends on / 依赖: G.recolorOfCardLE, hc.some, recolorOfCardLE
-/
theorem Colorable.mono {n m : Nat} (h : n <= m) (hc : G.Colorable n) : G.Colorable m :=
  ⟨G.recolorOfCardLE (by simp [h]) hc.some⟩

/--
theorem `Coloring.colorable` / 定理 `Coloring.colorable`

English:
theorem Coloring.colorable
  given: [Fintype α] (C : G.Coloring α)
  statement: G.Colorable (Fintype.card α)
  proof: ⟨G.recolorOfCardLE (by simp) C⟩

中文:
定理 染色.colorable
  条件: [有限类型 α] (C : G.染色 α)
  结论: G.Colorable (有限类型.card α)
  证明: ⟨G.recolorOfCardLE (by simp) C⟩

Depends on / 依赖: G.recolorOfCardLE, recolorOfCardLE
-/
theorem Coloring.colorable [Fintype α] (C : G.Coloring α) : G.Colorable (Fintype.card α) :=
  ⟨G.recolorOfCardLE (by simp) C⟩

/--
theorem `colorable_of_fintype` / 定理 `colorable_of_fintype`

English:
theorem colorable_of_fintype
  given: (G : SimpleGraph V) [Fintype V]
  statement: G.Colorable (Fintype.card V)
  proof: G.selfColoring.colorable

中文:
定理 colorable_of_fintype
  条件: (G : 简单图 V) [有限类型 V]
  结论: G.Colorable (有限类型.card V)
  证明: G.selfColoring.colorable

Depends on / 依赖: G.selfColoring.colorable, colorable, selfColoring
-/
theorem colorable_of_fintype (G : SimpleGraph V) [Fintype V] : G.Colorable (Fintype.card V) :=
  G.selfColoring.colorable

/--
Definition of `Colorable.toColoring` / `Colorable.toColoring` 的定义

English:
definition Colorable.toColoring
  signature: [Fintype α] {n : Nat} (hc : G.Colorable n)
  body: by
  rw [← Fintype.card_fin n] at hn
  exact G.recolorOfCardLE hn hc.some

中文:
定义 Colorable.toColoring
  签名: [有限类型 α] {n : 自然数} (hc : G.Colorable n)
  定义体: by
  rw [← Fintype.card_fin n] at hn
  exact G.recolorOfCardLE hn hc.some

Depends on / 依赖: Fintype, Fintype.card_fin, G.recolorOfCardLE, card_fin, hc.some, recolorOfCardLE
-/
noncomputable def Colorable.toColoring [Fintype α] {n : Nat} (hc : G.Colorable n)
    (hn : n <= Fintype.card α) : G.Coloring α := by
  rw [← Fintype.card_fin n] at hn
  exact G.recolorOfCardLE hn hc.some

/--
theorem `Colorable.of_hom` / 定理 `Colorable.of_hom`

English:
theorem Colorable.of_hom
  statement: {V' : Type*} {G' : SimpleGraph V'} {n : Nat} (f : G ->g G')
  proof: ⟨h.some.comap f⟩

中文:
定理 Colorable.of_hom
  结论: {V' : 类型} {G' : 简单图 V'} {n : 自然数} (f : G ->g G')
  证明: ⟨h.some.comap f⟩

Depends on / 依赖: h.some.comap
-/
theorem Colorable.of_hom {V' : Type*} {G' : SimpleGraph V'} {n : Nat} (f : G ->g G')
    (h : G'.Colorable n) : G.Colorable n :=
  ⟨h.some.comap f⟩

/--
theorem `colorable_iff_exists_bdd_nat_coloring` / 定理 `colorable_iff_exists_bdd_nat_coloring`

English:
theorem colorable_iff_exists_bdd_nat_coloring
  given: (n : Nat)
  proof: by
  constructor
  · rintro hc
    have C : G.Coloring (Fin n) := hc.toColoring (by simp)
    let f := Embedding.completeGraph (@Fin.valEmbedding n)
    use f.toHom.comp C
    intro v
    exact Fin.is_lt (C.1 v)
  · rintro ⟨C, Cf⟩
    refine ⟨Coloring.mk ?_ ?_⟩
    · exact fun v => ⟨C v, Cf v⟩
    · rintro v w hvw
      simp only [Fin.mk_eq_mk, Ne]
      exact C.valid hvw

中文:
定理 colorable_iff_存在_bdd_nat_coloring
  条件: (n : 自然数)
  证明: by
  constructor
  · rintro hc
    have C : G.Coloring (Fin n) := hc.toColoring (by simp)
    let f := Embedding.completeGraph (@Fin.valEmbedding n)
    use f.toHom.comp C
    intro v
    exact Fin.is_lt (C.1 v)
  · rintro ⟨C, Cf⟩
    refine ⟨Coloring.mk ?_ ?_⟩
    · exact fun v => ⟨C v, Cf v⟩
    · rintro v w hvw
      simp only [Fin.mk_eq_mk, Ne]
      exact C.valid hvw

Depends on / 依赖: C.valid, Coloring, Coloring.mk, Embedding, Embedding.completeGraph, Fin.is_lt, Fin.mk_eq_mk, Fin.valEmbedding, G.Coloring, completeGraph, f.toHom.comp, hc.toColoring, is_lt, mk_eq_mk, toColoring, valEmbedding
-/
theorem colorable_iff_exists_bdd_nat_coloring (n : Nat) :
    G.Colorable n ↔ exists C : G.Coloring Nat, forall v, C v < n := by
  constructor
  · rintro hc
    have C : G.Coloring (Fin n) := hc.toColoring (by simp)
    let f := Embedding.completeGraph (@Fin.valEmbedding n)
    use f.toHom.comp C
    intro v
    exact Fin.is_lt (C.1 v)
  · rintro ⟨C, Cf⟩
    refine ⟨Coloring.mk ?_ ?_⟩
    · exact fun v => ⟨C v, Cf v⟩
    · rintro v w hvw
      simp only [Fin.mk_eq_mk, Ne]
      exact C.valid hvw

/--
theorem `colorable_iff_forall_connectedComponent` / 定理 `colorable_iff_forall_connectedComponent`

English:
theorem colorable_iff_forall_connectedComponent
  given: {n : Nat}
  proof: ⟨fun ⟨C⟩ _ => ⟨fun v => C v, fun h h1 => C.valid h h1⟩,
   fun h => ⟨G.homOfConnectedComponents (fun c => (h c).some)⟩⟩

@[deprecated (since := "2026-07-12")]
alias colorable_iff_forall_connectedComponents := colorable_iff_forall_connectedComponent

中文:
定理 colorable_iff_对任意_connectedComponent
  条件: {n : 自然数}
  证明: ⟨fun ⟨C⟩ _ => ⟨fun v => C v, fun h h1 => C.valid h h1⟩,
   fun h => ⟨G.homOfConnectedComponents (fun c => (h c).some)⟩⟩

@[deprecated (since := "2026-07-12")]
alias colorable_iff_forall_connectedComponents := colorable_iff_forall_connectedComponent

Depends on / 依赖: C.valid, G.homOfConnectedComponents, homOfConnectedComponents
-/
theorem colorable_iff_forall_connectedComponent {n : Nat} :
    G.Colorable n ↔ forall c : G.ConnectedComponent, (c.toSimpleGraph).Colorable n :=
  ⟨fun ⟨C⟩ _ => ⟨fun v => C v, fun h h1 => C.valid h h1⟩,
   fun h => ⟨G.homOfConnectedComponents (fun c => (h c).some)⟩⟩

@[deprecated (since := "2026-07-12")]
alias colorable_iff_forall_connectedComponents := colorable_iff_forall_connectedComponent

/--
theorem `colorable_set_nonempty_of_colorable` / 定理 `colorable_set_nonempty_of_colorable`

English:
theorem colorable_set_nonempty_of_colorable
  given: {n : Nat} (hc : G.Colorable n)
  proof: ⟨n, hc⟩

中文:
定理 colorable_set_nonempty_of_colorable
  条件: {n : 自然数} (hc : G.Colorable n)
  证明: ⟨n, hc⟩
-/
theorem colorable_set_nonempty_of_colorable {n : Nat} (hc : G.Colorable n) :
    { n : Nat | G.Colorable n }.Nonempty :=
  ⟨n, hc⟩

/--
theorem `chromaticNumber_bddBelow` / 定理 `chromaticNumber_bddBelow`

English:
theorem chromaticNumber_bddBelow
  statement: BddBelow { n : Nat | G.Colorable n }
  proof: ⟨0, fun _ _ => zero_le⟩

中文:
定理 chromaticNumber_bddBelow
  结论: BddBelow { n : 自然数 | G.Colorable n }
  证明: ⟨0, fun _ _ => zero_le⟩

Depends on / 依赖: zero_le
-/
theorem chromaticNumber_bddBelow : BddBelow { n : Nat | G.Colorable n } :=
  ⟨0, fun _ _ => zero_le⟩

/--
theorem `Colorable.chromaticNumber_le` / 定理 `Colorable.chromaticNumber_le`

English:
theorem Colorable.chromaticNumber_le
  given: {n : Nat} (hc : G.Colorable n)
  statement: G.chromaticNumber <= n
  proof: by
  rw [hc.chromaticNumber_eq_sInf]
  norm_cast
  apply csInf_le chromaticNumber_bddBelow
  exact hc

中文:
定理 Colorable.chromaticNumber_le
  条件: {n : 自然数} (hc : G.Colorable n)
  结论: G.chromaticNumber <= n
  证明: by
  rw [hc.chromaticNumber_eq_sInf]
  norm_cast
  apply csInf_le chromaticNumber_bddBelow
  exact hc

Depends on / 依赖: chromaticNumber_bddBelow, chromaticNumber_eq_sInf, csInf_le, hc.chromaticNumber_eq_sInf
-/
theorem Colorable.chromaticNumber_le {n : Nat} (hc : G.Colorable n) : G.chromaticNumber <= n := by
  rw [hc.chromaticNumber_eq_sInf]
  norm_cast
  apply csInf_le chromaticNumber_bddBelow
  exact hc

/--
theorem `chromaticNumber_ne_top_iff_exists` / 定理 `chromaticNumber_ne_top_iff_exists`

English:
theorem chromaticNumber_ne_top_iff_exists
  statement: G.chromaticNumber != ⊤ ↔ exists n, G.Colorable n
  proof: by
  rw [chromaticNumber]
  simp

中文:
定理 chromaticNumber_ne_top_iff_存在
  结论: G.chromaticNumber != ⊤ ↔ 存在 n, G.Colorable n
  证明: by
  rw [chromaticNumber]
  simp

Depends on / 依赖: chromaticNumber
-/
theorem chromaticNumber_ne_top_iff_exists : G.chromaticNumber != ⊤ ↔ exists n, G.Colorable n := by
  rw [chromaticNumber]
  simp

/--
theorem `chromaticNumber_le_iff_colorable` / 定理 `chromaticNumber_le_iff_colorable`

English:
theorem chromaticNumber_le_iff_colorable
  given: {n : Nat}
  statement: G.chromaticNumber <= n ↔ G.Colorable n
  proof: by
  refine ⟨fun h => ?_, Colorable.chromaticNumber_le⟩
  have : G.chromaticNumber != ⊤ := (trans h (ENat.natCast_lt_top n)).ne
  rw [chromaticNumber_ne_top_iff_exists] at this
  obtain ⟨m, hm⟩ := this
  rw [hm.chromaticNumber_eq_sInf]; rw [Nat.cast_le] at h
  have := Nat.sInf_mem (⟨m, hm⟩ : {n' | G.Colorable n'}.Nonempty)
  rw [Set.mem_ofPred_eq] at this
  exact this.mono h

中文:
定理 chromaticNumber_le_iff_colorable
  条件: {n : 自然数}
  结论: G.chromaticNumber <= n ↔ G.Colorable n
  证明: by
  refine ⟨fun h => ?_, Colorable.chromaticNumber_le⟩
  have : G.chromaticNumber != ⊤ := (trans h (ENat.natCast_lt_top n)).ne
  rw [chromaticNumber_ne_top_iff_exists] at this
  obtain ⟨m, hm⟩ := this
  rw [hm.chromaticNumber_eq_sInf]; rw [Nat.cast_le] at h
  have := Nat.sInf_mem (⟨m, hm⟩ : {n' | G.Colorable n'}.Nonempty)
  rw [Set.mem_ofPred_eq] at this
  exact this.mono h

Depends on / 依赖: Colorable, Colorable.chromaticNumber_le, ENat.natCast_lt_top, G.Colorable, G.chromaticNumber, Nat.cast_le, Nat.sInf_mem, Nonempty, Set.mem_ofPred_eq, cast_le, chromaticNumber, chromaticNumber_eq_sInf, chromaticNumber_le, chromaticNumber_ne_top_iff_exists, hm.chromaticNumber_eq_sInf, mem_ofPred_eq, natCast_lt_top, sInf_mem, this.mono
-/
theorem chromaticNumber_le_iff_colorable {n : Nat} : G.chromaticNumber <= n ↔ G.Colorable n := by
  refine ⟨fun h => ?_, Colorable.chromaticNumber_le⟩
  have : G.chromaticNumber != ⊤ := (trans h (ENat.natCast_lt_top n)).ne
  rw [chromaticNumber_ne_top_iff_exists] at this
  obtain ⟨m, hm⟩ := this
  rw [hm.chromaticNumber_eq_sInf]; rw [Nat.cast_le] at h
  have := Nat.sInf_mem (⟨m, hm⟩ : {n' | G.Colorable n'}.Nonempty)
  rw [Set.mem_ofPred_eq] at this
  exact this.mono h

/--
theorem `chromaticNumber_eq_iff_colorable_not_colorable` / 定理 `chromaticNumber_eq_iff_colorable_not_colorable`

English:
theorem chromaticNumber_eq_iff_colorable_not_colorable
  proof: by
  rw [eq_iff_le_not_lt]; rw [not_lt]; rw [ENat.add_one_le_iff (ENat.natCast_ne_top n)]; rw [← not_le]; rw [chromaticNumber_le_iff_colorable]; rw [← Nat.cast_add_one]; rw [chromaticNumber_le_iff_colorable]

中文:
定理 chromaticNumber_eq_iff_colorable_not_colorable
  证明: by
  rw [eq_iff_le_not_lt]; rw [not_lt]; rw [ENat.add_one_le_iff (ENat.natCast_ne_top n)]; rw [← not_le]; rw [chromaticNumber_le_iff_colorable]; rw [← Nat.cast_add_one]; rw [chromaticNumber_le_iff_colorable]

Depends on / 依赖: ENat.add_one_le_iff, ENat.natCast_ne_top, Nat.cast_add_one, add_one_le_iff, cast_add_one, chromaticNumber_le_iff_colorable, eq_iff_le_not_lt, natCast_ne_top, not_le, not_lt
-/
theorem chromaticNumber_eq_iff_colorable_not_colorable :
    G.chromaticNumber = n + 1 ↔ G.Colorable (n + 1) ∧ ¬G.Colorable n := by
  rw [eq_iff_le_not_lt]; rw [not_lt]; rw [ENat.add_one_le_iff (ENat.natCast_ne_top n)]; rw [← not_le]; rw [chromaticNumber_le_iff_colorable]; rw [← Nat.cast_add_one]; rw [chromaticNumber_le_iff_colorable]

/--
theorem `colorable_chromaticNumber` / 定理 `colorable_chromaticNumber`

English:
theorem colorable_chromaticNumber
  given: {m : Nat} (hc : G.Colorable m)
  proof: by
  classical
  rw [hc.chromaticNumber_eq_sInf]; rw [Nat.sInf_def]
  · apply Nat.find_spec
  · exact colorable_set_nonempty_of_colorable hc

中文:
定理 colorable_chromaticNumber
  条件: {m : 自然数} (hc : G.Colorable m)
  证明: by
  classical
  rw [hc.chromaticNumber_eq_sInf]; rw [Nat.sInf_def]
  · apply Nat.find_spec
  · exact colorable_set_nonempty_of_colorable hc

Depends on / 依赖: Nat.find_spec, Nat.sInf_def, chromaticNumber_eq_sInf, classical, colorable_set_nonempty_of_colorable, find_spec, hc.chromaticNumber_eq_sInf, sInf_def
-/
theorem colorable_chromaticNumber {m : Nat} (hc : G.Colorable m) :
    G.Colorable (ENat.toNat G.chromaticNumber) := by
  classical
  rw [hc.chromaticNumber_eq_sInf]; rw [Nat.sInf_def]
  · apply Nat.find_spec
  · exact colorable_set_nonempty_of_colorable hc

/--
theorem `colorable_chromaticNumber_of_fintype` / 定理 `colorable_chromaticNumber_of_fintype`

English:
theorem colorable_chromaticNumber_of_fintype
  given: (G : SimpleGraph V) [Finite V]
  proof: by
  cases nonempty_fintype V
  exact colorable_chromaticNumber G.colorable_of_fintype

中文:
定理 colorable_chromaticNumber_of_fintype
  条件: (G : 简单图 V) [有限 V]
  证明: by
  cases nonempty_fintype V
  exact colorable_chromaticNumber G.colorable_of_fintype

Depends on / 依赖: G.colorable_of_fintype, colorable_chromaticNumber, colorable_of_fintype, nonempty_fintype
-/
theorem colorable_chromaticNumber_of_fintype (G : SimpleGraph V) [Finite V] :
    G.Colorable (ENat.toNat G.chromaticNumber) := by
  cases nonempty_fintype V
  exact colorable_chromaticNumber G.colorable_of_fintype

/--
theorem `chromaticNumber_le_one_of_subsingleton` / 定理 `chromaticNumber_le_one_of_subsingleton`

English:
theorem chromaticNumber_le_one_of_subsingleton
  given: (G : SimpleGraph V) [Subsingleton V]
  proof: by
  rw [← Nat.cast_one]; rw [chromaticNumber_le_iff_colorable]
  refine ⟨Coloring.mk (fun _ => 0) ?_⟩
  intro v w
  cases Subsingleton.elim v w
  simp

中文:
定理 chromaticNumber_le_one_of_subsingleton
  条件: (G : 简单图 V) [子单例 V]
  证明: by
  rw [← Nat.cast_one]; rw [chromaticNumber_le_iff_colorable]
  refine ⟨Coloring.mk (fun _ => 0) ?_⟩
  intro v w
  cases Subsingleton.elim v w
  simp

Depends on / 依赖: Coloring, Coloring.mk, Nat.cast_one, Subsingleton, Subsingleton.elim, cast_one, chromaticNumber_le_iff_colorable
-/
theorem chromaticNumber_le_one_of_subsingleton (G : SimpleGraph V) [Subsingleton V] :
    G.chromaticNumber <= 1 := by
  rw [← Nat.cast_one]; rw [chromaticNumber_le_iff_colorable]
  refine ⟨Coloring.mk (fun _ => 0) ?_⟩
  intro v w
  cases Subsingleton.elim v w
  simp

/--
theorem `Colorable.chromaticNumber_pos` / 定理 `Colorable.chromaticNumber_pos`

English:
theorem Colorable.chromaticNumber_pos
  given: [Nonempty V] {n : Nat} (hc : G.Colorable n)
  proof: by
  rw [hc.chromaticNumber_eq_sInf]; rw [Nat.cast_pos]
  apply le_csInf (colorable_set_nonempty_of_colorable hc)
  intro m hm
  by_contra h'
  simp only [not_le] at h'
  obtain ⟨i, hi⟩ := hm.some (Classical.arbitrary V)
  have h₁ : i < 0 := lt_of_lt_of_le hi (Nat.le_of_lt_succ h')
  exact Nat.not_lt_zero _ h₁

@[deprecated (since := "2026-05-20")] alias chromaticNumber_pos := Colorable.chromaticNumber_pos

中文:
定理 Colorable.chromaticNumber_pos
  条件: [非空 V] {n : 自然数} (hc : G.Colorable n)
  证明: by
  rw [hc.chromaticNumber_eq_sInf]; rw [Nat.cast_pos]
  apply le_csInf (colorable_set_nonempty_of_colorable hc)
  intro m hm
  by_contra h'
  simp only [not_le] at h'
  obtain ⟨i, hi⟩ := hm.some (Classical.arbitrary V)
  have h₁ : i < 0 := lt_of_lt_of_le hi (Nat.le_of_lt_succ h')
  exact Nat.not_lt_zero _ h₁

@[deprecated (since := "2026-05-20")] alias chromaticNumber_pos := Colorable.chromaticNumber_pos

Depends on / 依赖: Classical, Classical.arbitrary, Nat.cast_pos, Nat.le_of_lt_succ, Nat.not_lt_zero, arbitrary, cast_pos, chromaticNumber_eq_sInf, colorable_set_nonempty_of_colorable, hc.chromaticNumber_eq_sInf, hm.some, le_csInf, le_of_lt_succ, lt_of_lt_of_le, not_le, not_lt_zero
-/
theorem Colorable.chromaticNumber_pos [Nonempty V] {n : Nat} (hc : G.Colorable n) :
    0 < G.chromaticNumber := by
  rw [hc.chromaticNumber_eq_sInf]; rw [Nat.cast_pos]
  apply le_csInf (colorable_set_nonempty_of_colorable hc)
  intro m hm
  by_contra h'
  simp only [not_le] at h'
  obtain ⟨i, hi⟩ := hm.some (Classical.arbitrary V)
  have h₁ : i < 0 := lt_of_lt_of_le hi (Nat.le_of_lt_succ h')
  exact Nat.not_lt_zero _ h₁

@[deprecated (since := "2026-05-20")] alias chromaticNumber_pos := Colorable.chromaticNumber_pos

/--
theorem `colorable_of_chromaticNumber_ne_top` / 定理 `colorable_of_chromaticNumber_ne_top`

English:
theorem colorable_of_chromaticNumber_ne_top
  given: (h : G.chromaticNumber != ⊤)
  proof: by
  rw [chromaticNumber_ne_top_iff_exists] at h
  obtain ⟨n, hn⟩ := h
  exact colorable_chromaticNumber hn

中文:
定理 colorable_of_chromaticNumber_ne_top
  条件: (h : G.chromaticNumber != ⊤)
  证明: by
  rw [chromaticNumber_ne_top_iff_exists] at h
  obtain ⟨n, hn⟩ := h
  exact colorable_chromaticNumber hn

Depends on / 依赖: chromaticNumber_ne_top_iff_exists, colorable_chromaticNumber
-/
theorem colorable_of_chromaticNumber_ne_top (h : G.chromaticNumber != ⊤) :
    G.Colorable (ENat.toNat G.chromaticNumber) := by
  rw [chromaticNumber_ne_top_iff_exists] at h
  obtain ⟨n, hn⟩ := h
  exact colorable_chromaticNumber hn

/--
theorem `Colorable.mono_left` / 定理 `Colorable.mono_left`

English:
theorem Colorable.mono_left
  given: {G' : SimpleGraph V} (h : G <= G') {n : Nat} (hc : G'.Colorable n)
  proof: ⟨hc.some.comp (.ofLE h)⟩

中文:
定理 Colorable.mono_left
  条件: {G' : 简单图 V} (h : G <= G') {n : 自然数} (hc : G'.Colorable n)
  证明: ⟨hc.some.comp (.ofLE h)⟩

Depends on / 依赖: hc.some.comp
-/
theorem Colorable.mono_left {G' : SimpleGraph V} (h : G <= G') {n : Nat} (hc : G'.Colorable n) :
    G.Colorable n :=
  ⟨hc.some.comp (.ofLE h)⟩

/--
theorem `chromaticNumber_le_of_forall_imp` / 定理 `chromaticNumber_le_of_forall_imp`

English:
theorem chromaticNumber_le_of_forall_imp
  statement: {V' : Type*} {G' : SimpleGraph V'}
  proof: by
  rw [chromaticNumber]; rw [chromaticNumber]
  simp only [Set.mem_ofPred_eq, le_iInf_iff]
  intro m hc
  have := h _ hc
  rw [← chromaticNumber_le_iff_colorable] at this
  exact this

中文:
定理 chromaticNumber_le_of_对任意_imp
  结论: {V' : 类型} {G' : 简单图 V'}
  证明: by
  rw [chromaticNumber]; rw [chromaticNumber]
  simp only [Set.mem_ofPred_eq, le_iInf_iff]
  intro m hc
  have := h _ hc
  rw [← chromaticNumber_le_iff_colorable] at this
  exact this

Depends on / 依赖: Set.mem_ofPred_eq, chromaticNumber, chromaticNumber_le_iff_colorable, le_iInf_iff, mem_ofPred_eq
-/
theorem chromaticNumber_le_of_forall_imp {V' : Type*} {G' : SimpleGraph V'}
    (h : forall n, G'.Colorable n -> G.Colorable n) :
    G.chromaticNumber <= G'.chromaticNumber := by
  rw [chromaticNumber]; rw [chromaticNumber]
  simp only [Set.mem_ofPred_eq, le_iInf_iff]
  intro m hc
  have := h _ hc
  rw [← chromaticNumber_le_iff_colorable] at this
  exact this

/--
theorem `chromaticNumber_mono` / 定理 `chromaticNumber_mono`

English:
theorem chromaticNumber_mono
  statement: (G' : SimpleGraph V)
  proof: chromaticNumber_le_of_forall_imp fun _ => Colorable.mono_left h

中文:
定理 chromaticNumber_mono
  结论: (G' : 简单图 V)
  证明: chromaticNumber_le_of_forall_imp fun _ => Colorable.mono_left h

Depends on / 依赖: Colorable, Colorable.mono_left, chromaticNumber_le_of_forall_imp, mono_left
-/
theorem chromaticNumber_mono (G' : SimpleGraph V)
    (h : G <= G') : G.chromaticNumber <= G'.chromaticNumber :=
  chromaticNumber_le_of_forall_imp fun _ => Colorable.mono_left h

/--
theorem `chromaticNumber_mono_of_hom` / 定理 `chromaticNumber_mono_of_hom`

English:
theorem chromaticNumber_mono_of_hom
  given: {V' : Type*} {G' : SimpleGraph V'} (f : G ->g G')
  proof: chromaticNumber_le_of_forall_imp fun _ hc => hc.of_hom f

中文:
定理 chromaticNumber_mono_of_hom
  条件: {V' : 类型} {G' : 简单图 V'} (f : G ->g G')
  证明: chromaticNumber_le_of_forall_imp fun _ hc => hc.of_hom f

Depends on / 依赖: chromaticNumber_le_of_forall_imp, hc.of_hom, of_hom
-/
theorem chromaticNumber_mono_of_hom {V' : Type*} {G' : SimpleGraph V'} (f : G ->g G') :
    G.chromaticNumber <= G'.chromaticNumber :=
  chromaticNumber_le_of_forall_imp fun _ hc => hc.of_hom f

/--
lemma `card_le_chromaticNumber_iff_forall_surjective` / 引理 `card_le_chromaticNumber_iff_forall_surjective`

English:
lemma card_le_chromaticNumber_iff_forall_surjective
  given: [Fintype α]
  proof: by
  refine ⟨fun h C => ?_, fun h => ?_⟩
  · rw [C.colorable.chromaticNumber_eq_sInf, Nat.cast_le] at h
    intro i
    by_contra! hi
    let D : G.Coloring {a // a != i} := ⟨fun v => ⟨C v, hi v⟩, (C.valid · <| congr_arg Subtype.val ·)⟩
    classical
    exact Nat.notMem_of_lt_sInf ((Nat.sub_one_lt_of_lt <| card_pos_iff.2 ⟨i⟩).trans_le h)
      ⟨G.recolorOfEquiv (equivOfCardEq <| by simp) D⟩
  · simp only [chromaticNumber, Set.mem_ofPred_eq, le_iInf_iff, Nat.cast_le]
    rintro i ⟨C⟩
    contrapose! h
    refine ⟨G.recolorOfCardLE (by simpa using h.le) C, fun hC => ?_⟩
    dsimp at hC
    simpa [h.not_ge] using Fintype.card_le_of_surjective _ hC.of_comp

中文:
引理 card_le_chromaticNumber_iff_对任意_surjective
  条件: [有限类型 α]
  证明: by
  refine ⟨fun h C => ?_, fun h => ?_⟩
  · rw [C.colorable.chromaticNumber_eq_sInf, Nat.cast_le] at h
    intro i
    by_contra! hi
    let D : G.Coloring {a // a != i} := ⟨fun v => ⟨C v, hi v⟩, (C.valid · <| congr_arg Subtype.val ·)⟩
    classical
    exact Nat.notMem_of_lt_sInf ((Nat.sub_one_lt_of_lt <| card_pos_iff.2 ⟨i⟩).trans_le h)
      ⟨G.recolorOfEquiv (equivOfCardEq <| by simp) D⟩
  · simp only [chromaticNumber, Set.mem_ofPred_eq, le_iInf_iff, Nat.cast_le]
    rintro i ⟨C⟩
    contrapose! h
    refine ⟨G.recolorOfCardLE (by simpa using h.le) C, fun hC => ?_⟩
    dsimp at hC
    simpa [h.not_ge] using Fintype.card_le_of_surjective _ hC.of_comp

Depends on / 依赖: C.colorable.chromaticNumber_eq_sInf, C.valid, Coloring, G.Coloring, G.recolorOfCardLE, G.recolorOfEquiv, Nat.cast_le, Nat.notMem_of_lt_sInf, Nat.sub_one_lt_of_lt, Set.mem_ofPred_eq, Subtype, Subtype.val, card_pos_iff, cast_le, chromaticNumber, chromaticNumber_eq_sInf, classical, colorable, congr_arg, contrapose
-/
lemma card_le_chromaticNumber_iff_forall_surjective [Fintype α] :
    card α <= G.chromaticNumber ↔ forall C : G.Coloring α, Surjective C := by
  refine ⟨fun h C => ?_, fun h => ?_⟩
  · rw [C.colorable.chromaticNumber_eq_sInf, Nat.cast_le] at h
    intro i
    by_contra! hi
    let D : G.Coloring {a // a != i} := ⟨fun v => ⟨C v, hi v⟩, (C.valid · <| congr_arg Subtype.val ·)⟩
    classical
    exact Nat.notMem_of_lt_sInf ((Nat.sub_one_lt_of_lt <| card_pos_iff.2 ⟨i⟩).trans_le h)
      ⟨G.recolorOfEquiv (equivOfCardEq <| by simp) D⟩
  · simp only [chromaticNumber, Set.mem_ofPred_eq, le_iInf_iff, Nat.cast_le]
    rintro i ⟨C⟩
    contrapose! h
    refine ⟨G.recolorOfCardLE (by simpa using h.le) C, fun hC => ?_⟩
    dsimp at hC
    simpa [h.not_ge] using Fintype.card_le_of_surjective _ hC.of_comp

/--
lemma `le_chromaticNumber_iff_forall_surjective` / 引理 `le_chromaticNumber_iff_forall_surjective`

English:
lemma le_chromaticNumber_iff_forall_surjective
  proof: by
  simp [← card_le_chromaticNumber_iff_forall_surjective]

中文:
引理 le_chromaticNumber_iff_对任意_surjective
  证明: by
  simp [← card_le_chromaticNumber_iff_forall_surjective]

Depends on / 依赖: card_le_chromaticNumber_iff_forall_surjective
-/
lemma le_chromaticNumber_iff_forall_surjective :
    n <= G.chromaticNumber ↔ forall C : G.Coloring (Fin n), Surjective C := by
  simp [← card_le_chromaticNumber_iff_forall_surjective]

/--
lemma `chromaticNumber_eq_card_iff_forall_surjective` / 引理 `chromaticNumber_eq_card_iff_forall_surjective`

English:
lemma chromaticNumber_eq_card_iff_forall_surjective
  given: [Fintype α] (hG : G.Colorable (card α))
  proof: by
  rw [← hG.chromaticNumber_le.ge_iff_eq]; rw [card_le_chromaticNumber_iff_forall_surjective]

中文:
引理 chromaticNumber_eq_card_iff_对任意_surjective
  条件: [有限类型 α] (hG : G.Colorable (card α))
  证明: by
  rw [← hG.chromaticNumber_le.ge_iff_eq]; rw [card_le_chromaticNumber_iff_forall_surjective]

Depends on / 依赖: card_le_chromaticNumber_iff_forall_surjective, chromaticNumber_le, ge_iff_eq, hG.chromaticNumber_le.ge_iff_eq
-/
lemma chromaticNumber_eq_card_iff_forall_surjective [Fintype α] (hG : G.Colorable (card α)) :
    G.chromaticNumber = card α ↔ forall C : G.Coloring α, Surjective C := by
  rw [← hG.chromaticNumber_le.ge_iff_eq]; rw [card_le_chromaticNumber_iff_forall_surjective]

/--
lemma `chromaticNumber_eq_iff_forall_surjective` / 引理 `chromaticNumber_eq_iff_forall_surjective`

English:
lemma chromaticNumber_eq_iff_forall_surjective
  given: (hG : G.Colorable n)
  proof: by
  rw [← hG.chromaticNumber_le.ge_iff_eq]; rw [le_chromaticNumber_iff_forall_surjective]

中文:
引理 chromaticNumber_eq_iff_对任意_surjective
  条件: (hG : G.Colorable n)
  证明: by
  rw [← hG.chromaticNumber_le.ge_iff_eq]; rw [le_chromaticNumber_iff_forall_surjective]

Depends on / 依赖: chromaticNumber_le, ge_iff_eq, hG.chromaticNumber_le.ge_iff_eq, le_chromaticNumber_iff_forall_surjective
-/
lemma chromaticNumber_eq_iff_forall_surjective (hG : G.Colorable n) :
    G.chromaticNumber = n ↔ forall C : G.Coloring (Fin n), Surjective C := by
  rw [← hG.chromaticNumber_le.ge_iff_eq]; rw [le_chromaticNumber_iff_forall_surjective]

/--
theorem `chromaticNumber_bot` / 定理 `chromaticNumber_bot`

English:
theorem chromaticNumber_bot
  given: [Nonempty V]
  statement: (⊥ : SimpleGraph V).chromaticNumber = 1
  proof: have : (⊥ : SimpleGraph V).Colorable 1 := by simp
this.chromaticNumber_le.antisymm Order.one_le_iff_pos.2 this.chromaticNumber_pos

@[simp]

中文:
定理 chromaticNumber_bot
  条件: [非空 V]
  结论: (⊥ : 简单图 V).chromaticNumber = 1
  证明: have : (⊥ : SimpleGraph V).Colorable 1 := by simp
this.chromaticNumber_le.antisymm Order.one_le_iff_pos.2 this.chromaticNumber_pos

@[simp]

Depends on / 依赖: Colorable, Order.one_le_iff_pos, SimpleGraph, antisymm, chromaticNumber_le, chromaticNumber_pos, one_le_iff_pos, this.chromaticNumber_le.antisymm, this.chromaticNumber_pos
-/
theorem chromaticNumber_bot [Nonempty V] : (⊥ : SimpleGraph V).chromaticNumber = 1 :=
  have : (⊥ : SimpleGraph V).Colorable 1 := by simp
this.chromaticNumber_le.antisymm Order.one_le_iff_pos.2 this.chromaticNumber_pos

@[simp]
/--
theorem `chromaticNumber_top` / 定理 `chromaticNumber_top`

English:
theorem chromaticNumber_top
  given: [Fintype V]
  statement: (⊤ : SimpleGraph V).chromaticNumber = Fintype.card V
  proof: by
  rw [chromaticNumber_eq_card_iff_forall_surjective (selfColoring _).colorable]
  intro C
  rw [← Finite.injective_iff_surjective]
  exact Hom.injective_of_top_hom C

@[simp]

中文:
定理 chromaticNumber_top
  条件: [有限类型 V]
  结论: (⊤ : 简单图 V).chromaticNumber = 有限类型.card V
  证明: by
  rw [chromaticNumber_eq_card_iff_forall_surjective (selfColoring _).colorable]
  intro C
  rw [← Finite.injective_iff_surjective]
  exact Hom.injective_of_top_hom C

@[simp]

Depends on / 依赖: Finite, Finite.injective_iff_surjective, Hom.injective_of_top_hom, chromaticNumber_eq_card_iff_forall_surjective, colorable, injective_iff_surjective, injective_of_top_hom, selfColoring
-/
theorem chromaticNumber_top [Fintype V] : (⊤ : SimpleGraph V).chromaticNumber = Fintype.card V := by
  rw [chromaticNumber_eq_card_iff_forall_surjective (selfColoring _).colorable]
  intro C
  rw [← Finite.injective_iff_surjective]
  exact Hom.injective_of_top_hom C

@[simp]
/--
theorem `chromaticNumber_top_eq_top_of_infinite` / 定理 `chromaticNumber_top_eq_top_of_infinite`

English:
theorem chromaticNumber_top_eq_top_of_infinite
  given: (V : Type*) [Infinite V]
  proof: by
  by_contra hc
  rw [← Ne]; rw [chromaticNumber_ne_top_iff_exists] at hc
  obtain ⟨n, ⟨hn⟩⟩ := hc
  exact not_injective_infinite_finite _ hn.injective_of_top_hom

@[simp]

中文:
定理 chromaticNumber_top_eq_top_of_infinite
  条件: (V : 类型) [无限 V]
  证明: by
  by_contra hc
  rw [← Ne]; rw [chromaticNumber_ne_top_iff_exists] at hc
  obtain ⟨n, ⟨hn⟩⟩ := hc
  exact not_injective_infinite_finite _ hn.injective_of_top_hom

@[simp]

Depends on / 依赖: chromaticNumber_ne_top_iff_exists, hn.injective_of_top_hom, injective_of_top_hom, not_injective_infinite_finite
-/
theorem chromaticNumber_top_eq_top_of_infinite (V : Type*) [Infinite V] :
    (⊤ : SimpleGraph V).chromaticNumber = ⊤ := by
  by_contra hc
  rw [← Ne]; rw [chromaticNumber_ne_top_iff_exists] at hc
  obtain ⟨n, ⟨hn⟩⟩ := hc
  exact not_injective_infinite_finite _ hn.injective_of_top_hom

@[simp]
/--
theorem `chromaticNumber_top_eq_enat_card` / 定理 `chromaticNumber_top_eq_enat_card`

English:
theorem chromaticNumber_top_eq_enat_card
  statement: (⊤ : SimpleGraph V).chromaticNumber = ENat.card V
  proof: by
  cases finite_or_infinite V
  · have := Fintype.ofFinite ‹_›
    simp
  · simp

中文:
定理 chromaticNumber_top_eq_enat_card
  结论: (⊤ : 简单图 V).chromaticNumber = E自然数.card V
  证明: by
  cases finite_or_infinite V
  · have := Fintype.ofFinite ‹_›
    simp
  · simp

Depends on / 依赖: Fintype, Fintype.ofFinite, finite_or_infinite, ofFinite
-/
theorem chromaticNumber_top_eq_enat_card : (⊤ : SimpleGraph V).chromaticNumber = ENat.card V := by
  cases finite_or_infinite V
  · have := Fintype.ofFinite ‹_›
    simp
  · simp

/--
theorem `eq_top_of_chromaticNumber_eq_card` / 定理 `eq_top_of_chromaticNumber_eq_card`

English:
theorem eq_top_of_chromaticNumber_eq_card
  statement: [Fintype V]
  proof: by
  classical
  by_contra! hh
  have : G.chromaticNumber <= Fintype.card V - 1 := by
    obtain ⟨a, b, hne, _⟩ := ne_top_iff_exists_not_adj.mp hh
    apply chromaticNumber_le_iff_colorable.mpr
    suffices G.Coloring (Finset.univ.erase b) by simpa using Coloring.colorable this
    apply Coloring.mk (fun x => if h' : x != b then ⟨x, by simp [h']⟩ else ⟨a, by simp [hne]⟩)
    grind [Adj.ne', adj_symm]
  rw [h]; rw [← ENat.natCast_one]; rw [← ENat.natCast_sub]; rw [ENat.natCast_le_natCast] at this
have := Fintype.one_lt_card_iff_nontrivial.mpr SimpleGraph.nontrivial_iff.mp ⟨_, _, hh⟩
  grind

中文:
定理 eq_top_of_chromaticNumber_eq_card
  结论: [有限类型 V]
  证明: by
  classical
  by_contra! hh
  have : G.chromaticNumber <= Fintype.card V - 1 := by
    obtain ⟨a, b, hne, _⟩ := ne_top_iff_exists_not_adj.mp hh
    apply chromaticNumber_le_iff_colorable.mpr
    suffices G.Coloring (Finset.univ.erase b) by simpa using Coloring.colorable this
    apply Coloring.mk (fun x => if h' : x != b then ⟨x, by simp [h']⟩ else ⟨a, by simp [hne]⟩)
    grind [Adj.ne', adj_symm]
  rw [h]; rw [← ENat.natCast_one]; rw [← ENat.natCast_sub]; rw [ENat.natCast_le_natCast] at this
have := Fintype.one_lt_card_iff_nontrivial.mpr SimpleGraph.nontrivial_iff.mp ⟨_, _, hh⟩
  grind

Depends on / 依赖: Adj.ne, Coloring, Coloring.colorable, Coloring.mk, ENat.natCast_le_natCast, ENat.natCast_one, ENat.natCast_sub, Finset, Finset.univ.erase, Fintype, Fintype.card, Fintype.one_lt_card, G.Coloring, G.chromaticNumber, adj_symm, chromaticNumber, chromaticNumber_le_iff_colorable, chromaticNumber_le_iff_colorable.mpr, classical, colorable
-/
theorem eq_top_of_chromaticNumber_eq_card [Fintype V]
    (h : G.chromaticNumber = Fintype.card V) : G = ⊤ := by
  classical
  by_contra! hh
  have : G.chromaticNumber <= Fintype.card V - 1 := by
    obtain ⟨a, b, hne, _⟩ := ne_top_iff_exists_not_adj.mp hh
    apply chromaticNumber_le_iff_colorable.mpr
    suffices G.Coloring (Finset.univ.erase b) by simpa using Coloring.colorable this
    apply Coloring.mk (fun x => if h' : x != b then ⟨x, by simp [h']⟩ else ⟨a, by simp [hne]⟩)
    grind [Adj.ne', adj_symm]
  rw [h]; rw [← ENat.natCast_one]; rw [← ENat.natCast_sub]; rw [ENat.natCast_le_natCast] at this
have := Fintype.one_lt_card_iff_nontrivial.mpr SimpleGraph.nontrivial_iff.mp ⟨_, _, hh⟩
  grind

/--
theorem `chromaticNumber_eq_card_iff` / 定理 `chromaticNumber_eq_card_iff`

English:
theorem chromaticNumber_eq_card_iff
  given: [Fintype V]
  proof: ⟨eq_top_of_chromaticNumber_eq_card, fun h => h ▸ chromaticNumber_top⟩

中文:
定理 chromaticNumber_eq_card_iff
  条件: [有限类型 V]
  证明: ⟨eq_top_of_chromaticNumber_eq_card, fun h => h ▸ chromaticNumber_top⟩

Depends on / 依赖: chromaticNumber_top, eq_top_of_chromaticNumber_eq_card
-/
theorem chromaticNumber_eq_card_iff [Fintype V] :
    G.chromaticNumber = Fintype.card V ↔ G = ⊤ :=
  ⟨eq_top_of_chromaticNumber_eq_card, fun h => h ▸ chromaticNumber_top⟩

/--
theorem `chromaticNumber_le_card` / 定理 `chromaticNumber_le_card`

English:
theorem chromaticNumber_le_card
  given: [Fintype V]
  statement: G.chromaticNumber <= Fintype.card V
  proof: by
  rw [← chromaticNumber_top]
  exact chromaticNumber_mono_of_hom G.selfColoring

中文:
定理 chromaticNumber_le_card
  条件: [有限类型 V]
  结论: G.chromaticNumber <= 有限类型.card V
  证明: by
  rw [← chromaticNumber_top]
  exact chromaticNumber_mono_of_hom G.selfColoring

Depends on / 依赖: G.selfColoring, chromaticNumber_mono_of_hom, chromaticNumber_top, selfColoring
-/
theorem chromaticNumber_le_card [Fintype V] : G.chromaticNumber <= Fintype.card V := by
  rw [← chromaticNumber_top]
  exact chromaticNumber_mono_of_hom G.selfColoring

/--
theorem `two_le_chromaticNumber_of_adj` / 定理 `two_le_chromaticNumber_of_adj`

English:
theorem two_le_chromaticNumber_of_adj
  given: {u v : V} (hadj : G.Adj u v)
  statement: 2 <= G.chromaticNumber
  proof: by
  refine le_of_not_gt fun h => ?_
  obtain ⟨c⟩ := chromaticNumber_le_iff_colorable.mp (Order.le_of_lt_add_one h)
  exact c.valid hadj (Subsingleton.elim (c u) (c v))

@[simp]

中文:
定理 two_le_chromaticNumber_of_adj
  条件: {u v : V} (hadj : G.伴随 u v)
  结论: 2 <= G.chromaticNumber
  证明: by
  refine le_of_not_gt fun h => ?_
  obtain ⟨c⟩ := chromaticNumber_le_iff_colorable.mp (Order.le_of_lt_add_one h)
  exact c.valid hadj (Subsingleton.elim (c u) (c v))

@[simp]

Depends on / 依赖: Order.le_of_lt_add_one, Subsingleton, Subsingleton.elim, c.valid, chromaticNumber_le_iff_colorable, chromaticNumber_le_iff_colorable.mp, le_of_lt_add_one, le_of_not_gt
-/
theorem two_le_chromaticNumber_of_adj {u v : V} (hadj : G.Adj u v) : 2 <= G.chromaticNumber := by
  refine le_of_not_gt fun h => ?_
  obtain ⟨c⟩ := chromaticNumber_le_iff_colorable.mp (Order.le_of_lt_add_one h)
  exact c.valid hadj (Subsingleton.elim (c u) (c v))

@[simp]
/--
theorem `chromaticNumber_eq_zero_iff` / 定理 `chromaticNumber_eq_zero_iff`

English:
theorem chromaticNumber_eq_zero_iff
  statement: G.chromaticNumber = 0 ↔ IsEmpty V
  proof: nonpos_iff_eq_zero.symm.trans chromaticNumber_le_iff_colorable.trans colorable_zero_iff

@[simp]

中文:
定理 chromaticNumber_eq_zero_iff
  结论: G.chromaticNumber = 0 ↔ 是空 V
  证明: nonpos_iff_eq_zero.symm.trans chromaticNumber_le_iff_colorable.trans colorable_zero_iff

@[simp]

Depends on / 依赖: chromaticNumber_le_iff_colorable, chromaticNumber_le_iff_colorable.trans, colorable_zero_iff, nonpos_iff_eq_zero, nonpos_iff_eq_zero.symm.trans
-/
theorem chromaticNumber_eq_zero_iff : G.chromaticNumber = 0 ↔ IsEmpty V :=
nonpos_iff_eq_zero.symm.trans chromaticNumber_le_iff_colorable.trans colorable_zero_iff

@[simp]
/--
theorem `chromaticNumber_eq_zero_of_isEmpty` / 定理 `chromaticNumber_eq_zero_of_isEmpty`

English:
theorem chromaticNumber_eq_zero_of_isEmpty
  given: [IsEmpty V]
  statement: G.chromaticNumber = 0
  proof: by
  simpa

@[deprecated (since := "2026-04-24")]
alias ⟨isEmpty_of_chromaticNumber_eq_zero, _⟩ := chromaticNumber_eq_zero_iff

中文:
定理 chromaticNumber_eq_zero_of_isEmpty
  条件: [是空 V]
  结论: G.chromaticNumber = 0
  证明: by
  simpa

@[deprecated (since := "2026-04-24")]
alias ⟨isEmpty_of_chromaticNumber_eq_zero, _⟩ := chromaticNumber_eq_zero_iff
-/
theorem chromaticNumber_eq_zero_of_isEmpty [IsEmpty V] : G.chromaticNumber = 0 := by
  simpa

@[deprecated (since := "2026-04-24")]
alias ⟨isEmpty_of_chromaticNumber_eq_zero, _⟩ := chromaticNumber_eq_zero_iff

/--
theorem `chromaticNumber_eq_one_iff` / 定理 `chromaticNumber_eq_one_iff`

English:
theorem chromaticNumber_eq_one_iff
  statement: G.chromaticNumber = 1 ↔ G = ⊥ ∧ Nonempty V
  proof: by
  rw [eq_iff_le_not_lt]; rw [Order.lt_one_iff_nonpos]; rw [← not_isEmpty_iff]; rw [← Nat.cast_one]; rw [← Nat.cast_zero]; rw [chromaticNumber_le_iff_colorable]; rw [chromaticNumber_le_iff_colorable]; rw [colorable_one_iff]; rw [colorable_zero_iff]

中文:
定理 chromaticNumber_eq_one_iff
  结论: G.chromaticNumber = 1 ↔ G = ⊥ ∧ 非空 V
  证明: by
  rw [eq_iff_le_not_lt]; rw [Order.lt_one_iff_nonpos]; rw [← not_isEmpty_iff]; rw [← Nat.cast_one]; rw [← Nat.cast_zero]; rw [chromaticNumber_le_iff_colorable]; rw [chromaticNumber_le_iff_colorable]; rw [colorable_one_iff]; rw [colorable_zero_iff]

Depends on / 依赖: Nat.cast_one, Nat.cast_zero, Order.lt_one_iff_nonpos, cast_one, cast_zero, chromaticNumber_le_iff_colorable, colorable_one_iff, colorable_zero_iff, eq_iff_le_not_lt, lt_one_iff_nonpos, not_isEmpty_iff
-/
theorem chromaticNumber_eq_one_iff : G.chromaticNumber = 1 ↔ G = ⊥ ∧ Nonempty V := by
  rw [eq_iff_le_not_lt]; rw [Order.lt_one_iff_nonpos]; rw [← not_isEmpty_iff]; rw [← Nat.cast_one]; rw [← Nat.cast_zero]; rw [chromaticNumber_le_iff_colorable]; rw [chromaticNumber_le_iff_colorable]; rw [colorable_one_iff]; rw [colorable_zero_iff]

/--
theorem `two_le_chromaticNumber_iff_ne_bot` / 定理 `two_le_chromaticNumber_iff_ne_bot`

English:
theorem two_le_chromaticNumber_iff_ne_bot
  statement: 2 <= G.chromaticNumber ↔ G != ⊥
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · contrapose! h
    by_cases h' : IsEmpty V
    · simp [chromaticNumber_eq_zero_of_isEmpty]
    · simp [chromaticNumber_eq_one_iff.mpr ⟨h, by simpa using h'⟩]
  · obtain ⟨_, _, h⟩ := ne_bot_iff_exists_adj.mp h
    exact two_le_chromaticNumber_of_adj h

中文:
定理 two_le_chromaticNumber_iff_ne_bot
  结论: 2 <= G.chromaticNumber ↔ G != ⊥
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · contrapose! h
    by_cases h' : IsEmpty V
    · simp [chromaticNumber_eq_zero_of_isEmpty]
    · simp [chromaticNumber_eq_one_iff.mpr ⟨h, by simpa using h'⟩]
  · obtain ⟨_, _, h⟩ := ne_bot_iff_exists_adj.mp h
    exact two_le_chromaticNumber_of_adj h

Depends on / 依赖: IsEmpty, chromaticNumber_eq_one_iff, chromaticNumber_eq_one_iff.mpr, chromaticNumber_eq_zero_of_isEmpty, contrapose, ne_bot_iff_exists_adj, ne_bot_iff_exists_adj.mp, two_le_chromaticNumber_of_adj
-/
theorem two_le_chromaticNumber_iff_ne_bot : 2 <= G.chromaticNumber ↔ G != ⊥ := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · contrapose! h
    by_cases h' : IsEmpty V
    · simp [chromaticNumber_eq_zero_of_isEmpty]
    · simp [chromaticNumber_eq_one_iff.mpr ⟨h, by simpa using h'⟩]
  · obtain ⟨_, _, h⟩ := ne_bot_iff_exists_adj.mp h
    exact two_le_chromaticNumber_of_adj h

/--
Definition of `CompleteBipartiteGraph.bicoloring` / `CompleteBipartiteGraph.bicoloring` 的定义

English:
definition CompleteBipartiteGraph.bicoloring
  signature: (V W : Type*)
  body: Coloring.mk (fun v => v.isRight)
    (by
      intro v w
      cases v <;> cases w <;> simp)

中文:
定义 CompleteBipartiteGraph.bicoloring
  签名: (V W : 类型)
  定义体: Coloring.mk (fun v => v.isRight)
    (by
      intro v w
      cases v <;> cases w <;> simp)

Depends on / 依赖: Coloring, Coloring.mk, isRight, v.isRight
-/
def CompleteBipartiteGraph.bicoloring (V W : Type*) : (completeBipartiteGraph V W).Coloring Bool :=
  Coloring.mk (fun v => v.isRight)
    (by
      intro v w
      cases v <;> cases w <;> simp)

/--
theorem `CompleteBipartiteGraph.chromaticNumber` / 定理 `CompleteBipartiteGraph.chromaticNumber`

English:
theorem CompleteBipartiteGraph.chromaticNumber
  given: {V W : Type*} [Nonempty V] [Nonempty W]
  proof: by
  rw [← Nat.cast_two]; rw [chromaticNumber_eq_iff_forall_surjective
    (by simpa using (CompleteBipartiteGraph.bicoloring V W).colorable)]
  intro C b
  have v := Classical.arbitrary V
  have w := Classical.arbitrary W
  have h : (completeBipartiteGraph V W).Adj (Sum.inl v) (Sum.inr w) := by simp
  by_cases he : C (Sum.inl v) = b
  · exact ⟨_, he⟩
  by_cases he' : C (Sum.inr w) = b
  · exact ⟨_, he'⟩
  · simpa using two_lt_card_iff.2 ⟨_, _, _, C.valid h, he, he'⟩

中文:
定理 CompleteBipartiteGraph.chromaticNumber
  条件: {V W : 类型} [非空 V] [非空 W]
  证明: by
  rw [← Nat.cast_two]; rw [chromaticNumber_eq_iff_forall_surjective
    (by simpa using (CompleteBipartiteGraph.bicoloring V W).colorable)]
  intro C b
  have v := Classical.arbitrary V
  have w := Classical.arbitrary W
  have h : (completeBipartiteGraph V W).Adj (Sum.inl v) (Sum.inr w) := by simp
  by_cases he : C (Sum.inl v) = b
  · exact ⟨_, he⟩
  by_cases he' : C (Sum.inr w) = b
  · exact ⟨_, he'⟩
  · simpa using two_lt_card_iff.2 ⟨_, _, _, C.valid h, he, he'⟩

Depends on / 依赖: C.valid, Classical, Classical.arbitrary, CompleteBipartiteGraph, CompleteBipartiteGraph.bicoloring, Nat.cast_two, Sum.inl, Sum.inr, arbitrary, bicoloring, cast_two, chromaticNumber_eq_iff_forall_surjective, colorable, completeBipartiteGraph, two_lt_card_iff
-/
theorem CompleteBipartiteGraph.chromaticNumber {V W : Type*} [Nonempty V] [Nonempty W] :
    (completeBipartiteGraph V W).chromaticNumber = 2 := by
  rw [← Nat.cast_two]; rw [chromaticNumber_eq_iff_forall_surjective
    (by simpa using (CompleteBipartiteGraph.bicoloring V W).colorable)]
  intro C b
  have v := Classical.arbitrary V
  have w := Classical.arbitrary W
  have h : (completeBipartiteGraph V W).Adj (Sum.inl v) (Sum.inr w) := by simp
  by_cases he : C (Sum.inl v) = b
  · exact ⟨_, he⟩
  by_cases he' : C (Sum.inr w) = b
  · exact ⟨_, he'⟩
  · simpa using two_lt_card_iff.2 ⟨_, _, _, C.valid h, he, he'⟩


/--
theorem `IsClique.card_le_of_colorable` / 定理 `IsClique.card_le_of_colorable`

English:
theorem IsClique.card_le_of_colorable
  given: {s : Finset V} (h : G.IsClique s) (hc : G.Colorable n)
  proof: by
simpa using! hc.card_le_of_pairwise_adj (Subtype.val : s -> V) by simpa [Pairwise] using! h

中文:
定理 IsClique.card_le_of_colorable
  条件: {s : 有限集 V} (h : G.IsClique s) (hc : G.Colorable n)
  证明: by
simpa using! hc.card_le_of_pairwise_adj (Subtype.val : s -> V) by simpa [Pairwise] using! h

Depends on / 依赖: Pairwise, Subtype, Subtype.val, card_le_of_pairwise_adj, hc.card_le_of_pairwise_adj
-/
theorem IsClique.card_le_of_colorable {s : Finset V} (h : G.IsClique s) (hc : G.Colorable n) :
    s.card <= n := by
simpa using! hc.card_le_of_pairwise_adj (Subtype.val : s -> V) by simpa [Pairwise] using! h

/--
theorem `IsClique.card_le_of_coloring` / 定理 `IsClique.card_le_of_coloring`

English:
theorem IsClique.card_le_of_coloring
  statement: {s : Finset V} (h : G.IsClique s) [Fintype α]
  proof: h.card_le_of_colorable C.colorable

中文:
定理 IsClique.card_le_of_coloring
  结论: {s : 有限集 V} (h : G.IsClique s) [有限类型 α]
  证明: h.card_le_of_colorable C.colorable

Depends on / 依赖: C.colorable, card_le_of_colorable, colorable, h.card_le_of_colorable
-/
theorem IsClique.card_le_of_coloring {s : Finset V} (h : G.IsClique s) [Fintype α]
    (C : G.Coloring α) : s.card <= Fintype.card α := h.card_le_of_colorable C.colorable

/--
theorem `IsClique.card_le_chromaticNumber` / 定理 `IsClique.card_le_chromaticNumber`

English:
theorem IsClique.card_le_chromaticNumber
  given: {s : Finset V} (h : G.IsClique s)
  proof: le_chromaticNumber_of_pairwise_adj (by simp) (Subtype.val : s -> V) by simpa [Pairwise] using! h

中文:
定理 IsClique.card_le_chromaticNumber
  条件: {s : 有限集 V} (h : G.IsClique s)
  证明: le_chromaticNumber_of_pairwise_adj (by simp) (Subtype.val : s -> V) by simpa [Pairwise] using! h

Depends on / 依赖: Pairwise, Subtype, Subtype.val, le_chromaticNumber_of_pairwise_adj
-/
theorem IsClique.card_le_chromaticNumber {s : Finset V} (h : G.IsClique s) :
    s.card <= G.chromaticNumber :=
le_chromaticNumber_of_pairwise_adj (by simp) (Subtype.val : s -> V) by simpa [Pairwise] using! h

/--
theorem `cliqueNum_le_chromaticNumber` / 定理 `cliqueNum_le_chromaticNumber`

English:
theorem cliqueNum_le_chromaticNumber
  statement: G.cliqueNum <= G.chromaticNumber
  proof: by
  have ⟨s, hs⟩ := G.exists_isNClique_cliqueNum
  exact hs.card_eq ▸ hs.isClique.card_le_chromaticNumber

中文:
定理 cliqueNum_le_chromaticNumber
  结论: G.cliqueNum <= G.chromaticNumber
  证明: by
  have ⟨s, hs⟩ := G.exists_isNClique_cliqueNum
  exact hs.card_eq ▸ hs.isClique.card_le_chromaticNumber

Depends on / 依赖: G.exists_isNClique_cliqueNum, card_eq, card_le_chromaticNumber, exists_isNClique_cliqueNum, hs.card_eq, hs.isClique.card_le_chromaticNumber, isClique
-/
theorem cliqueNum_le_chromaticNumber : G.cliqueNum <= G.chromaticNumber := by
  have ⟨s, hs⟩ := G.exists_isNClique_cliqueNum
  exact hs.card_eq ▸ hs.isClique.card_le_chromaticNumber

/--
theorem `Colorable.cliqueFree` / 定理 `Colorable.cliqueFree`

English:
theorem Colorable.cliqueFree
  given: {n m : Nat} (hc : G.Colorable n) (hm : n < m)
  proof: by
  by_contra h
  simp only [CliqueFree, isNClique_iff, not_forall, Classical.not_not] at h
  obtain ⟨s, h, rfl⟩ := h
  exact Nat.lt_le_asymm hm (h.card_le_of_colorable hc)

中文:
定理 Colorable.cliqueFree
  条件: {n m : 自然数} (hc : G.Colorable n) (hm : n < m)
  证明: by
  by_contra h
  simp only [CliqueFree, isNClique_iff, not_forall, Classical.not_not] at h
  obtain ⟨s, h, rfl⟩ := h
  exact Nat.lt_le_asymm hm (h.card_le_of_colorable hc)
-/
protected theorem Colorable.cliqueFree {n m : Nat} (hc : G.Colorable n) (hm : n < m) :
    G.CliqueFree m := by
  by_contra h
  simp only [CliqueFree, isNClique_iff, not_forall, Classical.not_not] at h
  obtain ⟨s, h, rfl⟩ := h
  exact Nat.lt_le_asymm hm (h.card_le_of_colorable hc)

/--
theorem `cliqueFree_of_chromaticNumber_lt` / 定理 `cliqueFree_of_chromaticNumber_lt`

English:
theorem cliqueFree_of_chromaticNumber_lt
  given: {n : Nat} (hc : G.chromaticNumber < n)
  proof: by
  have hne : G.chromaticNumber != ⊤ := hc.ne_top
  obtain ⟨m, hc'⟩ := chromaticNumber_ne_top_iff_exists.mp hne
  have := colorable_chromaticNumber hc'
  refine this.cliqueFree ?_
  rw [← ENat.natCast_toNat_eq_self] at hne
  rw [← hne] at hc
  simpa using hc

中文:
定理 cliqueFree_of_chromaticNumber_lt
  条件: {n : 自然数} (hc : G.chromaticNumber < n)
  证明: by
  have hne : G.chromaticNumber != ⊤ := hc.ne_top
  obtain ⟨m, hc'⟩ := chromaticNumber_ne_top_iff_exists.mp hne
  have := colorable_chromaticNumber hc'
  refine this.cliqueFree ?_
  rw [← ENat.natCast_toNat_eq_self] at hne
  rw [← hne] at hc
  simpa using hc

Depends on / 依赖: ENat.natCast_toNat_eq_self, G.chromaticNumber, chromaticNumber, chromaticNumber_ne_top_iff_exists, chromaticNumber_ne_top_iff_exists.mp, cliqueFree, colorable_chromaticNumber, hc.ne_top, natCast_toNat_eq_self, ne_top, this.cliqueFree
-/
theorem cliqueFree_of_chromaticNumber_lt {n : Nat} (hc : G.chromaticNumber < n) :
    G.CliqueFree n := by
  have hne : G.chromaticNumber != ⊤ := hc.ne_top
  obtain ⟨m, hc'⟩ := chromaticNumber_ne_top_iff_exists.mp hne
  have := colorable_chromaticNumber hc'
  refine this.cliqueFree ?_
  rw [← ENat.natCast_toNat_eq_self] at hne
  rw [← hne] at hc
  simpa using hc

/--
lemma `Coloring.surjOn_of_card_le_isClique` / 引理 `Coloring.surjOn_of_card_le_isClique`

English:
lemma Coloring.surjOn_of_card_le_isClique
  statement: [Fintype α] {s : Finset V} (h : G.IsClique s)
  proof: by
  intro _ _
  obtain ⟨_, hx⟩ := card_le_chromaticNumber_iff_forall_surjective.mp
                    (by simp_all [← induce_eq_top]) (C.comp (Embedding.induce s).toHom) _
  exact ⟨_, Subtype.coe_prop _, hx⟩

中文:
引理 染色.surjOn_of_card_le_isClique
  结论: [有限类型 α] {s : 有限集 V} (h : G.IsClique s)
  证明: by
  intro _ _
  obtain ⟨_, hx⟩ := card_le_chromaticNumber_iff_forall_surjective.mp
                    (by simp_all [← induce_eq_top]) (C.comp (Embedding.induce s).toHom) _
  exact ⟨_, Subtype.coe_prop _, hx⟩

Depends on / 依赖: C.comp, Embedding, Embedding.induce, Subtype, Subtype.coe_prop, card_le_chromaticNumber_iff_forall_surjective, card_le_chromaticNumber_iff_forall_surjective.mp, coe_prop, induce, induce_eq_top
-/
lemma Coloring.surjOn_of_card_le_isClique [Fintype α] {s : Finset V} (h : G.IsClique s)
    (hc : Fintype.card α <= s.card) (C : G.Coloring α) : Set.SurjOn C s Set.univ := by
  intro _ _
  obtain ⟨_, hx⟩ := card_le_chromaticNumber_iff_forall_surjective.mp
                    (by simp_all [← induce_eq_top]) (C.comp (Embedding.induce s).toHom) _
  exact ⟨_, Subtype.coe_prop _, hx⟩

namespace completeMultipartiteGraph

variable {ι : Type*} (V : ι -> Type*)

/--
Definition of `coloring` / `coloring` 的定义

English:
definition coloring
  signature: : (completeMultipartiteGraph V).Coloring ι
  body: Coloring.mk (fun v => v.1) (by simp)

中文:
定义 coloring
  签名: : (completeMultipartiteGraph V).染色 ι
  定义体: Coloring.mk (fun v => v.1) (by simp)

Depends on / 依赖: Coloring, Coloring.mk
-/
def coloring : (completeMultipartiteGraph V).Coloring ι := Coloring.mk (fun v => v.1) (by simp)

/--
lemma `colorable` / 引理 `colorable`

English:
lemma colorable
  given: [Fintype ι]
  statement: (completeMultipartiteGraph V).Colorable (Fintype.card ι)
  proof: (coloring V).colorable

中文:
引理 colorable
  条件: [有限类型 ι]
  结论: (completeMultipartiteGraph V).Colorable (有限类型.card ι)
  证明: (coloring V).colorable

Depends on / 依赖: colorable, coloring
-/
lemma colorable [Fintype ι] : (completeMultipartiteGraph V).Colorable (Fintype.card ι) :=
  (coloring V).colorable

/--
theorem `chromaticNumber` / 定理 `chromaticNumber`

English:
theorem chromaticNumber
  given: [Fintype ι] (f : forall (i : ι), V i)
  proof: by
  apply le_antisymm (colorable V).chromaticNumber_le
  by_contra! h
exact not_cliqueFree_of_le_card V f le_rfl cliqueFree_of_chromaticNumber_lt h

中文:
定理 chromaticNumber
  条件: [有限类型 ι] (f : 对任意 (i : ι), V i)
  证明: by
  apply le_antisymm (colorable V).chromaticNumber_le
  by_contra! h
exact not_cliqueFree_of_le_card V f le_rfl cliqueFree_of_chromaticNumber_lt h

Depends on / 依赖: chromaticNumber_le, cliqueFree_of_chromaticNumber_lt, colorable, le_antisymm, le_rfl, not_cliqueFree_of_le_card
-/
theorem chromaticNumber [Fintype ι] (f : forall (i : ι), V i) :
    (completeMultipartiteGraph V).chromaticNumber = Fintype.card ι := by
  apply le_antisymm (colorable V).chromaticNumber_le
  by_contra! h
exact not_cliqueFree_of_le_card V f le_rfl cliqueFree_of_chromaticNumber_lt h

/--
theorem `colorable_of_cliqueFree` / 定理 `colorable_of_cliqueFree`

English:
theorem colorable_of_cliqueFree
  statement: (f : forall (i : ι), V i)
  proof: by
  cases n with
  | zero => exact absurd hc not_cliqueFree_zero
  | succ n =>
  have : Fintype ι := fintypeOfNotInfinite
    fun hinf => not_cliqueFree_of_infinite V f hc
  apply (coloring V).colorable.mono
  have := not_cliqueFree_of_le_card V f le_rfl
  contrapose! this
  exact hc.mono this

中文:
定理 colorable_of_cliqueFree
  结论: (f : 对任意 (i : ι), V i)
  证明: by
  cases n with
  | zero => exact absurd hc not_cliqueFree_zero
  | succ n =>
  have : Fintype ι := fintypeOfNotInfinite
    fun hinf => not_cliqueFree_of_infinite V f hc
  apply (coloring V).colorable.mono
  have := not_cliqueFree_of_le_card V f le_rfl
  contrapose! this
  exact hc.mono this

Depends on / 依赖: Fintype, absurd, colorable, colorable.mono, coloring, contrapose, fintypeOfNotInfinite, hc.mono, le_rfl, not_cliqueFree_of_infinite, not_cliqueFree_of_le_card, not_cliqueFree_zero
-/
theorem colorable_of_cliqueFree (f : forall (i : ι), V i)
    (hc : (completeMultipartiteGraph V).CliqueFree n) :
    (completeMultipartiteGraph V).Colorable (n - 1) := by
  cases n with
  | zero => exact absurd hc not_cliqueFree_zero
  | succ n =>
  have : Fintype ι := fintypeOfNotInfinite
    fun hinf => not_cliqueFree_of_infinite V f hc
  apply (coloring V).colorable.mono
  have := not_cliqueFree_of_le_card V f le_rfl
  contrapose! this
  exact hc.mono this

end completeMultipartiteGraph

variable {W : Type*} {H : SimpleGraph W}

/--
theorem `free_of_colorable` / 定理 `free_of_colorable`

English:
theorem free_of_colorable
  given: (nhc : ¬H.Colorable n) (hc : G.Colorable n)
  statement: H.Free G
  proof: by
  contrapose! nhc with hc'
  exact hc.of_hom hc'.some.toHom

中文:
定理 free_of_colorable
  条件: (nhc : ¬H.Colorable n) (hc : G.Colorable n)
  结论: H.自由 G
  证明: by
  contrapose! nhc with hc'
  exact hc.of_hom hc'.some.toHom

Depends on / 依赖: contrapose, hc.of_hom, of_hom, some.toHom
-/
theorem free_of_colorable (nhc : ¬H.Colorable n) (hc : G.Colorable n) : H.Free G := by
  contrapose! nhc with hc'
  exact hc.of_hom hc'.some.toHom

/-! ### Isomorphisms -/

/--
Definition of `coloringCongr` / `coloringCongr` 的定义

English:
definition coloringCongr
  signature: (f : G ≃g H) (g : α ≃ β)
  body: f.homCongr (Iso.completeGraph g)

中文:
定义 coloringCongr
  签名: (f : G ≃g H) (g : α ≃ β)
  定义体: f.homCongr (Iso.completeGraph g)

Depends on / 依赖: Iso.completeGraph, completeGraph, f.homCongr, homCongr
-/
def coloringCongr (f : G ≃g H) (g : α ≃ β) : G.Coloring α ≃ H.Coloring β :=
  f.homCongr (Iso.completeGraph g)

/--
lemma `colorable_congr` / 引理 `colorable_congr`

English:
lemma colorable_congr
  given: (f : G ≃g H)
  statement: G.Colorable n ↔ H.Colorable n
  proof: ⟨fun hc => hc.of_hom f.symm.toHom, fun hc => hc.of_hom f.toHom⟩

中文:
引理 colorable_congr
  条件: (f : G ≃g H)
  结论: G.Colorable n ↔ H.Colorable n
  证明: ⟨fun hc => hc.of_hom f.symm.toHom, fun hc => hc.of_hom f.toHom⟩

Depends on / 依赖: f.symm.toHom, f.toHom, hc.of_hom, of_hom
-/
lemma colorable_congr (f : G ≃g H) : G.Colorable n ↔ H.Colorable n :=
  ⟨fun hc => hc.of_hom f.symm.toHom, fun hc => hc.of_hom f.toHom⟩

/--
lemma `chromaticNumber_congr` / 引理 `chromaticNumber_congr`

English:
lemma chromaticNumber_congr
  given: (f : G ≃g H)
  statement: G.chromaticNumber = H.chromaticNumber
  proof: le_antisymm (chromaticNumber_mono_of_hom f.toHom) (chromaticNumber_mono_of_hom f.symm.toHom)

中文:
引理 chromaticNumber_congr
  条件: (f : G ≃g H)
  结论: G.chromaticNumber = H.chromaticNumber
  证明: le_antisymm (chromaticNumber_mono_of_hom f.toHom) (chromaticNumber_mono_of_hom f.symm.toHom)

Depends on / 依赖: chromaticNumber_mono_of_hom, f.symm.toHom, f.toHom, le_antisymm
-/
lemma chromaticNumber_congr (f : G ≃g H) : G.chromaticNumber = H.chromaticNumber :=
  le_antisymm (chromaticNumber_mono_of_hom f.toHom) (chromaticNumber_mono_of_hom f.symm.toHom)

end SimpleGraph
