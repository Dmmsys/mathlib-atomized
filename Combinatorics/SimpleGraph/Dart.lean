/-
Copyright (c) 2020 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Fintype.Sigma

/-!
# Darts in graphs

A `Dart` or half-edge or bond in a graph is an ordered pair of adjacent vertices, regarded as an
oriented edge. This file defines darts and proves some of their basic properties.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/--
Definition of `Dart` / `Dart` 的定义

English:
structure Dart
  parameters: extends V × V
  extends: V × V
  axioms and operations (1):
    - adj : G.Adj fst snd

中文:
结构 Dart
  参数: extends V × V
  继承: V × V
  公理与运算 (1 个):
    - adj : G.Adj fst snd
-/
structure Dart extends V × V where
  adj : G.Adj fst snd
  deriving DecidableEq

initialize_simps_projections Dart (+toProd, -fst, -snd)

attribute [simp] Dart.adj

variable {G}

/--
theorem `Dart.ext_iff` / 定理 `Dart.ext_iff`

English:
theorem Dart.ext_iff
  given: (d₁ d₂ : G.Dart)
  statement: d₁ = d₂ ↔ d₁.toProd = d₂.toProd
  proof: by
  cases d₁; cases d₂; simp

@[ext]

中文:
定理 Dart.ext_iff
  条件: (d₁ d₂ : G.Dart)
  结论: d₁ = d₂ ↔ d₁.toProd = d₂.toProd
  证明: by
  cases d₁; cases d₂; simp

@[ext]
-/
theorem Dart.ext_iff (d₁ d₂ : G.Dart) : d₁ = d₂ ↔ d₁.toProd = d₂.toProd := by
  cases d₁; cases d₂; simp

@[ext]
/--
theorem `Dart.ext` / 定理 `Dart.ext`

English:
theorem Dart.ext
  given: (d₁ d₂ : G.Dart) (h : d₁.toProd = d₂.toProd)
  statement: d₁ = d₂
  proof: (Dart.ext_iff d₁ d₂).mpr h

@[simp]

中文:
定理 Dart.ext
  条件: (d₁ d₂ : G.Dart) (h : d₁.toProd = d₂.toProd)
  结论: d₁ = d₂
  证明: (Dart.ext_iff d₁ d₂).mpr h

@[simp]

Depends on / 依赖: Dart.ext_iff, ext_iff
-/
theorem Dart.ext (d₁ d₂ : G.Dart) (h : d₁.toProd = d₂.toProd) : d₁ = d₂ :=
  (Dart.ext_iff d₁ d₂).mpr h

@[simp]
/--
theorem `Dart.fst_ne_snd` / 定理 `Dart.fst_ne_snd`

English:
theorem Dart.fst_ne_snd
  given: (d : G.Dart)
  statement: d.fst != d.snd
  proof: fun h => G.irrefl (h ▸ d.adj)

@[simp]

中文:
定理 Dart.fst_ne_snd
  条件: (d : G.Dart)
  结论: d.fst != d.snd
  证明: fun h => G.irrefl (h ▸ d.adj)

@[simp]

Depends on / 依赖: G.irrefl, d.adj, irrefl
-/
theorem Dart.fst_ne_snd (d : G.Dart) : d.fst != d.snd :=
  fun h => G.irrefl (h ▸ d.adj)

@[simp]
/--
theorem `Dart.snd_ne_fst` / 定理 `Dart.snd_ne_fst`

English:
theorem Dart.snd_ne_fst
  given: (d : G.Dart)
  statement: d.snd != d.fst
  proof: fun h => G.irrefl (h ▸ d.adj)

中文:
定理 Dart.snd_ne_fst
  条件: (d : G.Dart)
  结论: d.snd != d.fst
  证明: fun h => G.irrefl (h ▸ d.adj)

Depends on / 依赖: G.irrefl, d.adj, irrefl
-/
theorem Dart.snd_ne_fst (d : G.Dart) : d.snd != d.fst :=
  fun h => G.irrefl (h ▸ d.adj)

/--
theorem `Dart.toProd_injective` / 定理 `Dart.toProd_injective`

English:
theorem Dart.toProd_injective
  statement: Function.Injective (Dart.toProd : G.Dart -> V × V)
  proof: Dart.ext

中文:
定理 Dart.toProd_injective
  结论: Function.Injective (Dart.toProd : G.Dart -> V × V)
  证明: Dart.ext

Depends on / 依赖: Dart.ext
-/
theorem Dart.toProd_injective : Function.Injective (Dart.toProd : G.Dart -> V × V) :=
  Dart.ext

/--
Instance `Dart.fintype` / 实例 `Dart.fintype`

English:
instance Dart.fintype
  signature: [Fintype V] [DecidableRel G.Adj]
  body: Fintype.ofEquiv (Σ v, G.neighborSet v)
    { toFun := fun s => ⟨(s.fst, s.snd), s.snd.property⟩
      invFun := fun d => ⟨d.fst, d.snd, d.adj⟩ }

中文:
实例 Dart.fintype
  签名: [Fintype V] [DecidableRel G.Adj]
  定义体: Fintype.ofEquiv (Σ v, G.neighborSet v)
    { toFun := fun s => ⟨(s.fst, s.snd), s.snd.property⟩
      invFun := fun d => ⟨d.fst, d.snd, d.adj⟩ }

Depends on / 依赖: Fintype, Fintype.ofEquiv, G.neighborSet, d.adj, d.fst, d.snd, invFun, neighborSet, ofEquiv, property, s.fst, s.snd, s.snd.property
-/
instance Dart.fintype [Fintype V] [DecidableRel G.Adj] : Fintype G.Dart :=
  Fintype.ofEquiv (Σ v, G.neighborSet v)
    { toFun := fun s => ⟨(s.fst, s.snd), s.snd.property⟩
      invFun := fun d => ⟨d.fst, d.snd, d.adj⟩ }

/--
Definition of `Dart.edge` / `Dart.edge` 的定义

English:
definition Dart.edge
  signature: (d : G.Dart)
  body: s(d.fst, d.snd)

@[simp]

中文:
定义 Dart.edge
  签名: (d : G.Dart)
  定义体: s(d.fst, d.snd)

@[simp]

Depends on / 依赖: d.fst, d.snd
-/
def Dart.edge (d : G.Dart) : Sym2 V := s(d.fst, d.snd)

@[simp]
/--
theorem `Dart.edge_mk` / 定理 `Dart.edge_mk`

English:
theorem Dart.edge_mk
  given: {p : V × V} (h : G.Adj p.1 p.2)
  statement: (Dart.mk p h).edge = s(p.1, p.2)
  proof: rfl

@[simp]

中文:
定理 Dart.edge_mk
  条件: {p : V × V} (h : G.Adj p.1 p.2)
  结论: (Dart.mk p h).edge = s(p.1, p.2)
  证明: rfl

@[simp]
-/
theorem Dart.edge_mk {p : V × V} (h : G.Adj p.1 p.2) : (Dart.mk p h).edge = s(p.1, p.2) :=
  rfl

@[simp]
/--
theorem `Dart.edge_mem` / 定理 `Dart.edge_mem`

English:
theorem Dart.edge_mem
  given: (d : G.Dart)
  statement: d.edge in G.edgeSet
  proof: d.adj

中文:
定理 Dart.edge_mem
  条件: (d : G.Dart)
  结论: d.edge in G.edgeSet
  证明: d.adj

Depends on / 依赖: d.adj
-/
theorem Dart.edge_mem (d : G.Dart) : d.edge in G.edgeSet :=
  d.adj

/-- The dart with reversed orientation from a given dart. -/
@[simps]
/--
Definition of `Dart.symm` / `Dart.symm` 的定义

English:
definition Dart.symm
  signature: (d : G.Dart)
  body: ⟨d.toProd.swap, d.adj.symm⟩

@[simp]

中文:
定义 Dart.symm
  签名: (d : G.Dart)
  定义体: ⟨d.toProd.swap, d.adj.symm⟩

@[simp]

Depends on / 依赖: d.adj.symm, d.toProd.swap, toProd
-/
def Dart.symm (d : G.Dart) : G.Dart :=
  ⟨d.toProd.swap, d.adj.symm⟩

@[simp]
/--
theorem `Dart.symm_mk` / 定理 `Dart.symm_mk`

English:
theorem Dart.symm_mk
  given: {p : V × V} (h : G.Adj p.1 p.2)
  statement: (Dart.mk p h).symm = Dart.mk p.swap h.symm
  proof: rfl

@[simp]

中文:
定理 Dart.symm_mk
  条件: {p : V × V} (h : G.Adj p.1 p.2)
  结论: (Dart.mk p h).symm = Dart.mk p.swap h.symm
  证明: rfl

@[simp]
-/
theorem Dart.symm_mk {p : V × V} (h : G.Adj p.1 p.2) : (Dart.mk p h).symm = Dart.mk p.swap h.symm :=
  rfl

@[simp]
/--
theorem `Dart.edge_symm` / 定理 `Dart.edge_symm`

English:
theorem Dart.edge_symm
  given: (d : G.Dart)
  statement: d.symm.edge = d.edge
  proof: Sym2.eq_swap

@[simp]

中文:
定理 Dart.edge_symm
  条件: (d : G.Dart)
  结论: d.symm.edge = d.edge
  证明: Sym2.eq_swap

@[simp]

Depends on / 依赖: Sym2.eq_swap, eq_swap
-/
theorem Dart.edge_symm (d : G.Dart) : d.symm.edge = d.edge :=
  Sym2.eq_swap

@[simp]
/--
theorem `Dart.edge_comp_symm` / 定理 `Dart.edge_comp_symm`

English:
theorem Dart.edge_comp_symm
  statement: Dart.edge ∘ Dart.symm = (Dart.edge : G.Dart -> Sym2 V)
  proof: funext Dart.edge_symm

@[simp]

中文:
定理 Dart.edge_comp_symm
  结论: Dart.edge ∘ Dart.symm = (Dart.edge : G.Dart -> Sym2 V)
  证明: funext Dart.edge_symm

@[simp]

Depends on / 依赖: Dart.edge_symm, edge_symm
-/
theorem Dart.edge_comp_symm : Dart.edge ∘ Dart.symm = (Dart.edge : G.Dart -> Sym2 V) :=
  funext Dart.edge_symm

@[simp]
/--
theorem `Dart.symm_symm` / 定理 `Dart.symm_symm`

English:
theorem Dart.symm_symm
  given: (d : G.Dart)
  statement: d.symm.symm = d
  proof: Dart.ext _ _ Prod.swap_swap _

@[simp]

中文:
定理 Dart.symm_symm
  条件: (d : G.Dart)
  结论: d.symm.symm = d
  证明: Dart.ext _ _ Prod.swap_swap _

@[simp]

Depends on / 依赖: Dart.ext, Prod.swap_swap, swap_swap
-/
theorem Dart.symm_symm (d : G.Dart) : d.symm.symm = d :=
Dart.ext _ _ Prod.swap_swap _

@[simp]
/--
theorem `Dart.symm_involutive` / 定理 `Dart.symm_involutive`

English:
theorem Dart.symm_involutive
  statement: Function.Involutive (Dart.symm : G.Dart -> G.Dart)
  proof: Dart.symm_symm

中文:
定理 Dart.symm_involutive
  结论: Function.Involutive (Dart.symm : G.Dart -> G.Dart)
  证明: Dart.symm_symm

Depends on / 依赖: Dart.symm_symm, symm_symm
-/
theorem Dart.symm_involutive : Function.Involutive (Dart.symm : G.Dart -> G.Dart) :=
  Dart.symm_symm

/--
theorem `Dart.symm_ne` / 定理 `Dart.symm_ne`

English:
theorem Dart.symm_ne
  given: (d : G.Dart)
  statement: d.symm != d
  proof: ne_of_apply_ne (Prod.snd ∘ Dart.toProd) d.adj.ne

中文:
定理 Dart.symm_ne
  条件: (d : G.Dart)
  结论: d.symm != d
  证明: ne_of_apply_ne (Prod.snd ∘ Dart.toProd) d.adj.ne

Depends on / 依赖: Dart.toProd, Prod.snd, d.adj.ne, ne_of_apply_ne, toProd
-/
theorem Dart.symm_ne (d : G.Dart) : d.symm != d :=
  ne_of_apply_ne (Prod.snd ∘ Dart.toProd) d.adj.ne

set_option backward.isDefEq.respectTransparency false in
/--
theorem `dart_edge_eq_iff` / 定理 `dart_edge_eq_iff`

English:
theorem dart_edge_eq_iff
  statement: forall d₁ d₂ : G.Dart, d₁.edge = d₂.edge ↔ d₁ = d₂ ∨ d₁ = d₂.symm
  proof: by
  rintro ⟨p, hp⟩ ⟨q, hq⟩
  simp

中文:
定理 dart_edge_eq_iff
  结论: 对任意 d₁ d₂ : G.Dart, d₁.edge = d₂.edge ↔ d₁ = d₂ ∨ d₁ = d₂.symm
  证明: by
  rintro ⟨p, hp⟩ ⟨q, hq⟩
  simp
-/
theorem dart_edge_eq_iff : forall d₁ d₂ : G.Dart, d₁.edge = d₂.edge ↔ d₁ = d₂ ∨ d₁ = d₂.symm := by
  rintro ⟨p, hp⟩ ⟨q, hq⟩
  simp

/--
theorem `dart_edge_eq_mk'_iff` / 定理 `dart_edge_eq_mk'_iff`

English:
theorem dart_edge_eq_mk'_iff
  proof: by
  rintro ⟨p, h⟩ _ _
  simp

中文:
定理 dart_edge_eq_mk'_iff
  证明: by
  rintro ⟨p, h⟩ _ _
  simp
-/
theorem dart_edge_eq_mk'_iff :
    forall {d : G.Dart} {u v : V}, d.edge = s(u, v) ↔ d.toProd = (u, v) ∨ d.toProd = (v, u) := by
  rintro ⟨p, h⟩ _ _
  simp

/--
theorem `dart_edge_eq_mk'_iff'` / 定理 `dart_edge_eq_mk'_iff'`

English:
theorem dart_edge_eq_mk'_iff'
  proof: by
  rintro ⟨⟨a, b⟩, h⟩ u v
  rw [dart_edge_eq_mk'_iff]
  simp

中文:
定理 dart_edge_eq_mk'_iff'
  证明: by
  rintro ⟨⟨a, b⟩, h⟩ u v
  rw [dart_edge_eq_mk'_iff]
  simp
-/
theorem dart_edge_eq_mk'_iff' :
    forall {d : G.Dart} {u v : V},
      d.edge = s(u, v) ↔ d.fst = u ∧ d.snd = v ∨ d.fst = v ∧ d.snd = u := by
  rintro ⟨⟨a, b⟩, h⟩ u v
  rw [dart_edge_eq_mk'_iff]
  simp

variable (G)

/--
Definition of `DartAdj` / `DartAdj` 的定义

English:
definition DartAdj
  signature: (d d' : G.Dart)
  body: d.snd = d'.fst

中文:
定义 DartAdj
  签名: (d d' : G.Dart)
  定义体: d.snd = d'.fst

Depends on / 依赖: d.snd
-/
def DartAdj (d d' : G.Dart) : Prop :=
  d.snd = d'.fst

/-- For a given vertex `v`, this is the bijective map from the neighbor set at `v`
to the darts `d` with `d.fst = v`. -/
@[simps]
/--
Definition of `dartOfNeighborSet` / `dartOfNeighborSet` 的定义

English:
definition dartOfNeighborSet
  signature: (v : V) (w : G.neighborSet v)
  body: ⟨(v, w), w.property⟩

中文:
定义 dartOfNeighborSet
  签名: (v : V) (w : G.neighborSet v)
  定义体: ⟨(v, w), w.property⟩

Depends on / 依赖: property, w.property
-/
def dartOfNeighborSet (v : V) (w : G.neighborSet v) : G.Dart :=
  ⟨(v, w), w.property⟩

/--
theorem `dartOfNeighborSet_injective` / 定理 `dartOfNeighborSet_injective`

English:
theorem dartOfNeighborSet_injective
  given: (v : V)
  statement: Function.Injective (G.dartOfNeighborSet v)
  proof: fun e₁ e₂ h =>
Subtype.ext by
    injection h with h'
    convert! congr_arg Prod.snd h'

中文:
定理 dartOfNeighborSet_injective
  条件: (v : V)
  结论: Function.Injective (G.dartOfNeighborSet v)
  证明: fun e₁ e₂ h =>
Subtype.ext by
    injection h with h'
    convert! congr_arg Prod.snd h'

Depends on / 依赖: Prod.snd, Subtype, Subtype.ext, congr_arg, convert, injection
-/
theorem dartOfNeighborSet_injective (v : V) : Function.Injective (G.dartOfNeighborSet v) :=
  fun e₁ e₂ h =>
Subtype.ext by
    injection h with h'
    convert! congr_arg Prod.snd h'

/--
Instance `nonempty_dart_top` / 实例 `nonempty_dart_top`

English:
instance nonempty_dart_top
  signature: [Nontrivial V]
  body: by
  obtain ⟨v, w, h⟩ := exists_pair_ne V
  exact ⟨⟨(v, w), h⟩⟩

中文:
实例 nonempty_dart_top
  签名: [Nontrivial V]
  定义体: by
  obtain ⟨v, w, h⟩ := exists_pair_ne V
  exact ⟨⟨(v, w), h⟩⟩

Depends on / 依赖: exists_pair_ne
-/
instance nonempty_dart_top [Nontrivial V] : Nonempty (⊤ : SimpleGraph V).Dart := by
  obtain ⟨v, w, h⟩ := exists_pair_ne V
  exact ⟨⟨(v, w), h⟩⟩

end SimpleGraph
