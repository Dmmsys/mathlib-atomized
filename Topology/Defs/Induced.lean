/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
module

public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Topology.Basic
/-!
# Induced and coinduced topologies

In this file we define the induced and coinduced topologies,
as well as topology inducing maps, topological embeddings, and quotient maps.

## Main definitions

* `TopologicalSpace.induced`: given `f : X → Y` and a topology on `Y`,
  the induced topology on `X` is the collection of sets
  that are preimages of some open set in `Y`.
  This is the coarsest topology that makes `f` continuous.

* `TopologicalSpace.coinduced`: given `f : X → Y` and a topology on `X`,
  the coinduced topology on `Y` is defined such that
  `s : Set Y` is open if the preimage of `s` is open.
  This is the finest topology that makes `f` continuous.

* `IsInducing`: a map `f : X → Y` is called *inducing*,
  if the topology on the domain is equal to the induced topology.

* `IsCoinducing`: a map `f : X → Y` is called *coinducing*,
  if the topology on the codomain is equal to the coinduced topology.

* `IsEmbedding`: a map `f : X → Y` is an *embedding*,
  if it is a topology inducing map and it is injective.

* `IsOpenEmbedding`: a map `f : X → Y` is an *open embedding*,
  if it is an embedding and its range is open.
  An open embedding is an open map.

* `IsClosedEmbedding`: a map `f : X → Y` is an *open embedding*,
  if it is an embedding and its range is open.
  An open embedding is an open map.

* `IsQuotientMap`: a map `f : X → Y` is a *quotient map*,
  if it is surjective
  and the topology on the codomain is equal to the coinduced topology.
-/

@[expose] public section

open Set
open scoped Topology

namespace TopologicalSpace

variable {X Y : Type*}

/-- Given `f : X → Y` and a topology on `Y`,
  the induced topology on `X` is the collection of sets
  that are preimages of some open set in `Y`.
  This is the coarsest topology that makes `f` continuous. -/
@[instance_reducible]
/--
Definition of `induced` / `induced` 的定义

English:
definition induced
  signature: (f : X -> Y) (t : TopologicalSpace Y)
  body: exists t, IsOpen t ∧ f ⁻¹' t = s
  isOpen_univ := ⟨univ, isOpen_univ, preimage_univ⟩
  isOpen_inter := by
    rintro s₁ s₂ ⟨s'₁, hs₁, rfl⟩ ⟨s'₂, hs₂, rfl⟩
    exact ⟨s'₁ inter s'₂, hs₁.inter hs₂, preimage_inter⟩
  isOpen_sUnion S h := by
    choose! g hgo hfg using h
refine ⟨⋃₀ (g '' S), isOpen_sUni

中文:
定义 induced
  签名: (f : X -> Y) (t : TopologicalSpace Y)
  定义体: exists t, IsOpen t ∧ f ⁻¹' t = s
  isOpen_univ := ⟨univ, isOpen_univ, preimage_univ⟩
  isOpen_inter := by
    rintro s₁ s₂ ⟨s'₁, hs₁, rfl⟩ ⟨s'₂, hs₂, rfl⟩
    exact ⟨s'₁ inter s'₂, hs₁.inter hs₂, preimage_inter⟩
  isOpen_sUnion S h := by
    choose! g hgo hfg using h
refine ⟨⋃₀ (g '' S), isOpen_sUni

Depends on / 依赖: IsOpen
-/
def induced (f : X -> Y) (t : TopologicalSpace Y) : TopologicalSpace X where
  IsOpen s := exists t, IsOpen t ∧ f ⁻¹' t = s
  isOpen_univ := ⟨univ, isOpen_univ, preimage_univ⟩
  isOpen_inter := by
    rintro s₁ s₂ ⟨s'₁, hs₁, rfl⟩ ⟨s'₂, hs₂, rfl⟩
    exact ⟨s'₁ inter s'₂, hs₁.inter hs₂, preimage_inter⟩
  isOpen_sUnion S h := by
    choose! g hgo hfg using h
refine ⟨⋃₀ (g '' S), isOpen_sUnion forall_mem_image.2 hgo, ?_⟩
    rw [preimage_sUnion]; rw [biUnion_image]; rw [sUnion_eq_biUnion]
    exact iUnion₂_congr hfg

/--
Instance `_root_.instTopologicalSpaceSubtype` / 实例 `_root_.instTopologicalSpaceSubtype`

English:
instance _root_.instTopologicalSpaceSubtype
  signature: {p : X -> Prop} [t : TopologicalSpace X]
  body: induced (↑) t

中文:
实例 _root_.instTopologicalSpaceSubtype
  签名: {p : X -> 命题} [t : TopologicalSpace X]
  定义体: induced (↑) t

Depends on / 依赖: induced
-/
instance _root_.instTopologicalSpaceSubtype {p : X -> Prop} [t : TopologicalSpace X] :
    TopologicalSpace (Subtype p) :=
  induced (↑) t

/-- Given `f : X → Y` and a topology on `X`,
  the coinduced topology on `Y` is defined such that
  `s : Set Y` is open if the preimage of `s` is open.
  This is the finest topology that makes `f` continuous. -/
@[instance_reducible]
/--
Definition of `coinduced` / `coinduced` 的定义

English:
definition coinduced
  signature: (f : X -> Y) (t : TopologicalSpace X)
  body: IsOpen (f ⁻¹' s)
  isOpen_univ := t.isOpen_univ
  isOpen_inter _ _ h₁ h₂ := h₁.inter h₂
  isOpen_sUnion s h := by simpa only [preimage_sUnion] using isOpen_biUnion h

中文:
定义 coinduced
  签名: (f : X -> Y) (t : TopologicalSpace X)
  定义体: IsOpen (f ⁻¹' s)
  isOpen_univ := t.isOpen_univ
  isOpen_inter _ _ h₁ h₂ := h₁.inter h₂
  isOpen_sUnion s h := by simpa only [preimage_sUnion] using isOpen_biUnion h

Depends on / 依赖: IsOpen
-/
def coinduced (f : X -> Y) (t : TopologicalSpace X) : TopologicalSpace Y where
  IsOpen s := IsOpen (f ⁻¹' s)
  isOpen_univ := t.isOpen_univ
  isOpen_inter _ _ h₁ h₂ := h₁.inter h₂
  isOpen_sUnion s h := by simpa only [preimage_sUnion] using isOpen_biUnion h

end TopologicalSpace

namespace WithTopology

/--
Instance `instTopologicalSpace` / 实例 `instTopologicalSpace`

English:
instance instTopologicalSpace
  signature: (X : Type*) (t : TopologicalSpace X)
  body: .coinduced (WithTopology.toTopology t) t

中文:
实例 instTopologicalSpace
  签名: (X : 类型) (t : TopologicalSpace X)
  定义体: .coinduced (WithTopology.toTopology t) t

Depends on / 依赖: WithTopology, WithTopology.toTopology, coinduced, toTopology
-/
instance instTopologicalSpace (X : Type*) (t : TopologicalSpace X) :
    TopologicalSpace (WithTopology X t) :=
  .coinduced (WithTopology.toTopology t) t

/--
lemma `topology_eq_coinduced` / 引理 `topology_eq_coinduced`

English:
lemma topology_eq_coinduced
  given: (X : Type*) (t : TopologicalSpace X)
  proof: rfl

中文:
引理 topology_eq_coinduced
  条件: (X : 类型) (t : TopologicalSpace X)
  证明: rfl
-/
lemma topology_eq_coinduced (X : Type*) (t : TopologicalSpace X) :
    instTopologicalSpace X t = .coinduced (.toTopology t) t :=
  rfl

/-- `WithTopology.ofTopology` and `WithTopology.toTopology` as an equivalence. -/
@[simps]
/--
Definition of `equiv` / `equiv` 的定义

English:
definition equiv
  signature: (X : Type*) (t : TopologicalSpace X)
  body: WithTopology.ofTopology
  invFun := WithTopology.toTopology t
  left_inv _ := rfl
  right_inv _ := rfl

中文:
定义 equiv
  签名: (X : 类型) (t : TopologicalSpace X)
  定义体: WithTopology.ofTopology
  invFun := WithTopology.toTopology t
  left_inv _ := rfl
  right_inv _ := rfl
-/
protected def equiv (X : Type*) (t : TopologicalSpace X) : WithTopology X t ≃ X where
  toFun := WithTopology.ofTopology
  invFun := WithTopology.toTopology t
  left_inv _ := rfl
  right_inv _ := rfl

end WithTopology

namespace Topology
variable {X Y : Type*} [tX : TopologicalSpace X] [tY : TopologicalSpace Y]

/--
Definition of `IsCoherentWith` / `IsCoherentWith` 的定义

English:
structure IsCoherentWith
  parameters: (S : Set (Set X))
  axioms and operations (1):
    - isOpen_of_forall_induced((u : Set X)) : (forall s in S, IsOpen ((↑) ⁻¹' u : Set s)) -> IsOpen u

中文:
结构 IsCoherentWith
  参数: (S : Set (Set X))
  公理与运算 (1 个):
    - isOpen_of_forall_induced((u : Set X)) : (对任意 s in S, IsOpen ((↑) ⁻¹' u : Set s)) -> IsOpen u
-/
structure IsCoherentWith (S : Set (Set X)) : Prop where
  isOpen_of_forall_induced (u : Set X) : (forall s in S, IsOpen ((↑) ⁻¹' u : Set s)) -> IsOpen u

/-- A function `f : X → Y` between topological spaces is inducing if the topology on `X` is induced
by the topology on `Y` through `f`, meaning that a set `s : Set X` is open iff it is the preimage
under `f` of some open set `t : Set Y`. -/
@[fun_prop, mk_iff]
/--
Definition of `IsInducing` / `IsInducing` 的定义

English:
structure IsInducing
  parameters: (f : X -> Y)
  axioms and operations (1):
    - eq_induced : tX = tY.induced f

中文:
结构 IsInducing
  参数: (f : X -> Y)
  公理与运算 (1 个):
    - eq_induced : tX = tY.induced f
-/
structure IsInducing (f : X -> Y) : Prop where
  /-- The topology on the domain is equal to the induced topology. -/
  eq_induced : tX = tY.induced f

/-- A function `f : X → Y` between topological spaces is coinducing if the topology on `Y` is
coinduced by the topology on `X` through `f`, meaning that a set `s : Set Y` is open iff its
preimage is open. -/
@[fun_prop, mk_iff isCoinducing_iff']
/--
Definition of `IsCoinducing` / `IsCoinducing` 的定义

English:
structure IsCoinducing
  parameters: (f : X -> Y)
  axioms and operations (1):
    - eq_coinduced : tY = tX.coinduced f

中文:
结构 IsCoinducing
  参数: (f : X -> Y)
  公理与运算 (1 个):
    - eq_coinduced : tY = tX.coinduced f
-/
structure IsCoinducing (f : X -> Y) : Prop where
  /-- The topology on the codomain is equal to the coinduced topology. -/
  eq_coinduced : tY = tX.coinduced f

/-- A function between topological spaces is an embedding if it is injective,
  and for all `s : Set X`, `s` is open iff it is the preimage of an open set. -/
@[fun_prop, mk_iff]
/--
Definition of `IsEmbedding` / `IsEmbedding` 的定义

English:
structure IsEmbedding
  parameters: (f : X -> Y)
  extends: IsInducing f
  axioms and operations (1):
    - injective : Function.Injective f

中文:
结构 IsEmbedding
  参数: (f : X -> Y)
  继承: IsInducing f
  公理与运算 (1 个):
    - injective : Function.Injective f
-/
structure IsEmbedding (f : X -> Y) : Prop extends IsInducing f where
  /-- A topological embedding is injective. -/
  injective : Function.Injective f

/-- An open embedding is an embedding with open range. -/
@[fun_prop, mk_iff]
/--
Definition of `IsOpenEmbedding` / `IsOpenEmbedding` 的定义

English:
structure IsOpenEmbedding
  parameters: (f : X -> Y)
  extends: IsEmbedding f
  axioms and operations (1):
    - isOpen_range : IsOpen range f

中文:
结构 IsOpenEmbedding
  参数: (f : X -> Y)
  继承: IsEmbedding f
  公理与运算 (1 个):
    - isOpen_range : IsOpen range f
-/
structure IsOpenEmbedding (f : X -> Y) : Prop extends IsEmbedding f where
  /-- The range of an open embedding is an open set. -/
isOpen_range : IsOpen range f

/-- A closed embedding is an embedding with closed image. -/
@[fun_prop, mk_iff]
/--
Definition of `IsClosedEmbedding` / `IsClosedEmbedding` 的定义

English:
structure IsClosedEmbedding
  parameters: (f : X -> Y)
  extends: IsEmbedding f
  axioms and operations (1):
    - isClosed_range : IsClosed range f

中文:
结构 IsClosedEmbedding
  参数: (f : X -> Y)
  继承: IsEmbedding f
  公理与运算 (1 个):
    - isClosed_range : IsClosed range f
-/
structure IsClosedEmbedding (f : X -> Y) : Prop extends IsEmbedding f where
  /-- The range of a closed embedding is a closed set. -/
isClosed_range : IsClosed range f

/-- A function between topological spaces is a quotient map if it is surjective,
  and for all `s : Set Y`, `s` is open iff its preimage is an open set. -/
@[fun_prop, mk_iff]
/--
Definition of `IsQuotientMap` / `IsQuotientMap` 的定义

English:
structure IsQuotientMap
  parameters: {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  extends: isCoinducing : IsCoinducing f
  axioms and operations (1):
    - surjective : Function.Surjective f

中文:
结构 IsQuotientMap
  参数: {X : 类型} {Y : 类型} [TopologicalSpace X] [TopologicalSpace Y]
  继承: isCoinducing : IsCoinducing f
  公理与运算 (1 个):
    - surjective : Function.Surjective f
-/
structure IsQuotientMap {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X -> Y) : Prop extends isCoinducing : IsCoinducing f where
  surjective : Function.Surjective f

end Topology
