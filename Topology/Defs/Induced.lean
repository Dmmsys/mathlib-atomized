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
/-
**TopologicalSpace.induced** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalSpace`。
形式化陈述：induced (f : X -> Y) (t : TopologicalSpace Y) : TopologicalSpace X where I
sOpen s
参数：f : X -> Y；t : TopologicalSpace Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `f : X → Y` and a topology on `Y`,
  the induced topology on `X` is the collection of sets
  that are preimages of some open set in `Y`.
  This is the coarsest topology that makes `f` continuous.
-/
def induced (f : X → Y) (t : TopologicalSpace Y) : TopologicalSpace X where
  IsOpen s := ∃ t, IsOpen t ∧ f ⁻¹' t = s
  isOpen_univ := ⟨univ, isOpen_univ, preimage_univ⟩
  isOpen_inter := by
    rintro s₁ s₂ ⟨s'₁, hs₁, rfl⟩ ⟨s'₂, hs₂, rfl⟩
    exact ⟨s'₁ ∩ s'₂, hs₁.inter hs₂, preimage_inter⟩
  isOpen_sUnion S h := by
    choose! g hgo hfg using h
    refine ⟨⋃₀ (g '' S), isOpen_sUnion <| forall_mem_image.2 hgo, ?_⟩
    rw [preimage_sUnion, biUnion_image, sUnion_eq_biUnion]
    exact iUnion₂_congr hfg
/-
**TopologicalSpace._root_.instTopologicalSpaceSubtype** 是 Mathlib 中的一个实例，位于命名空间 
`TopologicalSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.instTopologicalSpaceSubtype {p : X → Prop} [t : TopologicalSpace X] :
    TopologicalSpace (Subtype p) :=
  induced (↑) t

/-- Given `f : X → Y` and a topology on `X`,
  the coinduced topology on `Y` is defined such that
  `s : Set Y` is open if the preimage of `s` is open.
  This is the finest topology that makes `f` continuous. -/
@[instance_reducible]
/-
**TopologicalSpace.coinduced** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalSpace`。
形式化陈述：coinduced (f : X -> Y) (t : TopologicalSpace X) : TopologicalSpace Y where
 IsOpen s
参数：f : X -> Y；t : TopologicalSpace X。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.isOpen_univ`：∀ {X : Type u} [self : TopologicalSpace X]
, TopologicalSpace.IsOpen Set.univ

--- 原说明 ---
Given `f : X → Y` and a topology on `X`,
  the coinduced topology on `Y` is defined such that
  `s : Set Y` is open if the preimage of `s` is open.
  This is the finest topology that makes `f` continuous.
-/
def coinduced (f : X → Y) (t : TopologicalSpace X) : TopologicalSpace Y where
  IsOpen s := IsOpen (f ⁻¹' s)
  isOpen_univ := t.isOpen_univ
  isOpen_inter _ _ h₁ h₂ := h₁.inter h₂
  isOpen_sUnion s h := by simpa only [preimage_sUnion] using isOpen_biUnion h

end TopologicalSpace

namespace WithTopology

/-
**WithTopology.instTopologicalSpace** 是 Mathlib 中的一个实例，位于命名空间 `WithTopology`。
形式化陈述：instTopologicalSpace (X : Type*) (t : TopologicalSpace X) : TopologicalSpa
ce (WithTopology X t)
参数：X : Type*；t : TopologicalSpace X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instTopologicalSpace (X : Type*) (t : TopologicalSpace X) :
    TopologicalSpace (WithTopology X t) :=
  .coinduced (WithTopology.toTopology t) t
/-
**WithTopology.topology_eq_coinduced** 是 Mathlib 中的一个引理，位于命名空间 `WithTopology`。
形式化陈述：topology_eq_coinduced (X : Type*) (t : TopologicalSpace X) : instTopologic
alSpace X t = .coinduced (.toTopology t) t
参数：X : Type*；t : TopologicalSpace X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma topology_eq_coinduced (X : Type*) (t : TopologicalSpace X) :
    instTopologicalSpace X t = .coinduced (.toTopology t) t :=
  rfl

/-- `WithTopology.ofTopology` and `WithTopology.toTopology` as an equivalence. -/
@[simps]
/-
**WithTopology.equiv** 是 Mathlib 中的一个定义，位于命名空间 `WithTopology`。
形式化陈述：(X : Type u_1) → (t : TopologicalSpace X) → WithTopology X t ≃ X
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`WithTopology.ofTopology` and `WithTopology.toTopology` as an equivalence.
-/
protected def equiv (X : Type*) (t : TopologicalSpace X) : WithTopology X t ≃ X where
  toFun := WithTopology.ofTopology
  invFun := WithTopology.toTopology t
  left_inv _ := rfl
  right_inv _ := rfl

end WithTopology

namespace Topology
variable {X Y : Type*} [tX : TopologicalSpace X] [tY : TopologicalSpace Y]

/-- We say that restrictions of the topology on `X` to sets from a family `S`
generates the original topology,
if either of the following equivalent conditions hold:

- a set which is relatively open in each `s ∈ S` is open;
- a set which is relatively closed in each `s ∈ S` is closed;
- for any topological space `Y`, a function `f : X → Y` is continuous
  provided that it is continuous on each `s ∈ S`.
-/
/-
**Topology.IsCoherentWith** 是 Mathlib 中的一个归纳类型，位于命名空间 `Topology`。
形式化陈述：{X : Type u_1} → [tX : TopologicalSpace X] → Set (Set X) → Prop
参数：Set X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that restrictions of the topology on `X` to sets from a family `S`
generates the original topology,
if either of the following equivalent conditions hold:

- a set which is relatively open in each `s ∈ S` is open;
- a set which is relatively closed in each `s ∈ S` is closed;
- for any topological space `Y`, a function `f : X → Y` is continuous
  provided that it is continuous on each `s ∈ S`.
-/
structure IsCoherentWith (S : Set (Set X)) : Prop where
  isOpen_of_forall_induced (u : Set X) : (∀ s ∈ S, IsOpen ((↑) ⁻¹' u : Set s)) → IsOpen u

/-- A function `f : X → Y` between topological spaces is inducing if the topology on `X` is induced
by the topology on `Y` through `f`, meaning that a set `s : Set X` is open iff it is the preimage
under `f` of some open set `t : Set Y`. -/
@[fun_prop, mk_iff]
/-
**Topology.IsInducing** 是 Mathlib 中的一个归纳类型，位于命名空间 `Topology`。
形式化陈述：{X : Type u_1} → {Y : Type u_2} → [tX : TopologicalSpace X] → [tY : Topolo
gicalSpace Y] → (X → Y) → Prop
参数：X → Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f : X → Y` between topological spaces is inducing if the topology on
 `X` is induced
by the topology on `Y` through `f`, meaning that a set `s : Set X` is open iff i
t is the preimage
under `f` of some open set `t : Set Y`.
-/
structure IsInducing (f : X → Y) : Prop where
  /-- The topology on the domain is equal to the induced topology. -/
  eq_induced : tX = tY.induced f

/-- A function `f : X → Y` between topological spaces is coinducing if the topology on `Y` is
coinduced by the topology on `X` through `f`, meaning that a set `s : Set Y` is open iff its
preimage is open. -/
@[fun_prop, mk_iff isCoinducing_iff']
/-
**Topology.IsCoinducing** 是 Mathlib 中的一个归纳类型，位于命名空间 `Topology`。
形式化陈述：{X : Type u_1} → {Y : Type u_2} → [tX : TopologicalSpace X] → [tY : Topolo
gicalSpace Y] → (X → Y) → Prop
参数：X → Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f : X → Y` between topological spaces is coinducing if the topology 
on `Y` is
coinduced by the topology on `X` through `f`, meaning that a set `s : Set Y` is 
open iff its
preimage is open.
-/
structure IsCoinducing (f : X → Y) : Prop where
  /-- The topology on the codomain is equal to the coinduced topology. -/
  eq_coinduced : tY = tX.coinduced f

/-- A function between topological spaces is an embedding if it is injective,
  and for all `s : Set X`, `s` is open iff it is the preimage of an open set. -/
@[fun_prop, mk_iff]
/-
**Topology.IsEmbedding** 是 Mathlib 中的一个归纳类型，位于命名空间 `Topology`。
形式化陈述：{X : Type u_1} → {Y : Type u_2} → [tX : TopologicalSpace X] → [tY : Topolo
gicalSpace Y] → (X → Y) → Prop
参数：X → Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function between topological spaces is an embedding if it is injective,
  and for all `s : Set X`, `s` is open iff it is the preimage of an open set.
-/
structure IsEmbedding (f : X → Y) : Prop extends IsInducing f where
  /-- A topological embedding is injective. -/
  injective : Function.Injective f

/-- An open embedding is an embedding with open range. -/
@[fun_prop, mk_iff]
/-
**Topology.IsOpenEmbedding** 是 Mathlib 中的一个归纳类型，位于命名空间 `Topology`。
形式化陈述：{X : Type u_1} → {Y : Type u_2} → [tX : TopologicalSpace X] → [tY : Topolo
gicalSpace Y] → (X → Y) → Prop
参数：X → Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An open embedding is an embedding with open range.
-/
structure IsOpenEmbedding (f : X → Y) : Prop extends IsEmbedding f where
  /-- The range of an open embedding is an open set. -/
  isOpen_range : IsOpen <| range f

/-- A closed embedding is an embedding with closed image. -/
@[fun_prop, mk_iff]
/-
**Topology.IsClosedEmbedding** 是 Mathlib 中的一个归纳类型，位于命名空间 `Topology`。
形式化陈述：{X : Type u_1} → {Y : Type u_2} → [tX : TopologicalSpace X] → [tY : Topolo
gicalSpace Y] → (X → Y) → Prop
参数：X → Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A closed embedding is an embedding with closed image.
-/
structure IsClosedEmbedding (f : X → Y) : Prop extends IsEmbedding f where
  /-- The range of a closed embedding is a closed set. -/
  isClosed_range : IsClosed <| range f

/-- A function between topological spaces is a quotient map if it is surjective,
  and for all `s : Set Y`, `s` is open iff its preimage is an open set. -/
@[fun_prop, mk_iff]
/-
**Topology.IsQuotientMap** 是 Mathlib 中的一个归纳类型，位于命名空间 `Topology`。
形式化陈述：{X : Type u_3} → {Y : Type u_4} → [TopologicalSpace X] → [TopologicalSpace
 Y] → (X → Y) → Prop
参数：X → Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function between topological spaces is a quotient map if it is surjective,
  and for all `s : Set Y`, `s` is open iff its preimage is an open set.
-/
structure IsQuotientMap {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : Prop extends isCoinducing : IsCoinducing f where
  surjective : Function.Surjective f

end Topology

