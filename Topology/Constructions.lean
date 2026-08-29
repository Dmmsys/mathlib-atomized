/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
module

public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finset.Piecewise
public import Mathlib.Data.SetLike.Basic
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Curry
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.NhdsSet
import Mathlib.Topology.WithTopology

/-!
# Constructions of new topological spaces from old ones

This file constructs pi types, subtypes and quotients of topological spaces
and sets up their basic theory, such as criteria for maps into or out of these
constructions to be continuous; descriptions of the open sets, neighborhood filters,
and generators of these constructions; and their behavior with respect to embeddings
and other specific classes of maps.

## Implementation note

The constructed topologies are defined using induced and coinduced topologies
along with the complete lattice structure on topologies. Their universal properties
(for example, a map `X → Y × Z` is continuous if and only if both projections
`X → Y`, `X → Z` are) follow easily using order-theoretic descriptions of
continuity. With more work we can also extract descriptions of the open sets,
neighborhood filters and so on.

## Tags

product, subspace, quotient space

-/

@[expose] public section

noncomputable section

open Topology TopologicalSpace Set Filter Function
open scoped Set.Notation

universe u v u' v'

variable {X : Type u} {Y : Type v} {Z W ε ζ : Type*}

section Constructions

instance {r : X -> X -> Prop} [t : TopologicalSpace X] : TopologicalSpace (Quot r) :=
  coinduced (Quot.mk r) t

/--
Instance `instTopologicalSpaceQuotient` / 实例 `instTopologicalSpaceQuotient`

English:
instance instTopologicalSpaceQuotient
  signature: {s : Setoid X} [t : TopologicalSpace X]
  body: coinduced Quotient.mk' t

中文:
实例 instTopologicalSpaceQuotient
  签名: {s : Setoid X} [t : TopologicalSpace X]
  定义体: coinduced Quotient.mk' t

Depends on / 依赖: Quotient, Quotient.mk, coinduced
-/
instance instTopologicalSpaceQuotient {s : Setoid X} [t : TopologicalSpace X] :
    TopologicalSpace (Quotient s) :=
  coinduced Quotient.mk' t

/--
Instance `instTopologicalSpaceSigma` / 实例 `instTopologicalSpaceSigma`

English:
instance instTopologicalSpaceSigma
  signature: {ι : Type*} {X : ι -> Type v} [t₂ : forall i, TopologicalSpace (X i)]
  body: ⨆ i, coinduced (Sigma.mk i) (t₂ i)

中文:
实例 instTopologicalSpaceSigma
  签名: {ι : 类型} {X : ι -> 类型v} [t₂ : 对任意 i, TopologicalSpace (X i)]
  定义体: ⨆ i, coinduced (Sigma.mk i) (t₂ i)

Depends on / 依赖: Sigma.mk, coinduced
-/
instance instTopologicalSpaceSigma {ι : Type*} {X : ι -> Type v} [t₂ : forall i, TopologicalSpace (X i)] :
    TopologicalSpace (Sigma X) :=
  ⨆ i, coinduced (Sigma.mk i) (t₂ i)

/--
Instance `Pi.topologicalSpace` / 实例 `Pi.topologicalSpace`

English:
instance Pi.topologicalSpace
  signature: {ι : Type*} {Y : ι -> Type v} [t₂ : (i : ι) -> TopologicalSpace (Y i)]
  body: ⨅ i, induced (fun f => f i) (t₂ i)

中文:
实例 Pi.topologicalSpace
  签名: {ι : 类型} {Y : ι -> 类型v} [t₂ : (i : ι) -> TopologicalSpace (Y i)]
  定义体: ⨅ i, induced (fun f => f i) (t₂ i)

Depends on / 依赖: induced
-/
instance Pi.topologicalSpace {ι : Type*} {Y : ι -> Type v} [t₂ : (i : ι) -> TopologicalSpace (Y i)] :
    TopologicalSpace ((i : ι) -> Y i) :=
  ⨅ i, induced (fun f => f i) (t₂ i)

/--
Instance `ULift.topologicalSpace` / 实例 `ULift.topologicalSpace`

English:
instance ULift.topologicalSpace
  signature: [t : TopologicalSpace X]
  body: t.induced ULift.down

中文:
实例 ULift.topologicalSpace
  签名: [t : TopologicalSpace X]
  定义体: t.induced ULift.down

Depends on / 依赖: ULift.down, induced, t.induced
-/
instance ULift.topologicalSpace [t : TopologicalSpace X] : TopologicalSpace (ULift.{v, u} X) :=
  t.induced ULift.down

/-!
### `Additive`, `Multiplicative`

The topology on those type synonyms is inherited without change.
-/

section

variable [TopologicalSpace X]

open Additive Multiplicative

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: TopologicalSpace (Additive X)
  body: ‹TopologicalSpace X›

中文:
实例 :
  签名: TopologicalSpace (Additive X)
  定义体: ‹TopologicalSpace X›

Depends on / 依赖: TopologicalSpace
-/
instance : TopologicalSpace (Additive X) := ‹TopologicalSpace X›
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: TopologicalSpace (Multiplicative X)
  body: ‹TopologicalSpace X›

中文:
实例 :
  签名: TopologicalSpace (Multiplicative X)
  定义体: ‹TopologicalSpace X›

Depends on / 依赖: TopologicalSpace
-/
instance : TopologicalSpace (Multiplicative X) := ‹TopologicalSpace X›

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DiscreteTopology
  signature: X] : DiscreteTopology (Additive X)
  body: ‹DiscreteTopology X›

中文:
实例 [DiscreteTopology
  签名: X] : DiscreteTopology (Additive X)
  定义体: ‹DiscreteTopology X›

Depends on / 依赖: DiscreteTopology
-/
instance [DiscreteTopology X] : DiscreteTopology (Additive X) := ‹DiscreteTopology X›
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DiscreteTopology
  signature: X] : DiscreteTopology (Multiplicative X)
  body: ‹DiscreteTopology X›

中文:
实例 [DiscreteTopology
  签名: X] : DiscreteTopology (Multiplicative X)
  定义体: ‹DiscreteTopology X›

Depends on / 依赖: DiscreteTopology
-/
instance [DiscreteTopology X] : DiscreteTopology (Multiplicative X) := ‹DiscreteTopology X›

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CompactSpace
  signature: X] : CompactSpace (Additive X)
  body: ‹CompactSpace X›

中文:
实例 [CompactSpace
  签名: X] : CompactSpace (Additive X)
  定义体: ‹CompactSpace X›

Depends on / 依赖: CompactSpace
-/
instance [CompactSpace X] : CompactSpace (Additive X) := ‹CompactSpace X›
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CompactSpace
  signature: X] : CompactSpace (Multiplicative X)
  body: ‹CompactSpace X›

中文:
实例 [CompactSpace
  签名: X] : CompactSpace (Multiplicative X)
  定义体: ‹CompactSpace X›

Depends on / 依赖: CompactSpace
-/
instance [CompactSpace X] : CompactSpace (Multiplicative X) := ‹CompactSpace X›

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NoncompactSpace
  signature: X] : NoncompactSpace (Additive X)
  body: ‹NoncompactSpace X›

中文:
实例 [NoncompactSpace
  签名: X] : NoncompactSpace (Additive X)
  定义体: ‹NoncompactSpace X›

Depends on / 依赖: NoncompactSpace
-/
instance [NoncompactSpace X] : NoncompactSpace (Additive X) := ‹NoncompactSpace X›
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NoncompactSpace
  signature: X] : NoncompactSpace (Multiplicative X)
  body: ‹NoncompactSpace X›

中文:
实例 [NoncompactSpace
  签名: X] : NoncompactSpace (Multiplicative X)
  定义体: ‹NoncompactSpace X›

Depends on / 依赖: NoncompactSpace
-/
instance [NoncompactSpace X] : NoncompactSpace (Multiplicative X) := ‹NoncompactSpace X›

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [WeaklyLocallyCompactSpace
  signature: X] : WeaklyLocallyCompactSpace (Additive X)
  body: ‹WeaklyLocallyCompactSpace X›

中文:
实例 [WeaklyLocallyCompactSpace
  签名: X] : WeaklyLocallyCompactSpace (Additive X)
  定义体: ‹WeaklyLocallyCompactSpace X›

Depends on / 依赖: WeaklyLocallyCompactSpace
-/
instance [WeaklyLocallyCompactSpace X] : WeaklyLocallyCompactSpace (Additive X) :=
  ‹WeaklyLocallyCompactSpace X›
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [WeaklyLocallyCompactSpace
  signature: X] : WeaklyLocallyCompactSpace (Multiplicative X)
  body: ‹WeaklyLocallyCompactSpace X›

中文:
实例 [WeaklyLocallyCompactSpace
  签名: X] : WeaklyLocallyCompactSpace (Multiplicative X)
  定义体: ‹WeaklyLocallyCompactSpace X›

Depends on / 依赖: WeaklyLocallyCompactSpace
-/
instance [WeaklyLocallyCompactSpace X] : WeaklyLocallyCompactSpace (Multiplicative X) :=
  ‹WeaklyLocallyCompactSpace X›

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LocallyCompactSpace
  signature: X] : LocallyCompactSpace (Additive X)
  body: ‹LocallyCompactSpace X›

中文:
实例 [LocallyCompactSpace
  签名: X] : LocallyCompactSpace (Additive X)
  定义体: ‹LocallyCompactSpace X›

Depends on / 依赖: LocallyCompactSpace
-/
instance [LocallyCompactSpace X] : LocallyCompactSpace (Additive X) := ‹LocallyCompactSpace X›
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LocallyCompactSpace
  signature: X] : LocallyCompactSpace (Multiplicative X)
  body: ‹LocallyCompactSpace X›

中文:
实例 [LocallyCompactSpace
  签名: X] : LocallyCompactSpace (Multiplicative X)
  定义体: ‹LocallyCompactSpace X›

Depends on / 依赖: LocallyCompactSpace
-/
instance [LocallyCompactSpace X] : LocallyCompactSpace (Multiplicative X) := ‹LocallyCompactSpace X›

/--
theorem `continuous_ofMul` / 定理 `continuous_ofMul`

English:
theorem continuous_ofMul
  statement: Continuous (ofMul : X -> Additive X)
  proof: continuous_id

中文:
定理 continuous_ofMul
  结论: Continuous (ofMul : X -> Additive X)
  证明: continuous_id

Depends on / 依赖: continuous_id
-/
theorem continuous_ofMul : Continuous (ofMul : X -> Additive X) := continuous_id

/--
theorem `continuous_toMul` / 定理 `continuous_toMul`

English:
theorem continuous_toMul
  statement: Continuous (toMul : Additive X -> X)
  proof: continuous_id

中文:
定理 continuous_toMul
  结论: Continuous (toMul : Additive X -> X)
  证明: continuous_id

Depends on / 依赖: continuous_id
-/
theorem continuous_toMul : Continuous (toMul : Additive X -> X) := continuous_id

/--
theorem `continuous_ofAdd` / 定理 `continuous_ofAdd`

English:
theorem continuous_ofAdd
  statement: Continuous (ofAdd : X -> Multiplicative X)
  proof: continuous_id

中文:
定理 continuous_ofAdd
  结论: Continuous (ofAdd : X -> Multiplicative X)
  证明: continuous_id

Depends on / 依赖: continuous_id
-/
theorem continuous_ofAdd : Continuous (ofAdd : X -> Multiplicative X) := continuous_id

/--
theorem `continuous_toAdd` / 定理 `continuous_toAdd`

English:
theorem continuous_toAdd
  statement: Continuous (toAdd : Multiplicative X -> X)
  proof: continuous_id

中文:
定理 continuous_toAdd
  结论: Continuous (toAdd : Multiplicative X -> X)
  证明: continuous_id

Depends on / 依赖: continuous_id
-/
theorem continuous_toAdd : Continuous (toAdd : Multiplicative X -> X) := continuous_id

/--
theorem `isOpenMap_ofMul` / 定理 `isOpenMap_ofMul`

English:
theorem isOpenMap_ofMul
  statement: IsOpenMap (ofMul : X -> Additive X)
  proof: IsOpenMap.id

中文:
定理 isOpenMap_ofMul
  结论: IsOpenMap (ofMul : X -> Additive X)
  证明: IsOpenMap.id

Depends on / 依赖: IsOpenMap, IsOpenMap.id
-/
theorem isOpenMap_ofMul : IsOpenMap (ofMul : X -> Additive X) := IsOpenMap.id

/--
theorem `isOpenMap_toMul` / 定理 `isOpenMap_toMul`

English:
theorem isOpenMap_toMul
  statement: IsOpenMap (toMul : Additive X -> X)
  proof: IsOpenMap.id

中文:
定理 isOpenMap_toMul
  结论: IsOpenMap (toMul : Additive X -> X)
  证明: IsOpenMap.id

Depends on / 依赖: IsOpenMap, IsOpenMap.id
-/
theorem isOpenMap_toMul : IsOpenMap (toMul : Additive X -> X) := IsOpenMap.id

/--
theorem `isOpenMap_ofAdd` / 定理 `isOpenMap_ofAdd`

English:
theorem isOpenMap_ofAdd
  statement: IsOpenMap (ofAdd : X -> Multiplicative X)
  proof: IsOpenMap.id

中文:
定理 isOpenMap_ofAdd
  结论: IsOpenMap (ofAdd : X -> Multiplicative X)
  证明: IsOpenMap.id

Depends on / 依赖: IsOpenMap, IsOpenMap.id
-/
theorem isOpenMap_ofAdd : IsOpenMap (ofAdd : X -> Multiplicative X) := IsOpenMap.id

/--
theorem `isOpenMap_toAdd` / 定理 `isOpenMap_toAdd`

English:
theorem isOpenMap_toAdd
  statement: IsOpenMap (toAdd : Multiplicative X -> X)
  proof: IsOpenMap.id

中文:
定理 isOpenMap_toAdd
  结论: IsOpenMap (toAdd : Multiplicative X -> X)
  证明: IsOpenMap.id

Depends on / 依赖: IsOpenMap, IsOpenMap.id
-/
theorem isOpenMap_toAdd : IsOpenMap (toAdd : Multiplicative X -> X) := IsOpenMap.id

/--
theorem `isClosedMap_ofMul` / 定理 `isClosedMap_ofMul`

English:
theorem isClosedMap_ofMul
  statement: IsClosedMap (ofMul : X -> Additive X)
  proof: IsClosedMap.id

中文:
定理 isClosedMap_ofMul
  结论: IsClosedMap (ofMul : X -> Additive X)
  证明: IsClosedMap.id

Depends on / 依赖: IsClosedMap, IsClosedMap.id
-/
theorem isClosedMap_ofMul : IsClosedMap (ofMul : X -> Additive X) := IsClosedMap.id

/--
theorem `isClosedMap_toMul` / 定理 `isClosedMap_toMul`

English:
theorem isClosedMap_toMul
  statement: IsClosedMap (toMul : Additive X -> X)
  proof: IsClosedMap.id

中文:
定理 isClosedMap_toMul
  结论: IsClosedMap (toMul : Additive X -> X)
  证明: IsClosedMap.id

Depends on / 依赖: IsClosedMap, IsClosedMap.id
-/
theorem isClosedMap_toMul : IsClosedMap (toMul : Additive X -> X) := IsClosedMap.id

/--
theorem `isClosedMap_ofAdd` / 定理 `isClosedMap_ofAdd`

English:
theorem isClosedMap_ofAdd
  statement: IsClosedMap (ofAdd : X -> Multiplicative X)
  proof: IsClosedMap.id

中文:
定理 isClosedMap_ofAdd
  结论: IsClosedMap (ofAdd : X -> Multiplicative X)
  证明: IsClosedMap.id

Depends on / 依赖: IsClosedMap, IsClosedMap.id
-/
theorem isClosedMap_ofAdd : IsClosedMap (ofAdd : X -> Multiplicative X) := IsClosedMap.id

/--
theorem `isClosedMap_toAdd` / 定理 `isClosedMap_toAdd`

English:
theorem isClosedMap_toAdd
  statement: IsClosedMap (toAdd : Multiplicative X -> X)
  proof: IsClosedMap.id

中文:
定理 isClosedMap_toAdd
  结论: IsClosedMap (toAdd : Multiplicative X -> X)
  证明: IsClosedMap.id

Depends on / 依赖: IsClosedMap, IsClosedMap.id
-/
theorem isClosedMap_toAdd : IsClosedMap (toAdd : Multiplicative X -> X) := IsClosedMap.id

/--
theorem `nhds_ofMul` / 定理 `nhds_ofMul`

English:
theorem nhds_ofMul
  given: (x : X)
  statement: 𝓝 (ofMul x) = map ofMul (𝓝 x)
  proof: rfl

中文:
定理 nhds_ofMul
  条件: (x : X)
  结论: 𝓝 (ofMul x) = map ofMul (𝓝 x)
  证明: rfl
-/
theorem nhds_ofMul (x : X) : 𝓝 (ofMul x) = map ofMul (𝓝 x) := rfl

/--
theorem `nhds_ofAdd` / 定理 `nhds_ofAdd`

English:
theorem nhds_ofAdd
  given: (x : X)
  statement: 𝓝 (ofAdd x) = map ofAdd (𝓝 x)
  proof: rfl

中文:
定理 nhds_ofAdd
  条件: (x : X)
  结论: 𝓝 (ofAdd x) = map ofAdd (𝓝 x)
  证明: rfl
-/
theorem nhds_ofAdd (x : X) : 𝓝 (ofAdd x) = map ofAdd (𝓝 x) := rfl

/--
theorem `nhds_toMul` / 定理 `nhds_toMul`

English:
theorem nhds_toMul
  given: (x : Additive X)
  statement: 𝓝 x.toMul = map toMul (𝓝 x)
  proof: rfl

中文:
定理 nhds_toMul
  条件: (x : Additive X)
  结论: 𝓝 x.toMul = map toMul (𝓝 x)
  证明: rfl
-/
theorem nhds_toMul (x : Additive X) : 𝓝 x.toMul = map toMul (𝓝 x) := rfl

/--
theorem `nhds_toAdd` / 定理 `nhds_toAdd`

English:
theorem nhds_toAdd
  given: (x : Multiplicative X)
  statement: 𝓝 x.toAdd = map toAdd (𝓝 x)
  proof: rfl

中文:
定理 nhds_toAdd
  条件: (x : Multiplicative X)
  结论: 𝓝 x.toAdd = map toAdd (𝓝 x)
  证明: rfl
-/
theorem nhds_toAdd (x : Multiplicative X) : 𝓝 x.toAdd = map toAdd (𝓝 x) := rfl

end

/-!
### Order dual

The topology on this type synonym is inherited without change.
-/


section

variable [TopologicalSpace X]

open OrderDual

/--
Instance `OrderDual.instTopologicalSpace` / 实例 `OrderDual.instTopologicalSpace`

English:
instance OrderDual.instTopologicalSpace
  signature: : TopologicalSpace Xᵒᵈ
  body: ‹_›

中文:
实例 OrderDual.instTopologicalSpace
  签名: : TopologicalSpace Xᵒᵈ
  定义体: ‹_›
-/
instance OrderDual.instTopologicalSpace : TopologicalSpace Xᵒᵈ := ‹_›
/--
Instance `OrderDual.instDiscreteTopology` / 实例 `OrderDual.instDiscreteTopology`

English:
instance OrderDual.instDiscreteTopology
  signature: [DiscreteTopology X]
  body: ‹_›

中文:
实例 OrderDual.instDiscreteTopology
  签名: [DiscreteTopology X]
  定义体: ‹_›
-/
instance OrderDual.instDiscreteTopology [DiscreteTopology X] : DiscreteTopology Xᵒᵈ := ‹_›

/--
theorem `continuous_toDual` / 定理 `continuous_toDual`

English:
theorem continuous_toDual
  statement: Continuous (toDual : X -> Xᵒᵈ)
  proof: continuous_id

中文:
定理 continuous_toDual
  结论: Continuous (toDual : X -> Xᵒᵈ)
  证明: continuous_id

Depends on / 依赖: continuous_id
-/
theorem continuous_toDual : Continuous (toDual : X -> Xᵒᵈ) := continuous_id

/--
theorem `continuous_ofDual` / 定理 `continuous_ofDual`

English:
theorem continuous_ofDual
  statement: Continuous (ofDual : Xᵒᵈ -> X)
  proof: continuous_id

中文:
定理 continuous_ofDual
  结论: Continuous (ofDual : Xᵒᵈ -> X)
  证明: continuous_id

Depends on / 依赖: continuous_id
-/
theorem continuous_ofDual : Continuous (ofDual : Xᵒᵈ -> X) := continuous_id

/--
theorem `isOpenMap_toDual` / 定理 `isOpenMap_toDual`

English:
theorem isOpenMap_toDual
  statement: IsOpenMap (toDual : X -> Xᵒᵈ)
  proof: IsOpenMap.id

中文:
定理 isOpenMap_toDual
  结论: IsOpenMap (toDual : X -> Xᵒᵈ)
  证明: IsOpenMap.id

Depends on / 依赖: IsOpenMap, IsOpenMap.id
-/
theorem isOpenMap_toDual : IsOpenMap (toDual : X -> Xᵒᵈ) := IsOpenMap.id

/--
theorem `isOpenMap_ofDual` / 定理 `isOpenMap_ofDual`

English:
theorem isOpenMap_ofDual
  statement: IsOpenMap (ofDual : Xᵒᵈ -> X)
  proof: IsOpenMap.id

中文:
定理 isOpenMap_ofDual
  结论: IsOpenMap (ofDual : Xᵒᵈ -> X)
  证明: IsOpenMap.id

Depends on / 依赖: IsOpenMap, IsOpenMap.id
-/
theorem isOpenMap_ofDual : IsOpenMap (ofDual : Xᵒᵈ -> X) := IsOpenMap.id

/--
theorem `isClosedMap_toDual` / 定理 `isClosedMap_toDual`

English:
theorem isClosedMap_toDual
  statement: IsClosedMap (toDual : X -> Xᵒᵈ)
  proof: IsClosedMap.id

中文:
定理 isClosedMap_toDual
  结论: IsClosedMap (toDual : X -> Xᵒᵈ)
  证明: IsClosedMap.id

Depends on / 依赖: IsClosedMap, IsClosedMap.id
-/
theorem isClosedMap_toDual : IsClosedMap (toDual : X -> Xᵒᵈ) := IsClosedMap.id

/--
theorem `isClosedMap_ofDual` / 定理 `isClosedMap_ofDual`

English:
theorem isClosedMap_ofDual
  statement: IsClosedMap (ofDual : Xᵒᵈ -> X)
  proof: IsClosedMap.id

中文:
定理 isClosedMap_ofDual
  结论: IsClosedMap (ofDual : Xᵒᵈ -> X)
  证明: IsClosedMap.id

Depends on / 依赖: IsClosedMap, IsClosedMap.id
-/
theorem isClosedMap_ofDual : IsClosedMap (ofDual : Xᵒᵈ -> X) := IsClosedMap.id

/--
theorem `nhds_toDual` / 定理 `nhds_toDual`

English:
theorem nhds_toDual
  given: (x : X)
  statement: 𝓝 (toDual x) = map toDual (𝓝 x)
  proof: rfl

中文:
定理 nhds_toDual
  条件: (x : X)
  结论: 𝓝 (toDual x) = map toDual (𝓝 x)
  证明: rfl
-/
theorem nhds_toDual (x : X) : 𝓝 (toDual x) = map toDual (𝓝 x) := rfl

/--
theorem `nhds_ofDual` / 定理 `nhds_ofDual`

English:
theorem nhds_ofDual
  given: (x : X)
  statement: 𝓝 (ofDual x) = map ofDual (𝓝 x)
  proof: rfl

中文:
定理 nhds_ofDual
  条件: (x : X)
  结论: 𝓝 (ofDual x) = map ofDual (𝓝 x)
  证明: rfl
-/
theorem nhds_ofDual (x : X) : 𝓝 (ofDual x) = map ofDual (𝓝 x) := rfl

variable [Preorder X] {x : X}

/--
Instance `OrderDual.instNeBotNhdsWithinIoi` / 实例 `OrderDual.instNeBotNhdsWithinIoi`

English:
instance OrderDual.instNeBotNhdsWithinIoi
  signature: [(𝓝[<] x).NeBot]
  body: ‹_›

中文:
实例 OrderDual.instNeBotNhdsWithinIoi
  签名: [(𝓝[<] x).NeBot]
  定义体: ‹_›
-/
instance OrderDual.instNeBotNhdsWithinIoi [(𝓝[<] x).NeBot] : (𝓝[>] toDual x).NeBot := ‹_›
/--
Instance `OrderDual.instNeBotNhdsWithinIio` / 实例 `OrderDual.instNeBotNhdsWithinIio`

English:
instance OrderDual.instNeBotNhdsWithinIio
  signature: [(𝓝[>] x).NeBot]
  body: ‹_›

中文:
实例 OrderDual.instNeBotNhdsWithinIio
  签名: [(𝓝[>] x).NeBot]
  定义体: ‹_›
-/
instance OrderDual.instNeBotNhdsWithinIio [(𝓝[>] x).NeBot] : (𝓝[<] toDual x).NeBot := ‹_›

end

/--
theorem `Quotient.preimage_mem_nhds` / 定理 `Quotient.preimage_mem_nhds`

English:
theorem Quotient.preimage_mem_nhds
  statement: [TopologicalSpace X] [s : Setoid X] {V : Set <| Quotient s}
  proof: preimage_nhds_coinduced hs

中文:
定理 Quotient.preimage_mem_nhds
  结论: [TopologicalSpace X] [s : Setoid X] {V : Set <| Quotient s}
  证明: preimage_nhds_coinduced hs

Depends on / 依赖: preimage_nhds_coinduced
-/
theorem Quotient.preimage_mem_nhds [TopologicalSpace X] [s : Setoid X] {V : Set <| Quotient s}
    {x : X} (hs : V in 𝓝 (Quotient.mk' x)) : Quotient.mk' ⁻¹' V in 𝓝 x :=
  preimage_nhds_coinduced hs

/--
theorem `Dense.quotient` / 定理 `Dense.quotient`

English:
theorem Dense.quotient
  given: [Setoid X] [TopologicalSpace X] {s : Set X} (H : Dense s)
  proof: Quotient.mk''_surjective.denseRange.dense_image continuous_coinduced_rng H

中文:
定理 Dense.quotient
  条件: [Setoid X] [TopologicalSpace X] {s : Set X} (H : Dense s)
  证明: Quotient.mk''_surjective.denseRange.dense_image continuous_coinduced_rng H

Depends on / 依赖: Quotient, Quotient.mk, _surjective, _surjective.denseRange.dense_image, continuous_coinduced_rng, denseRange, dense_image
-/
theorem Dense.quotient [Setoid X] [TopologicalSpace X] {s : Set X} (H : Dense s) :
    Dense (Quotient.mk' '' s) :=
  Quotient.mk''_surjective.denseRange.dense_image continuous_coinduced_rng H

/--
theorem `DenseRange.quotient` / 定理 `DenseRange.quotient`

English:
theorem DenseRange.quotient
  given: [Setoid X] [TopologicalSpace X] {f : Y -> X} (hf : DenseRange f)
  proof: Quotient.mk''_surjective.denseRange.comp hf continuous_coinduced_rng

中文:
定理 DenseRange.quotient
  条件: [Setoid X] [TopologicalSpace X] {f : Y -> X} (hf : DenseRange f)
  证明: Quotient.mk''_surjective.denseRange.comp hf continuous_coinduced_rng

Depends on / 依赖: Quotient, Quotient.mk, _surjective, _surjective.denseRange.comp, continuous_coinduced_rng, denseRange
-/
theorem DenseRange.quotient [Setoid X] [TopologicalSpace X] {f : Y -> X} (hf : DenseRange f) :
    DenseRange (Quotient.mk' ∘ f) :=
  Quotient.mk''_surjective.denseRange.comp hf continuous_coinduced_rng

/--
theorem `continuous_map_of_le` / 定理 `continuous_map_of_le`

English:
theorem continuous_map_of_le
  statement: {α : Type*} [TopologicalSpace α]
  proof: continuous_coinduced_rng

中文:
定理 continuous_map_of_le
  结论: {α : 类型} [TopologicalSpace α]
  证明: continuous_coinduced_rng

Depends on / 依赖: continuous_coinduced_rng
-/
theorem continuous_map_of_le {α : Type*} [TopologicalSpace α]
    {s t : Setoid α} (h : s <= t) : Continuous (Setoid.map_of_le h) :=
  continuous_coinduced_rng

/--
theorem `continuous_map_sInf` / 定理 `continuous_map_sInf`

English:
theorem continuous_map_sInf
  statement: {α : Type*} [TopologicalSpace α]
  proof: continuous_coinduced_rng

中文:
定理 continuous_map_sInf
  结论: {α : 类型} [TopologicalSpace α]
  证明: continuous_coinduced_rng

Depends on / 依赖: continuous_coinduced_rng
-/
theorem continuous_map_sInf {α : Type*} [TopologicalSpace α]
    {S : Set (Setoid α)} {s : Setoid α} (h : s in S) : Continuous (Setoid.map_sInf h) :=
  continuous_coinduced_rng

instance {p : X -> Prop} [TopologicalSpace X] [DiscreteTopology X] : DiscreteTopology (Subtype p) :=
  ⟨bot_unique fun s _ => ⟨(↑) '' s, isOpen_discrete _, preimage_image_eq _ Subtype.val_injective⟩⟩

/--
Instance `Sum.discreteTopology` / 实例 `Sum.discreteTopology`

English:
instance Sum.discreteTopology
  signature: [TopologicalSpace X] [TopologicalSpace Y] [h : DiscreteTopology X]
  body: ⟨sup_eq_bot_iff.2 by simp [h.eq_bot, hY.eq_bot]⟩

中文:
实例 Sum.discreteTopology
  签名: [TopologicalSpace X] [TopologicalSpace Y] [h : DiscreteTopology X]
  定义体: ⟨sup_eq_bot_iff.2 by simp [h.eq_bot, hY.eq_bot]⟩

Depends on / 依赖: eq_bot, h.eq_bot, hY.eq_bot, sup_eq_bot_iff
-/
instance Sum.discreteTopology [TopologicalSpace X] [TopologicalSpace Y] [h : DiscreteTopology X]
    [hY : DiscreteTopology Y] : DiscreteTopology (X oplus Y) :=
⟨sup_eq_bot_iff.2 by simp [h.eq_bot, hY.eq_bot]⟩

/--
Instance `Sigma.discreteTopology` / 实例 `Sigma.discreteTopology`

English:
instance Sigma.discreteTopology
  signature: {ι : Type*} {Y : ι -> Type v} [forall i, TopologicalSpace (Y i)]
  body: ⟨iSup_eq_bot.2 fun _ => by simp only [(h _).eq_bot, coinduced_bot]⟩

中文:
实例 Sigma.discreteTopology
  签名: {ι : 类型} {Y : ι -> 类型v} [对任意 i, TopologicalSpace (Y i)]
  定义体: ⟨iSup_eq_bot.2 fun _ => by simp only [(h _).eq_bot, coinduced_bot]⟩

Depends on / 依赖: coinduced_bot, eq_bot, iSup_eq_bot
-/
instance Sigma.discreteTopology {ι : Type*} {Y : ι -> Type v} [forall i, TopologicalSpace (Y i)]
    [h : forall i, DiscreteTopology (Y i)] : DiscreteTopology (Sigma Y) :=
  ⟨iSup_eq_bot.2 fun _ => by simp only [(h _).eq_bot, coinduced_bot]⟩

/--
Instance `Prod.indiscreteTopology` / 实例 `Prod.indiscreteTopology`

English:
instance Prod.indiscreteTopology
  signature: [TopologicalSpace X] [TopologicalSpace Y]
  body: ⟨inf_eq_top_iff.2 by simp [h.eq_top, hY.eq_top]⟩

中文:
实例 Prod.indiscreteTopology
  签名: [TopologicalSpace X] [TopologicalSpace Y]
  定义体: ⟨inf_eq_top_iff.2 by simp [h.eq_top, hY.eq_top]⟩

Depends on / 依赖: eq_top, h.eq_top, hY.eq_top, inf_eq_top_iff
-/
instance Prod.indiscreteTopology [TopologicalSpace X] [TopologicalSpace Y]
    [h : IndiscreteTopology X] [hY : IndiscreteTopology Y] : IndiscreteTopology (X × Y) :=
⟨inf_eq_top_iff.2 by simp [h.eq_top, hY.eq_top]⟩

/--
Instance `Pi.indiscreteTopology` / 实例 `Pi.indiscreteTopology`

English:
instance Pi.indiscreteTopology
  signature: {ι : Type*} {Y : ι -> Type v} [forall i, TopologicalSpace (Y i)]
  body: ⟨iInf_eq_top.2 fun _ => by simp only [(h _).eq_top, induced_top]⟩

中文:
实例 Pi.indiscreteTopology
  签名: {ι : 类型} {Y : ι -> 类型v} [对任意 i, TopologicalSpace (Y i)]
  定义体: ⟨iInf_eq_top.2 fun _ => by simp only [(h _).eq_top, induced_top]⟩

Depends on / 依赖: eq_top, iInf_eq_top, induced_top
-/
instance Pi.indiscreteTopology {ι : Type*} {Y : ι -> Type v} [forall i, TopologicalSpace (Y i)]
    [h : forall i, IndiscreteTopology (Y i)] : IndiscreteTopology ((i : ι) -> Y i) :=
  ⟨iInf_eq_top.2 fun _ => by simp only [(h _).eq_top, induced_top]⟩

/--
lemma `comap_nhdsWithin_range` / 引理 `comap_nhdsWithin_range`

English:
lemma comap_nhdsWithin_range
  given: {α β} [TopologicalSpace β] (f : α -> β) (y : β)
  proof: comap_inf_principal_range

中文:
引理 comap_nhdsWithin_range
  条件: {α β} [TopologicalSpace β] (f : α -> β) (y : β)
  证明: comap_inf_principal_range
-/
@[simp] lemma comap_nhdsWithin_range {α β} [TopologicalSpace β] (f : α -> β) (y : β) :
    comap f (𝓝[range f] y) = comap f (𝓝 y) := comap_inf_principal_range

section Top

variable [TopologicalSpace X]

/--
theorem `mem_nhds_subtype` / 定理 `mem_nhds_subtype`

English:
theorem mem_nhds_subtype
  given: (s : Set X) (x : { x // x in s }) (t : Set { x // x in s })
  proof: mem_nhds_induced _ x t

中文:
定理 mem_nhds_subtype
  条件: (s : Set X) (x : { x // x in s }) (t : Set { x // x in s })
  证明: mem_nhds_induced _ x t

Depends on / 依赖: mem_nhds_induced
-/
theorem mem_nhds_subtype (s : Set X) (x : { x // x in s }) (t : Set { x // x in s }) :
    t in 𝓝 x ↔ exists u in 𝓝 (x : X), Subtype.val ⁻¹' u subseteq t :=
  mem_nhds_induced _ x t

/--
theorem `nhds_subtype` / 定理 `nhds_subtype`

English:
theorem nhds_subtype
  given: (s : Set X) (x : { x // x in s })
  statement: 𝓝 x = comap (↑) (𝓝 (x : X))
  proof: nhds_induced _ x

中文:
定理 nhds_subtype
  条件: (s : Set X) (x : { x // x in s })
  结论: 𝓝 x = comap (↑) (𝓝 (x : X))
  证明: nhds_induced _ x

Depends on / 依赖: nhds_induced
-/
theorem nhds_subtype (s : Set X) (x : { x // x in s }) : 𝓝 x = comap (↑) (𝓝 (x : X)) :=
  nhds_induced _ x

/--
lemma `nhds_subtype_eq_comap_nhdsWithin` / 引理 `nhds_subtype_eq_comap_nhdsWithin`

English:
lemma nhds_subtype_eq_comap_nhdsWithin
  given: (s : Set X) (x : { x // x in s })
  proof: by
  rw [nhds_subtype]; rw [← comap_nhdsWithin_range]; rw [Subtype.range_val]

中文:
引理 nhds_subtype_eq_comap_nhdsWithin
  条件: (s : Set X) (x : { x // x in s })
  证明: by
  rw [nhds_subtype]; rw [← comap_nhdsWithin_range]; rw [Subtype.range_val]

Depends on / 依赖: Subtype, Subtype.range_val, comap_nhdsWithin_range, nhds_subtype, range_val
-/
lemma nhds_subtype_eq_comap_nhdsWithin (s : Set X) (x : { x // x in s }) :
    𝓝 x = comap (↑) (𝓝[s] (x : X)) := by
  rw [nhds_subtype]; rw [← comap_nhdsWithin_range]; rw [Subtype.range_val]

/--
theorem `nhdsWithin_subtype_eq_bot_iff` / 定理 `nhdsWithin_subtype_eq_bot_iff`

English:
theorem nhdsWithin_subtype_eq_bot_iff
  given: {s t : Set X} {x : s}
  proof: by
  rw [inf_principal_eq_bot_iff_comap]; rw [nhdsWithin]; rw [nhdsWithin]; rw [comap_inf]; rw [comap_principal]; rw [nhds_induced]

中文:
定理 nhdsWithin_subtype_eq_bot_iff
  条件: {s t : Set X} {x : s}
  证明: by
  rw [inf_principal_eq_bot_iff_comap]; rw [nhdsWithin]; rw [nhdsWithin]; rw [comap_inf]; rw [comap_principal]; rw [nhds_induced]

Depends on / 依赖: comap_inf, comap_principal, inf_principal_eq_bot_iff_comap, nhdsWithin, nhds_induced
-/
theorem nhdsWithin_subtype_eq_bot_iff {s t : Set X} {x : s} :
    𝓝[((↑) : s -> X) ⁻¹' t] x = ⊥ ↔ 𝓝[t] (x : X) ⊓ 𝓟 s = ⊥ := by
  rw [inf_principal_eq_bot_iff_comap]; rw [nhdsWithin]; rw [nhdsWithin]; rw [comap_inf]; rw [comap_principal]; rw [nhds_induced]

/--
theorem `nhds_ne_subtype_eq_bot_iff` / 定理 `nhds_ne_subtype_eq_bot_iff`

English:
theorem nhds_ne_subtype_eq_bot_iff
  given: {S : Set X} {x : S}
  proof: by
  rw [← nhdsWithin_subtype_eq_bot_iff]; rw [preimage_compl]; rw [← image_singleton]; rw [Subtype.coe_injective.preimage_image]

中文:
定理 nhds_ne_subtype_eq_bot_iff
  条件: {S : Set X} {x : S}
  证明: by
  rw [← nhdsWithin_subtype_eq_bot_iff]; rw [preimage_compl]; rw [← image_singleton]; rw [Subtype.coe_injective.preimage_image]

Depends on / 依赖: Subtype, Subtype.coe_injective.preimage_image, coe_injective, image_singleton, nhdsWithin_subtype_eq_bot_iff, preimage_compl, preimage_image
-/
theorem nhds_ne_subtype_eq_bot_iff {S : Set X} {x : S} :
    𝓝[!=] x = ⊥ ↔ 𝓝[!=] (x : X) ⊓ 𝓟 S = ⊥ := by
  rw [← nhdsWithin_subtype_eq_bot_iff]; rw [preimage_compl]; rw [← image_singleton]; rw [Subtype.coe_injective.preimage_image]

/--
theorem `nhds_ne_subtype_neBot_iff` / 定理 `nhds_ne_subtype_neBot_iff`

English:
theorem nhds_ne_subtype_neBot_iff
  given: {S : Set X} {x : S}
  proof: by
  rw [neBot_iff]; rw [neBot_iff]; rw [not_iff_not]; rw [nhds_ne_subtype_eq_bot_iff]

中文:
定理 nhds_ne_subtype_neBot_iff
  条件: {S : Set X} {x : S}
  证明: by
  rw [neBot_iff]; rw [neBot_iff]; rw [not_iff_not]; rw [nhds_ne_subtype_eq_bot_iff]

Depends on / 依赖: neBot_iff, nhds_ne_subtype_eq_bot_iff, not_iff_not
-/
theorem nhds_ne_subtype_neBot_iff {S : Set X} {x : S} :
    (𝓝[!=] x).NeBot ↔ (𝓝[!=] (x : X) ⊓ 𝓟 S).NeBot := by
  rw [neBot_iff]; rw [neBot_iff]; rw [not_iff_not]; rw [nhds_ne_subtype_eq_bot_iff]

end Top

section IsDiscrete

variable {X : Type*} [TopologicalSpace X] {s : Set X}

/--
Definition of `IsDiscrete` / `IsDiscrete` 的定义

English:
structure IsDiscrete
  parameters: (s : Set X)
  axioms and operations (1):
    - to_subtype : DiscreteTopology ↥s

中文:
结构 IsDiscrete
  参数: (s : Set X)
  公理与运算 (1 个):
    - to_subtype : DiscreteTopology ↥s
-/
structure IsDiscrete (s : Set X) : Prop where
  to_subtype : DiscreteTopology ↥s

/--
lemma `isDiscrete_iff_discreteTopology` / 引理 `isDiscrete_iff_discreteTopology`

English:
lemma isDiscrete_iff_discreteTopology
  statement: IsDiscrete s ↔ DiscreteTopology s
  proof: ⟨fun s => s.to_subtype, fun s => ⟨s⟩⟩

中文:
引理 isDiscrete_iff_discreteTopology
  结论: IsDiscrete s ↔ DiscreteTopology s
  证明: ⟨fun s => s.to_subtype, fun s => ⟨s⟩⟩

Depends on / 依赖: s.to_subtype, to_subtype
-/
lemma isDiscrete_iff_discreteTopology : IsDiscrete s ↔ DiscreteTopology s :=
  ⟨fun s => s.to_subtype, fun s => ⟨s⟩⟩

/--
lemma `SetLike.isDiscrete_iff_discreteTopology` / 引理 `SetLike.isDiscrete_iff_discreteTopology`

English:
lemma SetLike.isDiscrete_iff_discreteTopology
  given: {S : Type*} [SetLike S X] {s : S}
  proof: ⟨fun s => s.to_subtype, fun s => ⟨s⟩⟩

中文:
引理 SetLike.isDiscrete_iff_discreteTopology
  条件: {S : 类型} [SetLike S X] {s : S}
  证明: ⟨fun s => s.to_subtype, fun s => ⟨s⟩⟩

Depends on / 依赖: s.to_subtype, to_subtype
-/
lemma SetLike.isDiscrete_iff_discreteTopology {S : Type*} [SetLike S X] {s : S} :
    IsDiscrete (s : Set X) ↔ DiscreteTopology s :=
  ⟨fun s => s.to_subtype, fun s => ⟨s⟩⟩

/--
lemma `DiscreteTopology.isDiscrete` / 引理 `DiscreteTopology.isDiscrete`

English:
lemma DiscreteTopology.isDiscrete
  given: [DiscreteTopology s]
  statement: IsDiscrete s
  proof: ⟨inferInstance⟩

中文:
引理 DiscreteTopology.isDiscrete
  条件: [DiscreteTopology s]
  结论: IsDiscrete s
  证明: ⟨inferInstance⟩
-/
lemma DiscreteTopology.isDiscrete [DiscreteTopology s] : IsDiscrete s := ⟨inferInstance⟩

end IsDiscrete

/-- Cofinite topology. A set is open if it's empty or cofinite. -/
@[implicit_reducible]
/--
Definition of `TopologicalSpace.cofinite` / `TopologicalSpace.cofinite` 的定义

English:
definition TopologicalSpace.cofinite
  signature: {X : Type*}
  body: s.Nonempty -> Set.Finite sᶜ
  isOpen_univ := by simp
  isOpen_inter s t := by
    rintro hs ht ⟨x, hxs, hxt⟩
    rw [compl_inter]
    exact (hs ⟨x, hxs⟩).union (ht ⟨x, hxt⟩)
  isOpen_sUnion := by
    rintro s h ⟨x, t, hts, hzt⟩
    rw [compl_sUnion]
    exact Finite.sInter (mem_image_of_mem _ hts) (

中文:
定义 TopologicalSpace.cofinite
  签名: {X : 类型}
  定义体: s.Nonempty -> Set.Finite sᶜ
  isOpen_univ := by simp
  isOpen_inter s t := by
    rintro hs ht ⟨x, hxs, hxt⟩
    rw [compl_inter]
    exact (hs ⟨x, hxs⟩).union (ht ⟨x, hxt⟩)
  isOpen_sUnion := by
    rintro s h ⟨x, t, hts, hzt⟩
    rw [compl_sUnion]
    exact Finite.sInter (mem_image_of_mem _ hts) (
-/
protected def TopologicalSpace.cofinite {X : Type*} : TopologicalSpace X where
  IsOpen s := s.Nonempty -> Set.Finite sᶜ
  isOpen_univ := by simp
  isOpen_inter s t := by
    rintro hs ht ⟨x, hxs, hxt⟩
    rw [compl_inter]
    exact (hs ⟨x, hxs⟩).union (ht ⟨x, hxt⟩)
  isOpen_sUnion := by
    rintro s h ⟨x, t, hts, hzt⟩
    rw [compl_sUnion]
    exact Finite.sInter (mem_image_of_mem _ hts) (h t hts ⟨x, hzt⟩)

/--
Definition of `CofiniteTopology` / `CofiniteTopology` 的定义

English:
abbreviation CofiniteTopology
  signature: (X : Type*)
  body: WithTopology X .cofinite

中文:
缩写 CofiniteTopology
  签名: (X : 类型)
  定义体: WithTopology X .cofinite

Depends on / 依赖: WithTopology, cofinite
-/
abbrev CofiniteTopology (X : Type*) :=
  WithTopology X .cofinite

namespace CofiniteTopology

/--
Definition of `of` / `of` 的定义

English:
definition of
  signature: : X ≃ CofiniteTopology X
  body: (WithTopology.equiv _ _).symm

中文:
定义 of
  签名: : X ≃ CofiniteTopology X
  定义体: (WithTopology.equiv _ _).symm

Depends on / 依赖: WithTopology, WithTopology.equiv
-/
def of : X ≃ CofiniteTopology X := (WithTopology.equiv _ _).symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: X] : Inhabited (CofiniteTopology X) where default
  body: of default

中文:
实例 [Inhabited
  签名: X] : Inhabited (CofiniteTopology X) where default
  定义体: of default
-/
instance [Inhabited X] : Inhabited (CofiniteTopology X) where default := of default

set_option backward.isDefEq.respectTransparency false in
/--
theorem `isOpen_iff` / 定理 `isOpen_iff`

English:
theorem isOpen_iff
  given: {s : Set (CofiniteTopology X)}
  statement: IsOpen s ↔ s.Nonempty -> sᶜ.Finite
  proof: by
  simp_rw [isOpen_coinduced, TopologicalSpace.cofinite, isOpen_mk, ← Set.preimage_compl,
    WithTopology.preimage_toTopology, image_nonempty,
    finite_image_iff (WithTopology.ofTopology_injective _).injOn]

中文:
定理 isOpen_iff
  条件: {s : Set (CofiniteTopology X)}
  结论: IsOpen s ↔ s.Nonempty -> sᶜ.Finite
  证明: by
  simp_rw [isOpen_coinduced, TopologicalSpace.cofinite, isOpen_mk, ← Set.preimage_compl,
    WithTopology.preimage_toTopology, image_nonempty,
    finite_image_iff (WithTopology.ofTopology_injective _).injOn]

Depends on / 依赖: Set.preimage_compl, TopologicalSpace, TopologicalSpace.cofinite, WithTopology, WithTopology.ofTopology_injective, WithTopology.preimage_toTopology, cofinite, finite_image_iff, image_nonempty, isOpen_coinduced, isOpen_mk, ofTopology_injective, preimage_compl, preimage_toTopology, simp_rw
-/
theorem isOpen_iff {s : Set (CofiniteTopology X)} : IsOpen s ↔ s.Nonempty -> sᶜ.Finite := by
  simp_rw [isOpen_coinduced, TopologicalSpace.cofinite, isOpen_mk, ← Set.preimage_compl,
    WithTopology.preimage_toTopology, image_nonempty,
    finite_image_iff (WithTopology.ofTopology_injective _).injOn]

/--
theorem `isOpen_iff'` / 定理 `isOpen_iff'`

English:
theorem isOpen_iff'
  given: {s : Set (CofiniteTopology X)}
  statement: IsOpen s ↔ s = ∅ ∨ sᶜ.Finite
  proof: by
  simp only [isOpen_iff, nonempty_iff_ne_empty, or_iff_not_imp_left]

中文:
定理 isOpen_iff'
  条件: {s : Set (CofiniteTopology X)}
  结论: IsOpen s ↔ s = ∅ ∨ sᶜ.Finite
  证明: by
  simp only [isOpen_iff, nonempty_iff_ne_empty, or_iff_not_imp_left]

Depends on / 依赖: isOpen_iff, nonempty_iff_ne_empty, or_iff_not_imp_left
-/
theorem isOpen_iff' {s : Set (CofiniteTopology X)} : IsOpen s ↔ s = ∅ ∨ sᶜ.Finite := by
  simp only [isOpen_iff, nonempty_iff_ne_empty, or_iff_not_imp_left]

/--
theorem `isClosed_iff` / 定理 `isClosed_iff`

English:
theorem isClosed_iff
  given: {s : Set (CofiniteTopology X)}
  statement: IsClosed s ↔ s = univ ∨ s.Finite
  proof: by
  simp only [← isOpen_compl_iff, isOpen_iff', compl_compl, compl_empty_iff]

中文:
定理 isClosed_iff
  条件: {s : Set (CofiniteTopology X)}
  结论: IsClosed s ↔ s = univ ∨ s.Finite
  证明: by
  simp only [← isOpen_compl_iff, isOpen_iff', compl_compl, compl_empty_iff]

Depends on / 依赖: compl_compl, compl_empty_iff, isOpen_compl_iff, isOpen_iff
-/
theorem isClosed_iff {s : Set (CofiniteTopology X)} : IsClosed s ↔ s = univ ∨ s.Finite := by
  simp only [← isOpen_compl_iff, isOpen_iff', compl_compl, compl_empty_iff]

/--
theorem `nhds_eq` / 定理 `nhds_eq`

English:
theorem nhds_eq
  given: (x : CofiniteTopology X)
  statement: 𝓝 x = pure x ⊔ cofinite
  proof: by
  ext U
  simp_rw [mem_nhds_iff, isOpen_iff]
  constructor
  · rintro ⟨V, hVU, V_op, haV⟩
    exact mem_sup.mpr ⟨hVU haV, mem_of_superset (V_op ⟨_, haV⟩) hVU⟩
  · rintro ⟨hU : x in U, hU' : Uᶜ.Finite⟩
    exact ⟨U, Subset.rfl, fun _ => hU', hU⟩

中文:
定理 nhds_eq
  条件: (x : CofiniteTopology X)
  结论: 𝓝 x = pure x ⊔ cofinite
  证明: by
  ext U
  simp_rw [mem_nhds_iff, isOpen_iff]
  constructor
  · rintro ⟨V, hVU, V_op, haV⟩
    exact mem_sup.mpr ⟨hVU haV, mem_of_superset (V_op ⟨_, haV⟩) hVU⟩
  · rintro ⟨hU : x in U, hU' : Uᶜ.Finite⟩
    exact ⟨U, Subset.rfl, fun _ => hU', hU⟩

Depends on / 依赖: Finite, Subset, Subset.rfl, V_op, isOpen_iff, mem_nhds_iff, mem_of_superset, mem_sup, mem_sup.mpr, simp_rw
-/
theorem nhds_eq (x : CofiniteTopology X) : 𝓝 x = pure x ⊔ cofinite := by
  ext U
  simp_rw [mem_nhds_iff, isOpen_iff]
  constructor
  · rintro ⟨V, hVU, V_op, haV⟩
    exact mem_sup.mpr ⟨hVU haV, mem_of_superset (V_op ⟨_, haV⟩) hVU⟩
  · rintro ⟨hU : x in U, hU' : Uᶜ.Finite⟩
    exact ⟨U, Subset.rfl, fun _ => hU', hU⟩

/--
theorem `mem_nhds_iff` / 定理 `mem_nhds_iff`

English:
theorem mem_nhds_iff
  given: {x : CofiniteTopology X} {s : Set (CofiniteTopology X)}
  proof: by simp [nhds_eq]

中文:
定理 mem_nhds_iff
  条件: {x : CofiniteTopology X} {s : Set (CofiniteTopology X)}
  证明: by simp [nhds_eq]

Depends on / 依赖: nhds_eq
-/
theorem mem_nhds_iff {x : CofiniteTopology X} {s : Set (CofiniteTopology X)} :
    s in 𝓝 x ↔ x in s ∧ sᶜ.Finite := by simp [nhds_eq]

end CofiniteTopology

end Constructions

section Prod

variable [TopologicalSpace X] [TopologicalSpace Y]

/--
theorem `MapClusterPt.curry_prodMap` / 定理 `MapClusterPt.curry_prodMap`

English:
theorem MapClusterPt.curry_prodMap
  statement: {α β : Type*}
  proof: by
  rw [mapClusterPt_iff_frequently] at hf hg
  rw [((𝓝 x).basis_sets.prod_nhds (𝓝 y).basis_sets).mapClusterPt_iff_frequently]
  rintro ⟨s, t⟩ ⟨hs, ht⟩
  rw [frequently_curry_iff]
  exact (hf s hs).mono fun x hx => (hg t ht).mono fun y hy => ⟨hx, hy⟩

中文:
定理 MapClusterPt.curry_prodMap
  结论: {α β : 类型}
  证明: by
  rw [mapClusterPt_iff_frequently] at hf hg
  rw [((𝓝 x).basis_sets.prod_nhds (𝓝 y).basis_sets).mapClusterPt_iff_frequently]
  rintro ⟨s, t⟩ ⟨hs, ht⟩
  rw [frequently_curry_iff]
  exact (hf s hs).mono fun x hx => (hg t ht).mono fun y hy => ⟨hx, hy⟩

Depends on / 依赖: basis_sets, basis_sets.prod_nhds, frequently_curry_iff, mapClusterPt_iff_frequently, prod_nhds
-/
theorem MapClusterPt.curry_prodMap {α β : Type*}
    {f : α -> X} {g : β -> Y} {la : Filter α} {lb : Filter β} {x : X} {y : Y}
    (hf : MapClusterPt x la f) (hg : MapClusterPt y lb g) :
    MapClusterPt (x, y) (la.curry lb) (.map f g) := by
  rw [mapClusterPt_iff_frequently] at hf hg
  rw [((𝓝 x).basis_sets.prod_nhds (𝓝 y).basis_sets).mapClusterPt_iff_frequently]
  rintro ⟨s, t⟩ ⟨hs, ht⟩
  rw [frequently_curry_iff]
  exact (hf s hs).mono fun x hx => (hg t ht).mono fun y hy => ⟨hx, hy⟩

/--
theorem `MapClusterPt.prodMap` / 定理 `MapClusterPt.prodMap`

English:
theorem MapClusterPt.prodMap
  statement: {α β : Type*}
  proof: (hf.curry_prodMap hg).mono map_mono curry_le_prod

中文:
定理 MapClusterPt.prodMap
  结论: {α β : 类型}
  证明: (hf.curry_prodMap hg).mono map_mono curry_le_prod

Depends on / 依赖: curry_le_prod, curry_prodMap, hf.curry_prodMap, map_mono
-/
theorem MapClusterPt.prodMap {α β : Type*}
    {f : α -> X} {g : β -> Y} {la : Filter α} {lb : Filter β} {x : X} {y : Y}
    (hf : MapClusterPt x la f) (hg : MapClusterPt y lb g) :
    MapClusterPt (x, y) (la ×ˢ lb) (.map f g) :=
(hf.curry_prodMap hg).mono map_mono curry_le_prod

end Prod

section Bool

/--
lemma `continuous_bool_rng` / 引理 `continuous_bool_rng`

English:
lemma continuous_bool_rng
  given: [TopologicalSpace X] {f : X -> Bool} (b : Bool)
  proof: by
  rw [continuous_discrete_rng]; rw [Bool.forall_bool' b]; rw [IsClopen]; rw [← isOpen_compl_iff]; rw [← preimage_compl]; rw [Bool.compl_singleton]; rw [and_comm]

中文:
引理 continuous_bool_rng
  条件: [TopologicalSpace X] {f : X -> 布尔} (b : 布尔)
  证明: by
  rw [continuous_discrete_rng]; rw [Bool.forall_bool' b]; rw [IsClopen]; rw [← isOpen_compl_iff]; rw [← preimage_compl]; rw [Bool.compl_singleton]; rw [and_comm]

Depends on / 依赖: Bool.compl_singleton, Bool.forall_bool, IsClopen, and_comm, compl_singleton, continuous_discrete_rng, forall_bool, isOpen_compl_iff, preimage_compl
-/
lemma continuous_bool_rng [TopologicalSpace X] {f : X -> Bool} (b : Bool) :
    Continuous f ↔ IsClopen (f ⁻¹' {b}) := by
  rw [continuous_discrete_rng]; rw [Bool.forall_bool' b]; rw [IsClopen]; rw [← isOpen_compl_iff]; rw [← preimage_compl]; rw [Bool.compl_singleton]; rw [and_comm]

end Bool

section Subtype

variable [TopologicalSpace X] [TopologicalSpace Y] {p : X -> Prop}

@[fun_prop]
/--
lemma `Topology.IsInducing.subtypeVal` / 引理 `Topology.IsInducing.subtypeVal`

English:
lemma Topology.IsInducing.subtypeVal
  given: {t : Set Y}
  statement: IsInducing ((↑) : t -> Y)
  proof: ⟨rfl⟩

中文:
引理 Topology.IsInducing.subtypeVal
  条件: {t : Set Y}
  结论: IsInducing ((↑) : t -> Y)
  证明: ⟨rfl⟩
-/
lemma Topology.IsInducing.subtypeVal {t : Set Y} : IsInducing ((↑) : t -> Y) := ⟨rfl⟩

/--
lemma `Topology.IsInducing.of_codRestrict` / 引理 `Topology.IsInducing.of_codRestrict`

English:
lemma Topology.IsInducing.of_codRestrict
  statement: {f : X -> Y} {t : Set Y} (ht : forall x, f x in t)
  proof: subtypeVal.comp h

@[fun_prop]

中文:
引理 Topology.IsInducing.of_codRestrict
  结论: {f : X -> Y} {t : Set Y} (ht : 对任意 x, f x in t)
  证明: subtypeVal.comp h

@[fun_prop]

Depends on / 依赖: subtypeVal, subtypeVal.comp
-/
lemma Topology.IsInducing.of_codRestrict {f : X -> Y} {t : Set Y} (ht : forall x, f x in t)
    (h : IsInducing (t.codRestrict f ht)) : IsInducing f := subtypeVal.comp h

@[fun_prop]
/--
lemma `Topology.IsEmbedding.subtypeVal` / 引理 `Topology.IsEmbedding.subtypeVal`

English:
lemma Topology.IsEmbedding.subtypeVal
  statement: IsEmbedding ((↑) : Subtype p -> X)
  proof: ⟨.subtypeVal, Subtype.coe_injective⟩

@[fun_prop]

中文:
引理 Topology.IsEmbedding.subtypeVal
  结论: IsEmbedding ((↑) : Subtype p -> X)
  证明: ⟨.subtypeVal, Subtype.coe_injective⟩

@[fun_prop]

Depends on / 依赖: Subtype, Subtype.coe_injective, coe_injective, subtypeVal
-/
lemma Topology.IsEmbedding.subtypeVal : IsEmbedding ((↑) : Subtype p -> X) :=
  ⟨.subtypeVal, Subtype.coe_injective⟩

@[fun_prop]
/--
theorem `Topology.IsClosedEmbedding.subtypeVal` / 定理 `Topology.IsClosedEmbedding.subtypeVal`

English:
theorem Topology.IsClosedEmbedding.subtypeVal
  given: (h : IsClosed {a | p a})
  proof: ⟨.subtypeVal, by rwa [Subtype.range_coe_subtype]⟩

@[continuity, fun_prop]

中文:
定理 Topology.IsClosedEmbedding.subtypeVal
  条件: (h : IsClosed {a | p a})
  证明: ⟨.subtypeVal, by rwa [Subtype.range_coe_subtype]⟩

@[continuity, fun_prop]

Depends on / 依赖: Subtype, Subtype.range_coe_subtype, range_coe_subtype, subtypeVal
-/
theorem Topology.IsClosedEmbedding.subtypeVal (h : IsClosed {a | p a}) :
    IsClosedEmbedding ((↑) : Subtype p -> X) :=
  ⟨.subtypeVal, by rwa [Subtype.range_coe_subtype]⟩

@[continuity, fun_prop]
/--
theorem `continuous_subtype_val` / 定理 `continuous_subtype_val`

English:
theorem continuous_subtype_val
  statement: Continuous (@Subtype.val X p)
  proof: continuous_induced_dom

中文:
定理 continuous_subtype_val
  结论: Continuous (@Subtype.val X p)
  证明: continuous_induced_dom

Depends on / 依赖: continuous_induced_dom
-/
theorem continuous_subtype_val : Continuous (@Subtype.val X p) :=
  continuous_induced_dom

/--
theorem `Continuous.subtype_val` / 定理 `Continuous.subtype_val`

English:
theorem Continuous.subtype_val
  given: {f : Y -> Subtype p} (hf : Continuous f)
  proof: continuous_subtype_val.comp hf

@[fun_prop]

中文:
定理 Continuous.subtype_val
  条件: {f : Y -> Subtype p} (hf : Continuous f)
  证明: continuous_subtype_val.comp hf

@[fun_prop]

Depends on / 依赖: continuous_subtype_val, continuous_subtype_val.comp
-/
theorem Continuous.subtype_val {f : Y -> Subtype p} (hf : Continuous f) :
    Continuous fun x => (f x : X) :=
  continuous_subtype_val.comp hf

@[fun_prop]
/--
theorem `IsOpen.isOpenEmbedding_subtypeVal` / 定理 `IsOpen.isOpenEmbedding_subtypeVal`

English:
theorem IsOpen.isOpenEmbedding_subtypeVal
  given: {s : Set X} (hs : IsOpen s)
  proof: ⟨.subtypeVal, (@Subtype.range_coe _ s).symm ▸ hs⟩

中文:
定理 IsOpen.isOpenEmbedding_subtypeVal
  条件: {s : Set X} (hs : IsOpen s)
  证明: ⟨.subtypeVal, (@Subtype.range_coe _ s).symm ▸ hs⟩

Depends on / 依赖: Subtype, Subtype.range_coe, range_coe, subtypeVal
-/
theorem IsOpen.isOpenEmbedding_subtypeVal {s : Set X} (hs : IsOpen s) :
    IsOpenEmbedding ((↑) : s -> X) :=
  ⟨.subtypeVal, (@Subtype.range_coe _ s).symm ▸ hs⟩

/--
theorem `IsOpen.isOpenMap_subtype_val` / 定理 `IsOpen.isOpenMap_subtype_val`

English:
theorem IsOpen.isOpenMap_subtype_val
  given: {s : Set X} (hs : IsOpen s)
  statement: IsOpenMap ((↑) : s -> X)
  proof: hs.isOpenEmbedding_subtypeVal.isOpenMap

中文:
定理 IsOpen.isOpenMap_subtype_val
  条件: {s : Set X} (hs : IsOpen s)
  结论: IsOpenMap ((↑) : s -> X)
  证明: hs.isOpenEmbedding_subtypeVal.isOpenMap

Depends on / 依赖: hs.isOpenEmbedding_subtypeVal.isOpenMap, isOpenEmbedding_subtypeVal, isOpenMap
-/
theorem IsOpen.isOpenMap_subtype_val {s : Set X} (hs : IsOpen s) : IsOpenMap ((↑) : s -> X) :=
  hs.isOpenEmbedding_subtypeVal.isOpenMap

/--
theorem `IsOpenMap.domRestrict` / 定理 `IsOpenMap.domRestrict`

English:
theorem IsOpenMap.domRestrict
  given: {f : X -> Y} (hf : IsOpenMap f) {s : Set X} (hs : IsOpen s)
  proof: hf.comp hs.isOpenMap_subtype_val

@[deprecated (since := "2026-07-19")] alias IsOpenMap.restrict := IsOpenMap.domRestrict

@[fun_prop]

中文:
定理 IsOpenMap.domRestrict
  条件: {f : X -> Y} (hf : IsOpenMap f) {s : Set X} (hs : IsOpen s)
  证明: hf.comp hs.isOpenMap_subtype_val

@[deprecated (since := "2026-07-19")] alias IsOpenMap.restrict := IsOpenMap.domRestrict

@[fun_prop]

Depends on / 依赖: hf.comp, hs.isOpenMap_subtype_val, isOpenMap_subtype_val
-/
theorem IsOpenMap.domRestrict {f : X -> Y} (hf : IsOpenMap f) {s : Set X} (hs : IsOpen s) :
    IsOpenMap (s.domRestrict f) :=
  hf.comp hs.isOpenMap_subtype_val

@[deprecated (since := "2026-07-19")] alias IsOpenMap.restrict := IsOpenMap.domRestrict

@[fun_prop]
/--
lemma `IsClosed.isClosedEmbedding_subtypeVal` / 引理 `IsClosed.isClosedEmbedding_subtypeVal`

English:
lemma IsClosed.isClosedEmbedding_subtypeVal
  given: {s : Set X} (hs : IsClosed s)
  proof: .subtypeVal hs

中文:
引理 IsClosed.isClosedEmbedding_subtypeVal
  条件: {s : Set X} (hs : IsClosed s)
  证明: .subtypeVal hs

Depends on / 依赖: subtypeVal
-/
lemma IsClosed.isClosedEmbedding_subtypeVal {s : Set X} (hs : IsClosed s) :
    IsClosedEmbedding ((↑) : s -> X) := .subtypeVal hs

/--
theorem `IsClosed.isClosedMap_subtype_val` / 定理 `IsClosed.isClosedMap_subtype_val`

English:
theorem IsClosed.isClosedMap_subtype_val
  given: {s : Set X} (hs : IsClosed s)
  proof: hs.isClosedEmbedding_subtypeVal.isClosedMap

中文:
定理 IsClosed.isClosedMap_subtype_val
  条件: {s : Set X} (hs : IsClosed s)
  证明: hs.isClosedEmbedding_subtypeVal.isClosedMap

Depends on / 依赖: hs.isClosedEmbedding_subtypeVal.isClosedMap, isClosedEmbedding_subtypeVal, isClosedMap
-/
theorem IsClosed.isClosedMap_subtype_val {s : Set X} (hs : IsClosed s) :
    IsClosedMap ((↑) : s -> X) :=
  hs.isClosedEmbedding_subtypeVal.isClosedMap

/--
theorem `IsClosedMap.domRestrict` / 定理 `IsClosedMap.domRestrict`

English:
theorem IsClosedMap.domRestrict
  statement: {f : X -> Y} (hf : IsClosedMap f) {s : Set X}
  proof: hf.comp hs.isClosedMap_subtype_val

@[deprecated (since := "2026-07-19")] alias IsClosedMap.restrict := IsClosedMap.domRestrict

@[continuity, fun_prop]

中文:
定理 IsClosedMap.domRestrict
  结论: {f : X -> Y} (hf : IsClosedMap f) {s : Set X}
  证明: hf.comp hs.isClosedMap_subtype_val

@[deprecated (since := "2026-07-19")] alias IsClosedMap.restrict := IsClosedMap.domRestrict

@[continuity, fun_prop]

Depends on / 依赖: hf.comp, hs.isClosedMap_subtype_val, isClosedMap_subtype_val
-/
theorem IsClosedMap.domRestrict {f : X -> Y} (hf : IsClosedMap f) {s : Set X}
    (hs : IsClosed s) : IsClosedMap (s.domRestrict f) :=
  hf.comp hs.isClosedMap_subtype_val

@[deprecated (since := "2026-07-19")] alias IsClosedMap.restrict := IsClosedMap.domRestrict

@[continuity, fun_prop]
/--
theorem `Continuous.subtype_mk` / 定理 `Continuous.subtype_mk`

English:
theorem Continuous.subtype_mk
  given: {f : Y -> X} (h : Continuous f) (hp : forall x, p (f x))
  proof: continuous_induced_rng.2 h

中文:
定理 Continuous.subtype_mk
  条件: {f : Y -> X} (h : Continuous f) (hp : 对任意 x, p (f x))
  证明: continuous_induced_rng.2 h

Depends on / 依赖: continuous_induced_rng
-/
theorem Continuous.subtype_mk {f : Y -> X} (h : Continuous f) (hp : forall x, p (f x)) :
    Continuous fun x => (⟨f x, hp x⟩ : Subtype p) :=
  continuous_induced_rng.2 h

/--
theorem `IsOpenMap.subtype_mk` / 定理 `IsOpenMap.subtype_mk`

English:
theorem IsOpenMap.subtype_mk
  given: {f : Y -> X} (hf : IsOpenMap f) (hp : forall x, p (f x))
  proof: fun u hu => by
  convert! (hf u hu).preimage continuous_subtype_val
  exact Set.ext fun _ => exists_congr fun _ => and_congr_right' Subtype.ext_iff

中文:
定理 IsOpenMap.subtype_mk
  条件: {f : Y -> X} (hf : IsOpenMap f) (hp : 对任意 x, p (f x))
  证明: fun u hu => by
  convert! (hf u hu).preimage continuous_subtype_val
  exact Set.ext fun _ => exists_congr fun _ => and_congr_right' Subtype.ext_iff

Depends on / 依赖: Set.ext, Subtype, Subtype.ext_iff, and_congr_right, continuous_subtype_val, convert, exists_congr, ext_iff, preimage
-/
theorem IsOpenMap.subtype_mk {f : Y -> X} (hf : IsOpenMap f) (hp : forall x, p (f x)) :
    IsOpenMap fun x => (⟨f x, hp x⟩ : Subtype p) := fun u hu => by
  convert! (hf u hu).preimage continuous_subtype_val
  exact Set.ext fun _ => exists_congr fun _ => and_congr_right' Subtype.ext_iff

/--
theorem `IsClosedMap.subtype_mk` / 定理 `IsClosedMap.subtype_mk`

English:
theorem IsClosedMap.subtype_mk
  given: {f : Y -> X} (hf : IsClosedMap f) (hp : forall x, p (f x))
  proof: fun u hu => by
  convert! (hf u hu).preimage continuous_subtype_val
  exact Set.ext fun _ => exists_congr fun _ => and_congr_right' Subtype.ext_iff

@[fun_prop]

中文:
定理 IsClosedMap.subtype_mk
  条件: {f : Y -> X} (hf : IsClosedMap f) (hp : 对任意 x, p (f x))
  证明: fun u hu => by
  convert! (hf u hu).preimage continuous_subtype_val
  exact Set.ext fun _ => exists_congr fun _ => and_congr_right' Subtype.ext_iff

@[fun_prop]

Depends on / 依赖: Set.ext, Subtype, Subtype.ext_iff, and_congr_right, continuous_subtype_val, convert, exists_congr, ext_iff, preimage
-/
theorem IsClosedMap.subtype_mk {f : Y -> X} (hf : IsClosedMap f) (hp : forall x, p (f x)) :
    IsClosedMap fun x => (⟨f x, hp x⟩ : Subtype p) := fun u hu => by
  convert! (hf u hu).preimage continuous_subtype_val
  exact Set.ext fun _ => exists_congr fun _ => and_congr_right' Subtype.ext_iff

@[fun_prop]
/--
theorem `Continuous.subtype_coind` / 定理 `Continuous.subtype_coind`

English:
theorem Continuous.subtype_coind
  given: {f : Y -> X} (hf : Continuous f) (hp : forall x, p (f x))
  proof: hf.subtype_mk hp

中文:
定理 Continuous.subtype_coind
  条件: {f : Y -> X} (hf : Continuous f) (hp : 对任意 x, p (f x))
  证明: hf.subtype_mk hp

Depends on / 依赖: hf.subtype_mk, subtype_mk
-/
theorem Continuous.subtype_coind {f : Y -> X} (hf : Continuous f) (hp : forall x, p (f x)) :
    Continuous (Subtype.coind f hp) :=
  hf.subtype_mk hp

/--
theorem `IsOpenMap.subtype_coind` / 定理 `IsOpenMap.subtype_coind`

English:
theorem IsOpenMap.subtype_coind
  given: {f : Y -> X} (hf : IsOpenMap f) (hp : forall x, p (f x))
  proof: hf.subtype_mk hp

中文:
定理 IsOpenMap.subtype_coind
  条件: {f : Y -> X} (hf : IsOpenMap f) (hp : 对任意 x, p (f x))
  证明: hf.subtype_mk hp

Depends on / 依赖: hf.subtype_mk, subtype_mk
-/
theorem IsOpenMap.subtype_coind {f : Y -> X} (hf : IsOpenMap f) (hp : forall x, p (f x)) :
    IsOpenMap (Subtype.coind f hp) :=
  hf.subtype_mk hp

/--
theorem `IsClosedMap.subtype_coind` / 定理 `IsClosedMap.subtype_coind`

English:
theorem IsClosedMap.subtype_coind
  given: {f : Y -> X} (hf : IsClosedMap f) (hp : forall x, p (f x))
  proof: hf.subtype_mk hp

@[fun_prop]

中文:
定理 IsClosedMap.subtype_coind
  条件: {f : Y -> X} (hf : IsClosedMap f) (hp : 对任意 x, p (f x))
  证明: hf.subtype_mk hp

@[fun_prop]

Depends on / 依赖: hf.subtype_mk, subtype_mk
-/
theorem IsClosedMap.subtype_coind {f : Y -> X} (hf : IsClosedMap f) (hp : forall x, p (f x)) :
    IsClosedMap (Subtype.coind f hp) :=
  hf.subtype_mk hp

@[fun_prop]
/--
theorem `Continuous.subtype_map` / 定理 `Continuous.subtype_map`

English:
theorem Continuous.subtype_map
  statement: {f : X -> Y} (h : Continuous f) {q : Y -> Prop}
  proof: (h.comp continuous_subtype_val).subtype_mk _

中文:
定理 Continuous.subtype_map
  结论: {f : X -> Y} (h : Continuous f) {q : Y -> 命题}
  证明: (h.comp continuous_subtype_val).subtype_mk _

Depends on / 依赖: continuous_subtype_val, h.comp, subtype_mk
-/
theorem Continuous.subtype_map {f : X -> Y} (h : Continuous f) {q : Y -> Prop}
    (hpq : forall x, p x -> q (f x)) : Continuous (Subtype.map f hpq) :=
  (h.comp continuous_subtype_val).subtype_mk _

/--
theorem `IsOpenMap.subtype_map` / 定理 `IsOpenMap.subtype_map`

English:
theorem IsOpenMap.subtype_map
  statement: {f : X -> Y} (hf : IsOpenMap f) {s : Set X} {t : Set Y} (hs : IsOpen s)
  proof: (hf.comp hs.isOpenMap_subtype_val).subtype_mk _

中文:
定理 IsOpenMap.subtype_map
  结论: {f : X -> Y} (hf : IsOpenMap f) {s : Set X} {t : Set Y} (hs : IsOpen s)
  证明: (hf.comp hs.isOpenMap_subtype_val).subtype_mk _

Depends on / 依赖: hf.comp, hs.isOpenMap_subtype_val, isOpenMap_subtype_val, subtype_mk
-/
theorem IsOpenMap.subtype_map {f : X -> Y} (hf : IsOpenMap f) {s : Set X} {t : Set Y} (hs : IsOpen s)
    (hst : forall x in s, f x in t) : IsOpenMap (Subtype.map f hst) :=
  (hf.comp hs.isOpenMap_subtype_val).subtype_mk _

/--
theorem `IsClosedMap.subtype_map` / 定理 `IsClosedMap.subtype_map`

English:
theorem IsClosedMap.subtype_map
  statement: {f : X -> Y} (hf : IsClosedMap f) {s : Set X} {t : Set Y}
  proof: (hf.comp hs.isClosedMap_subtype_val).subtype_mk _

中文:
定理 IsClosedMap.subtype_map
  结论: {f : X -> Y} (hf : IsClosedMap f) {s : Set X} {t : Set Y}
  证明: (hf.comp hs.isClosedMap_subtype_val).subtype_mk _

Depends on / 依赖: hf.comp, hs.isClosedMap_subtype_val, isClosedMap_subtype_val, subtype_mk
-/
theorem IsClosedMap.subtype_map {f : X -> Y} (hf : IsClosedMap f) {s : Set X} {t : Set Y}
    (hs : IsClosed s) (hst : forall x in s, f x in t) : IsClosedMap (Subtype.map f hst) :=
  (hf.comp hs.isClosedMap_subtype_val).subtype_mk _

/--
theorem `continuous_inclusion` / 定理 `continuous_inclusion`

English:
theorem continuous_inclusion
  given: {s t : Set X} (h : s subseteq t)
  statement: Continuous (inclusion h)
  proof: continuous_id.subtype_map h

中文:
定理 continuous_inclusion
  条件: {s t : Set X} (h : s subseteq t)
  结论: Continuous (inclusion h)
  证明: continuous_id.subtype_map h

Depends on / 依赖: continuous_id, continuous_id.subtype_map, subtype_map
-/
theorem continuous_inclusion {s t : Set X} (h : s subseteq t) : Continuous (inclusion h) :=
  continuous_id.subtype_map h

/--
theorem `IsOpen.isOpenMap_inclusion` / 定理 `IsOpen.isOpenMap_inclusion`

English:
theorem IsOpen.isOpenMap_inclusion
  given: {s t : Set X} (hs : IsOpen s) (h : s subseteq t)
  proof: IsOpenMap.id.subtype_map hs h

中文:
定理 IsOpen.isOpenMap_inclusion
  条件: {s t : Set X} (hs : IsOpen s) (h : s subseteq t)
  证明: IsOpenMap.id.subtype_map hs h

Depends on / 依赖: IsOpenMap, IsOpenMap.id.subtype_map, subtype_map
-/
theorem IsOpen.isOpenMap_inclusion {s t : Set X} (hs : IsOpen s) (h : s subseteq t) :
    IsOpenMap (inclusion h) :=
  IsOpenMap.id.subtype_map hs h

/--
theorem `IsClosed.isClosedMap_inclusion` / 定理 `IsClosed.isClosedMap_inclusion`

English:
theorem IsClosed.isClosedMap_inclusion
  given: {s t : Set X} (hs : IsClosed s) (h : s subseteq t)
  proof: IsClosedMap.id.subtype_map hs h

@[simp]

中文:
定理 IsClosed.isClosedMap_inclusion
  条件: {s t : Set X} (hs : IsClosed s) (h : s subseteq t)
  证明: IsClosedMap.id.subtype_map hs h

@[simp]

Depends on / 依赖: IsClosedMap, IsClosedMap.id.subtype_map, subtype_map
-/
theorem IsClosed.isClosedMap_inclusion {s t : Set X} (hs : IsClosed s) (h : s subseteq t) :
    IsClosedMap (inclusion h) :=
  IsClosedMap.id.subtype_map hs h

@[simp]
/--
theorem `continuous_rangeFactorization_iff` / 定理 `continuous_rangeFactorization_iff`

English:
theorem continuous_rangeFactorization_iff
  given: {f : X -> Y}
  proof: IsInducing.subtypeVal.continuous_iff

@[continuity, fun_prop]

中文:
定理 continuous_rangeFactorization_iff
  条件: {f : X -> Y}
  证明: IsInducing.subtypeVal.continuous_iff

@[continuity, fun_prop]

Depends on / 依赖: IsInducing, IsInducing.subtypeVal.continuous_iff, continuous_iff, subtypeVal
-/
theorem continuous_rangeFactorization_iff {f : X -> Y} :
    Continuous (rangeFactorization f) ↔ Continuous f :=
  IsInducing.subtypeVal.continuous_iff

@[continuity, fun_prop]
/--
theorem `Continuous.rangeFactorization` / 定理 `Continuous.rangeFactorization`

English:
theorem Continuous.rangeFactorization
  given: {f : X -> Y} (hf : Continuous f)
  proof: continuous_rangeFactorization_iff.mpr hf

中文:
定理 Continuous.rangeFactorization
  条件: {f : X -> Y} (hf : Continuous f)
  证明: continuous_rangeFactorization_iff.mpr hf

Depends on / 依赖: continuous_rangeFactorization_iff, continuous_rangeFactorization_iff.mpr
-/
theorem Continuous.rangeFactorization {f : X -> Y} (hf : Continuous f) :
    Continuous (rangeFactorization f) :=
  continuous_rangeFactorization_iff.mpr hf

/--
theorem `continuousAt_subtype_val` / 定理 `continuousAt_subtype_val`

English:
theorem continuousAt_subtype_val
  given: {p : X -> Prop} {x : Subtype p}
  proof: continuous_subtype_val.continuousAt

中文:
定理 continuousAt_subtype_val
  条件: {p : X -> 命题} {x : Subtype p}
  证明: continuous_subtype_val.continuousAt

Depends on / 依赖: continuousAt, continuous_subtype_val, continuous_subtype_val.continuousAt
-/
theorem continuousAt_subtype_val {p : X -> Prop} {x : Subtype p} :
    ContinuousAt ((↑) : Subtype p -> X) x :=
  continuous_subtype_val.continuousAt

/--
Definition of `Homeomorph.ofEqSubtypes` / `Homeomorph.ofEqSubtypes` 的定义

English:
definition Homeomorph.ofEqSubtypes
  signature: {p q : X -> Prop} (hpq : p = q)
  body: Equiv.subtypeEquivProp hpq
  continuous_toFun := continuous_id.subtype_map (fun x => by simp [hpq])
  continuous_invFun := continuous_id.subtype_map (fun x => by simp [hpq])

@[simp]

中文:
定义 Homeomorph.ofEqSubtypes
  签名: {p q : X -> 命题} (hpq : p = q)
  定义体: Equiv.subtypeEquivProp hpq
  continuous_toFun := continuous_id.subtype_map (fun x => by simp [hpq])
  continuous_invFun := continuous_id.subtype_map (fun x => by simp [hpq])

@[simp]

Depends on / 依赖: Equiv.subtypeEquivProp, subtypeEquivProp
-/
def Homeomorph.ofEqSubtypes {p q : X -> Prop} (hpq : p = q) : Subtype p ≃ₜ Subtype q where
  toEquiv := Equiv.subtypeEquivProp hpq
  continuous_toFun := continuous_id.subtype_map (fun x => by simp [hpq])
  continuous_invFun := continuous_id.subtype_map (fun x => by simp [hpq])

@[simp]
/--
lemma `Homeomorph.ofEqSubtypes_toEquiv` / 引理 `Homeomorph.ofEqSubtypes_toEquiv`

English:
lemma Homeomorph.ofEqSubtypes_toEquiv
  given: {p q : X -> Prop} (hpq : p = q)
  proof: rfl

中文:
引理 Homeomorph.ofEqSubtypes_toEquiv
  条件: {p q : X -> 命题} (hpq : p = q)
  证明: rfl
-/
lemma Homeomorph.ofEqSubtypes_toEquiv {p q : X -> Prop} (hpq : p = q) :
    (Homeomorph.ofEqSubtypes hpq).toEquiv = Equiv.subtypeEquivProp hpq := rfl

/--
theorem `Subtype.dense_iff` / 定理 `Subtype.dense_iff`

English:
theorem Subtype.dense_iff
  given: {s : Set X} {t : Set s}
  statement: Dense t ↔ s subseteq closure ((↑) '' t)
  proof: by
  rw [IsInducing.subtypeVal.dense_iff]; rw [SetCoe.forall]
  rfl

@[simp]

中文:
定理 Subtype.dense_iff
  条件: {s : Set X} {t : Set s}
  结论: Dense t ↔ s subseteq closure ((↑) '' t)
  证明: by
  rw [IsInducing.subtypeVal.dense_iff]; rw [SetCoe.forall]
  rfl

@[simp]

Depends on / 依赖: IsInducing, IsInducing.subtypeVal.dense_iff, SetCoe, SetCoe.forall, dense_iff, subtypeVal
-/
theorem Subtype.dense_iff {s : Set X} {t : Set s} : Dense t ↔ s subseteq closure ((↑) '' t) := by
  rw [IsInducing.subtypeVal.dense_iff]; rw [SetCoe.forall]
  rfl

@[simp]
/--
theorem `denseRange_inclusion_iff` / 定理 `denseRange_inclusion_iff`

English:
theorem denseRange_inclusion_iff
  given: {s t : Set X} (hst : s subseteq t)
  proof: by
  rw [DenseRange]; rw [Subtype.dense_iff]; rw [← range_comp]; rw [val_comp_inclusion]; rw [Subtype.range_coe]

中文:
定理 denseRange_inclusion_iff
  条件: {s t : Set X} (hst : s subseteq t)
  证明: by
  rw [DenseRange]; rw [Subtype.dense_iff]; rw [← range_comp]; rw [val_comp_inclusion]; rw [Subtype.range_coe]

Depends on / 依赖: DenseRange, Subtype, Subtype.dense_iff, Subtype.range_coe, dense_iff, range_coe, range_comp, val_comp_inclusion
-/
theorem denseRange_inclusion_iff {s t : Set X} (hst : s subseteq t) :
    DenseRange (inclusion hst) ↔ t subseteq closure s := by
  rw [DenseRange]; rw [Subtype.dense_iff]; rw [← range_comp]; rw [val_comp_inclusion]; rw [Subtype.range_coe]

/--
theorem `map_nhds_subtype_val` / 定理 `map_nhds_subtype_val`

English:
theorem map_nhds_subtype_val
  given: {s : Set X} (x : s)
  statement: map ((↑) : s -> X) (𝓝 x) = 𝓝[s] ↑x
  proof: by
  rw [IsInducing.subtypeVal.map_nhds_eq]; rw [Subtype.range_val]

中文:
定理 map_nhds_subtype_val
  条件: {s : Set X} (x : s)
  结论: map ((↑) : s -> X) (𝓝 x) = 𝓝[s] ↑x
  证明: by
  rw [IsInducing.subtypeVal.map_nhds_eq]; rw [Subtype.range_val]

Depends on / 依赖: IsInducing, IsInducing.subtypeVal.map_nhds_eq, Subtype, Subtype.range_val, map_nhds_eq, range_val, subtypeVal
-/
theorem map_nhds_subtype_val {s : Set X} (x : s) : map ((↑) : s -> X) (𝓝 x) = 𝓝[s] ↑x := by
  rw [IsInducing.subtypeVal.map_nhds_eq]; rw [Subtype.range_val]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `map_nhds_subtype_coe_eq_nhds` / 定理 `map_nhds_subtype_coe_eq_nhds`

English:
theorem map_nhds_subtype_coe_eq_nhds
  given: {x : X} (hx : p x) (h : forallᶠ x in 𝓝 x, p x)
  proof: map_nhds_induced_of_mem by rw [Subtype.range_val]; exact h

中文:
定理 map_nhds_subtype_coe_eq_nhds
  条件: {x : X} (hx : p x) (h : 对任意ᶠ x in 𝓝 x, p x)
  证明: map_nhds_induced_of_mem by rw [Subtype.range_val]; exact h

Depends on / 依赖: Subtype, Subtype.range_val, map_nhds_induced_of_mem, range_val
-/
theorem map_nhds_subtype_coe_eq_nhds {x : X} (hx : p x) (h : forallᶠ x in 𝓝 x, p x) :
    map ((↑) : Subtype p -> X) (𝓝 ⟨x, hx⟩) = 𝓝 x :=
map_nhds_induced_of_mem by rw [Subtype.range_val]; exact h

/--
theorem `nhds_subtype_eq_comap` / 定理 `nhds_subtype_eq_comap`

English:
theorem nhds_subtype_eq_comap
  given: {x : X} {h : p x}
  statement: 𝓝 (⟨x, h⟩ : Subtype p) = comap (↑) (𝓝 x)
  proof: nhds_induced _ _

中文:
定理 nhds_subtype_eq_comap
  条件: {x : X} {h : p x}
  结论: 𝓝 (⟨x, h⟩ : Subtype p) = comap (↑) (𝓝 x)
  证明: nhds_induced _ _

Depends on / 依赖: nhds_induced
-/
theorem nhds_subtype_eq_comap {x : X} {h : p x} : 𝓝 (⟨x, h⟩ : Subtype p) = comap (↑) (𝓝 x) :=
  nhds_induced _ _

/--
theorem `tendsto_subtype_rng` / 定理 `tendsto_subtype_rng`

English:
theorem tendsto_subtype_rng
  given: {Y : Type*} {p : X -> Prop} {l : Filter Y} {f : Y -> Subtype p}

中文:
定理 tendsto_subtype_rng
  条件: {Y : 类型} {p : X -> 命题} {l : Filter Y} {f : Y -> Subtype p}
-/
theorem tendsto_subtype_rng {Y : Type*} {p : X -> Prop} {l : Filter Y} {f : Y -> Subtype p} :
    forall {x : Subtype p}, Tendsto f l (𝓝 x) ↔ Tendsto (fun x => (f x : X)) l (𝓝 (x : X))
  | ⟨a, ha⟩ => by rw [nhds_subtype_eq_comap, tendsto_comap_iff]; rfl

/--
theorem `closure_subtype` / 定理 `closure_subtype`

English:
theorem closure_subtype
  given: {x : { a // p a }} {s : Set { a // p a }}
  proof: closure_induced

@[simp]

中文:
定理 closure_subtype
  条件: {x : { a // p a }} {s : Set { a // p a }}
  证明: closure_induced

@[simp]

Depends on / 依赖: closure_induced
-/
theorem closure_subtype {x : { a // p a }} {s : Set { a // p a }} :
    x in closure s ↔ (x : X) in closure (((↑) : _ -> X) '' s) :=
  closure_induced

@[simp]
/--
theorem `continuousAt_codRestrict_iff` / 定理 `continuousAt_codRestrict_iff`

English:
theorem continuousAt_codRestrict_iff
  given: {f : X -> Y} {t : Set Y} (h1 : forall x, f x in t) {x : X}
  proof: IsInducing.subtypeVal.continuousAt_iff

alias ⟨_, ContinuousAt.codRestrict⟩ := continuousAt_codRestrict_iff

中文:
定理 continuousAt_codRestrict_iff
  条件: {f : X -> Y} {t : Set Y} (h1 : 对任意 x, f x in t) {x : X}
  证明: IsInducing.subtypeVal.continuousAt_iff

alias ⟨_, ContinuousAt.codRestrict⟩ := continuousAt_codRestrict_iff

Depends on / 依赖: IsInducing, IsInducing.subtypeVal.continuousAt_iff, continuousAt_iff, subtypeVal
-/
theorem continuousAt_codRestrict_iff {f : X -> Y} {t : Set Y} (h1 : forall x, f x in t) {x : X} :
    ContinuousAt (codRestrict f t h1) x ↔ ContinuousAt f x :=
  IsInducing.subtypeVal.continuousAt_iff

alias ⟨_, ContinuousAt.codRestrict⟩ := continuousAt_codRestrict_iff

/--
theorem `ContinuousAt.restrict` / 定理 `ContinuousAt.restrict`

English:
theorem ContinuousAt.restrict
  statement: {f : X -> Y} {s : Set X} {t : Set Y} (h1 : MapsTo f s t) {x : s}
  proof: (h2.comp continuousAt_subtype_val).codRestrict _

中文:
定理 ContinuousAt.restrict
  结论: {f : X -> Y} {s : Set X} {t : Set Y} (h1 : MapsTo f s t) {x : s}
  证明: (h2.comp continuousAt_subtype_val).codRestrict _

Depends on / 依赖: codRestrict, continuousAt_subtype_val, h2.comp
-/
theorem ContinuousAt.restrict {f : X -> Y} {s : Set X} {t : Set Y} (h1 : MapsTo f s t) {x : s}
    (h2 : ContinuousAt f x) : ContinuousAt (h1.restrict f s t) x :=
  (h2.comp continuousAt_subtype_val).codRestrict _

/--
theorem `ContinuousAt.restrictPreimage` / 定理 `ContinuousAt.restrictPreimage`

English:
theorem ContinuousAt.restrictPreimage
  given: {f : X -> Y} {s : Set Y} {x : f ⁻¹' s} (h : ContinuousAt f x)
  proof: h.restrict _

@[continuity, fun_prop]

中文:
定理 ContinuousAt.restrictPreimage
  条件: {f : X -> Y} {s : Set Y} {x : f ⁻¹' s} (h : ContinuousAt f x)
  证明: h.restrict _

@[continuity, fun_prop]

Depends on / 依赖: h.restrict, restrict
-/
theorem ContinuousAt.restrictPreimage {f : X -> Y} {s : Set Y} {x : f ⁻¹' s} (h : ContinuousAt f x) :
    ContinuousAt (s.restrictPreimage f) x :=
  h.restrict _

@[continuity, fun_prop]
/--
theorem `Continuous.codRestrict` / 定理 `Continuous.codRestrict`

English:
theorem Continuous.codRestrict
  given: {f : X -> Y} {s : Set Y} (hf : Continuous f) (hs : forall a, f a in s)
  proof: hf.subtype_mk hs

中文:
定理 Continuous.codRestrict
  条件: {f : X -> Y} {s : Set Y} (hf : Continuous f) (hs : 对任意 a, f a in s)
  证明: hf.subtype_mk hs

Depends on / 依赖: hf.subtype_mk, subtype_mk
-/
theorem Continuous.codRestrict {f : X -> Y} {s : Set Y} (hf : Continuous f) (hs : forall a, f a in s) :
    Continuous (s.codRestrict f hs) :=
  hf.subtype_mk hs

/--
theorem `continuous_codRestrict_iff` / 定理 `continuous_codRestrict_iff`

English:
theorem continuous_codRestrict_iff
  given: {f : X -> Y} {s : Set Y} (hs : forall a, f a in s)
  proof: by
  refine ⟨?_, fun hf => hf.codRestrict hs⟩
  simp_rw [continuous_def]
  intro hf t ht
  exact hf (Subtype.val ⁻¹' t) (isOpen_induced ht)

中文:
定理 continuous_codRestrict_iff
  条件: {f : X -> Y} {s : Set Y} (hs : 对任意 a, f a in s)
  证明: by
  refine ⟨?_, fun hf => hf.codRestrict hs⟩
  simp_rw [continuous_def]
  intro hf t ht
  exact hf (Subtype.val ⁻¹' t) (isOpen_induced ht)

Depends on / 依赖: Subtype, Subtype.val, codRestrict, continuous_def, hf.codRestrict, isOpen_induced, simp_rw
-/
theorem continuous_codRestrict_iff {f : X -> Y} {s : Set Y} (hs : forall a, f a in s) :
    Continuous (codRestrict f s hs) ↔ Continuous f := by
  refine ⟨?_, fun hf => hf.codRestrict hs⟩
  simp_rw [continuous_def]
  intro hf t ht
  exact hf (Subtype.val ⁻¹' t) (isOpen_induced ht)

/--
theorem `IsOpenMap.codRestrict` / 定理 `IsOpenMap.codRestrict`

English:
theorem IsOpenMap.codRestrict
  given: {f : X -> Y} (hf : IsOpenMap f) {s : Set Y} (hs : forall a, f a in s)
  proof: hf.subtype_mk hs

中文:
定理 IsOpenMap.codRestrict
  条件: {f : X -> Y} (hf : IsOpenMap f) {s : Set Y} (hs : 对任意 a, f a in s)
  证明: hf.subtype_mk hs

Depends on / 依赖: hf.subtype_mk, subtype_mk
-/
theorem IsOpenMap.codRestrict {f : X -> Y} (hf : IsOpenMap f) {s : Set Y} (hs : forall a, f a in s) :
    IsOpenMap (s.codRestrict f hs) :=
  hf.subtype_mk hs

/--
theorem `IsClosedMap.codRestrict` / 定理 `IsClosedMap.codRestrict`

English:
theorem IsClosedMap.codRestrict
  given: {f : X -> Y} (hf : IsClosedMap f) {s : Set Y} (hs : forall a, f a in s)
  proof: hf.subtype_mk hs

@[continuity, fun_prop]

中文:
定理 IsClosedMap.codRestrict
  条件: {f : X -> Y} (hf : IsClosedMap f) {s : Set Y} (hs : 对任意 a, f a in s)
  证明: hf.subtype_mk hs

@[continuity, fun_prop]

Depends on / 依赖: hf.subtype_mk, subtype_mk
-/
theorem IsClosedMap.codRestrict {f : X -> Y} (hf : IsClosedMap f) {s : Set Y} (hs : forall a, f a in s) :
    IsClosedMap (s.codRestrict f hs) :=
  hf.subtype_mk hs

@[continuity, fun_prop]
/--
theorem `Continuous.restrict` / 定理 `Continuous.restrict`

English:
theorem Continuous.restrict
  statement: {f : X -> Y} {s : Set X} {t : Set Y} (h1 : MapsTo f s t)
  proof: (h2.comp continuous_subtype_val).codRestrict _

中文:
定理 Continuous.restrict
  结论: {f : X -> Y} {s : Set X} {t : Set Y} (h1 : MapsTo f s t)
  证明: (h2.comp continuous_subtype_val).codRestrict _

Depends on / 依赖: codRestrict, continuous_subtype_val, h2.comp
-/
theorem Continuous.restrict {f : X -> Y} {s : Set X} {t : Set Y} (h1 : MapsTo f s t)
    (h2 : Continuous f) : Continuous (h1.restrict f s t) :=
  (h2.comp continuous_subtype_val).codRestrict _

/--
lemma `IsOpenMap.mapsToRestrict` / 引理 `IsOpenMap.mapsToRestrict`

English:
lemma IsOpenMap.mapsToRestrict
  statement: {f : X -> Y} (hf : IsOpenMap f) {s : Set X} {t : Set Y}
  proof: (hf.domRestrict hs).codRestrict _

中文:
引理 IsOpenMap.mapsToRestrict
  结论: {f : X -> Y} (hf : IsOpenMap f) {s : Set X} {t : Set Y}
  证明: (hf.domRestrict hs).codRestrict _

Depends on / 依赖: codRestrict, domRestrict, hf.domRestrict
-/
lemma IsOpenMap.mapsToRestrict {f : X -> Y} (hf : IsOpenMap f) {s : Set X} {t : Set Y}
    (hs : IsOpen s) (ht : MapsTo f s t) : IsOpenMap ht.restrict :=
  (hf.domRestrict hs).codRestrict _

/--
lemma `IsClosedMap.mapsToRestrict` / 引理 `IsClosedMap.mapsToRestrict`

English:
lemma IsClosedMap.mapsToRestrict
  statement: {f : X -> Y} (hf : IsClosedMap f) {s : Set X} {t : Set Y}
  proof: (hf.domRestrict hs).codRestrict _

@[continuity, fun_prop]

中文:
引理 IsClosedMap.mapsToRestrict
  结论: {f : X -> Y} (hf : IsClosedMap f) {s : Set X} {t : Set Y}
  证明: (hf.domRestrict hs).codRestrict _

@[continuity, fun_prop]

Depends on / 依赖: codRestrict, domRestrict, hf.domRestrict
-/
lemma IsClosedMap.mapsToRestrict {f : X -> Y} (hf : IsClosedMap f) {s : Set X} {t : Set Y}
    (hs : IsClosed s) (ht : MapsTo f s t) : IsClosedMap ht.restrict :=
  (hf.domRestrict hs).codRestrict _

@[continuity, fun_prop]
/--
theorem `Continuous.restrictPreimage` / 定理 `Continuous.restrictPreimage`

English:
theorem Continuous.restrictPreimage
  given: {f : X -> Y} {s : Set Y} (h : Continuous f)
  proof: h.restrict _

@[fun_prop]

中文:
定理 Continuous.restrictPreimage
  条件: {f : X -> Y} {s : Set Y} (h : Continuous f)
  证明: h.restrict _

@[fun_prop]

Depends on / 依赖: h.restrict, restrict
-/
theorem Continuous.restrictPreimage {f : X -> Y} {s : Set Y} (h : Continuous f) :
    Continuous (s.restrictPreimage f) :=
  h.restrict _

@[fun_prop]
/--
lemma `Topology.IsEmbedding.restrict` / 引理 `Topology.IsEmbedding.restrict`

English:
lemma Topology.IsEmbedding.restrict
  statement: {f : X -> Y}
  proof: .of_comp (hf.continuous.restrict H) continuous_subtype_val (hf.comp .subtypeVal)

@[fun_prop]

中文:
引理 Topology.IsEmbedding.restrict
  结论: {f : X -> Y}
  证明: .of_comp (hf.continuous.restrict H) continuous_subtype_val (hf.comp .subtypeVal)

@[fun_prop]

Depends on / 依赖: continuous, continuous_subtype_val, hf.comp, hf.continuous.restrict, of_comp, restrict, subtypeVal
-/
lemma Topology.IsEmbedding.restrict {f : X -> Y}
    (hf : IsEmbedding f) {s : Set X} {t : Set Y} (H : s.MapsTo f t) :
    IsEmbedding H.restrict :=
  .of_comp (hf.continuous.restrict H) continuous_subtype_val (hf.comp .subtypeVal)

@[fun_prop]
/--
lemma `Topology.IsOpenEmbedding.restrict` / 引理 `Topology.IsOpenEmbedding.restrict`

English:
lemma Topology.IsOpenEmbedding.restrict
  statement: {f : X -> Y}
  proof: ⟨hf.isEmbedding.restrict H, (by
    rw [MapsTo.range_restrict]
    exact continuous_subtype_val.1 _ (hf.isOpenMap _ hs))⟩

中文:
引理 Topology.IsOpenEmbedding.restrict
  结论: {f : X -> Y}
  证明: ⟨hf.isEmbedding.restrict H, (by
    rw [MapsTo.range_restrict]
    exact continuous_subtype_val.1 _ (hf.isOpenMap _ hs))⟩

Depends on / 依赖: MapsTo, MapsTo.range_restrict, continuous_subtype_val, hf.isEmbedding.restrict, hf.isOpenMap, isEmbedding, isOpenMap, range_restrict, restrict
-/
lemma Topology.IsOpenEmbedding.restrict {f : X -> Y}
    (hf : IsOpenEmbedding f) {s : Set X} {t : Set Y} (H : s.MapsTo f t) (hs : IsOpen s) :
    IsOpenEmbedding H.restrict :=
  ⟨hf.isEmbedding.restrict H, (by
    rw [MapsTo.range_restrict]
    exact continuous_subtype_val.1 _ (hf.isOpenMap _ hs))⟩

/--
theorem `Topology.IsInducing.codRestrict` / 定理 `Topology.IsInducing.codRestrict`

English:
theorem Topology.IsInducing.codRestrict
  statement: {e : X -> Y} (he : IsInducing e) {s : Set Y}
  proof: he.of_comp (he.continuous.codRestrict hs) continuous_subtype_val

中文:
定理 Topology.IsInducing.codRestrict
  结论: {e : X -> Y} (he : IsInducing e) {s : Set Y}
  证明: he.of_comp (he.continuous.codRestrict hs) continuous_subtype_val

Depends on / 依赖: codRestrict, continuous, continuous_subtype_val, he.continuous.codRestrict, he.of_comp, of_comp
-/
theorem Topology.IsInducing.codRestrict {e : X -> Y} (he : IsInducing e) {s : Set Y}
    (hs : forall x, e x in s) : IsInducing (codRestrict e s hs) :=
  he.of_comp (he.continuous.codRestrict hs) continuous_subtype_val

/--
lemma `Topology.IsEmbedding.codRestrict` / 引理 `Topology.IsEmbedding.codRestrict`

English:
lemma Topology.IsEmbedding.codRestrict
  statement: {e : X -> Y} (he : IsEmbedding e) (s : Set Y)
  proof: he.of_comp (he.continuous.codRestrict hs) continuous_subtype_val

中文:
引理 Topology.IsEmbedding.codRestrict
  结论: {e : X -> Y} (he : IsEmbedding e) (s : Set Y)
  证明: he.of_comp (he.continuous.codRestrict hs) continuous_subtype_val
-/
protected lemma Topology.IsEmbedding.codRestrict {e : X -> Y} (he : IsEmbedding e) (s : Set Y)
    (hs : forall x, e x in s) : IsEmbedding (codRestrict e s hs) :=
  he.of_comp (he.continuous.codRestrict hs) continuous_subtype_val

variable {s t : Set X}

@[fun_prop]
/--
lemma `Topology.IsEmbedding.inclusion` / 引理 `Topology.IsEmbedding.inclusion`

English:
lemma Topology.IsEmbedding.inclusion
  given: (h : s subseteq t)
  proof: IsEmbedding.subtypeVal.codRestrict _ _

@[fun_prop]

中文:
引理 Topology.IsEmbedding.inclusion
  条件: (h : s subseteq t)
  证明: IsEmbedding.subtypeVal.codRestrict _ _

@[fun_prop]
-/
protected lemma Topology.IsEmbedding.inclusion (h : s subseteq t) :
    IsEmbedding (inclusion h) := IsEmbedding.subtypeVal.codRestrict _ _

@[fun_prop]
/--
lemma `Topology.IsOpenEmbedding.inclusion` / 引理 `Topology.IsOpenEmbedding.inclusion`

English:
lemma Topology.IsOpenEmbedding.inclusion
  given: (hst : s subseteq t) (hs : IsOpen (t ↓inter s))
  proof: .inclusion _
  isOpen_range := by rwa [range_inclusion]

@[fun_prop]

中文:
引理 Topology.IsOpenEmbedding.inclusion
  条件: (hst : s subseteq t) (hs : IsOpen (t ↓inter s))
  证明: .inclusion _
  isOpen_range := by rwa [range_inclusion]

@[fun_prop]
-/
protected lemma Topology.IsOpenEmbedding.inclusion (hst : s subseteq t) (hs : IsOpen (t ↓inter s)) :
    IsOpenEmbedding (inclusion hst) where
  toIsEmbedding := .inclusion _
  isOpen_range := by rwa [range_inclusion]

@[fun_prop]
/--
lemma `Topology.IsClosedEmbedding.inclusion` / 引理 `Topology.IsClosedEmbedding.inclusion`

English:
lemma Topology.IsClosedEmbedding.inclusion
  given: (hst : s subseteq t) (hs : IsClosed (t ↓inter s))
  proof: .inclusion _
  isClosed_range := by rwa [range_inclusion]

中文:
引理 Topology.IsClosedEmbedding.inclusion
  条件: (hst : s subseteq t) (hs : IsClosed (t ↓inter s))
  证明: .inclusion _
  isClosed_range := by rwa [range_inclusion]
-/
protected lemma Topology.IsClosedEmbedding.inclusion (hst : s subseteq t) (hs : IsClosed (t ↓inter s)) :
    IsClosedEmbedding (inclusion hst) where
  toIsEmbedding := .inclusion _
  isClosed_range := by rwa [range_inclusion]

/--
theorem `DiscreteTopology.of_subset` / 定理 `DiscreteTopology.of_subset`

English:
theorem DiscreteTopology.of_subset
  statement: {X : Type*} [TopologicalSpace X] {s t : Set X}
  proof: (IsEmbedding.inclusion ts).discreteTopology

中文:
定理 DiscreteTopology.of_subset
  结论: {X : 类型} [TopologicalSpace X] {s t : Set X}
  证明: (IsEmbedding.inclusion ts).discreteTopology

Depends on / 依赖: IsEmbedding, IsEmbedding.inclusion, discreteTopology, inclusion
-/
theorem DiscreteTopology.of_subset {X : Type*} [TopologicalSpace X] {s t : Set X}
    (_ : DiscreteTopology s) (ts : t subseteq s) : DiscreteTopology t :=
  (IsEmbedding.inclusion ts).discreteTopology

/--
lemma `IsDiscrete.mono` / 引理 `IsDiscrete.mono`

English:
lemma IsDiscrete.mono
  given: {t : Set X} (hs : IsDiscrete s) (hst : t subseteq s)
  statement: IsDiscrete t
  proof: ⟨.of_subset hs.to_subtype hst⟩

中文:
引理 IsDiscrete.mono
  条件: {t : Set X} (hs : IsDiscrete s) (hst : t subseteq s)
  结论: IsDiscrete t
  证明: ⟨.of_subset hs.to_subtype hst⟩

Depends on / 依赖: hs.to_subtype, of_subset, to_subtype
-/
lemma IsDiscrete.mono {t : Set X} (hs : IsDiscrete s) (hst : t subseteq s) : IsDiscrete t :=
  ⟨.of_subset hs.to_subtype hst⟩

/--
theorem `DiscreteTopology.preimage_of_continuous_injective` / 定理 `DiscreteTopology.preimage_of_continuous_injective`

English:
theorem DiscreteTopology.preimage_of_continuous_injective
  statement: {X Y : Type*} [TopologicalSpace X]
  proof: DiscreteTopology.of_continuous_injective (β := s) (Continuous.restrict
    (by exact fun _ x => x) hc) ((MapsTo.restrict_inj _).mpr hinj.injOn)

中文:
定理 DiscreteTopology.preimage_of_continuous_injective
  结论: {X Y : 类型} [TopologicalSpace X]
  证明: DiscreteTopology.of_continuous_injective (β := s) (Continuous.restrict
    (by exact fun _ x => x) hc) ((MapsTo.restrict_inj _).mpr hinj.injOn)

Depends on / 依赖: Continuous, Continuous.restrict, DiscreteTopology, DiscreteTopology.of_continuous_injective, MapsTo, MapsTo.restrict_inj, hinj.injOn, of_continuous_injective, restrict, restrict_inj
-/
theorem DiscreteTopology.preimage_of_continuous_injective {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (s : Set Y) [DiscreteTopology s] {f : X -> Y} (hc : Continuous f)
    (hinj : Function.Injective f) : DiscreteTopology (f ⁻¹' s) :=
  DiscreteTopology.of_continuous_injective (β := s) (Continuous.restrict
    (by exact fun _ x => x) hc) ((MapsTo.restrict_inj _).mpr hinj.injOn)

/--
lemma `Topology.IsCoinducing.restrictPreimage_of_isOpen` / 引理 `Topology.IsCoinducing.restrictPreimage_of_isOpen`

English:
lemma Topology.IsCoinducing.restrictPreimage_of_isOpen
  statement: {f : X -> Y} (hf : IsCoinducing f)
  proof: by
  refine .of_isOpen_preimage_iff_isOpen fun _ => ?_
  rw [hs.isOpenEmbedding_subtypeVal.isOpen_iff_image_isOpen]; rw [← hf.isOpen_preimage]; rw [(hs.preimage hf.continuous).isOpenEmbedding_subtypeVal.isOpen_iff_image_isOpen]; rw [image_val_preimage_restrictPreimage]

中文:
引理 Topology.IsCoinducing.restrictPreimage_of_isOpen
  结论: {f : X -> Y} (hf : IsCoinducing f)
  证明: by
  refine .of_isOpen_preimage_iff_isOpen fun _ => ?_
  rw [hs.isOpenEmbedding_subtypeVal.isOpen_iff_image_isOpen]; rw [← hf.isOpen_preimage]; rw [(hs.preimage hf.continuous).isOpenEmbedding_subtypeVal.isOpen_iff_image_isOpen]; rw [image_val_preimage_restrictPreimage]

Depends on / 依赖: continuous, hf.continuous, hf.isOpen_preimage, hs.isOpenEmbedding_subtypeVal.isOpen_iff_image_isOpen, hs.preimage, image_val_preimage_restrictPreimage, isOpenEmbedding_subtypeVal, isOpenEmbedding_subtypeVal.isOpen_iff_image_isOpen, isOpen_iff_image_isOpen, isOpen_preimage, of_isOpen_preimage_iff_isOpen, preimage
-/
lemma Topology.IsCoinducing.restrictPreimage_of_isOpen {f : X -> Y} (hf : IsCoinducing f)
    {s : Set Y} (hs : IsOpen s) :
    IsCoinducing (s.restrictPreimage f) := by
  refine .of_isOpen_preimage_iff_isOpen fun _ => ?_
  rw [hs.isOpenEmbedding_subtypeVal.isOpen_iff_image_isOpen]; rw [← hf.isOpen_preimage]; rw [(hs.preimage hf.continuous).isOpenEmbedding_subtypeVal.isOpen_iff_image_isOpen]; rw [image_val_preimage_restrictPreimage]

/--
theorem `Topology.IsQuotientMap.restrictPreimage_isOpen` / 定理 `Topology.IsQuotientMap.restrictPreimage_isOpen`

English:
theorem Topology.IsQuotientMap.restrictPreimage_isOpen
  statement: {f : X -> Y} (hf : IsQuotientMap f)
  proof: (isQuotientMap_iff _).2
    ⟨.restrictPreimage_of_isOpen hf.isCoinducing hs, hf.surjective.restrictPreimage _⟩

中文:
定理 Topology.IsQuotientMap.restrictPreimage_isOpen
  结论: {f : X -> Y} (hf : IsQuotientMap f)
  证明: (isQuotientMap_iff _).2
    ⟨.restrictPreimage_of_isOpen hf.isCoinducing hs, hf.surjective.restrictPreimage _⟩

Depends on / 依赖: hf.isCoinducing, hf.surjective.restrictPreimage, isCoinducing, isQuotientMap_iff, restrictPreimage, restrictPreimage_of_isOpen, surjective
-/
theorem Topology.IsQuotientMap.restrictPreimage_isOpen {f : X -> Y} (hf : IsQuotientMap f)
    {s : Set Y} (hs : IsOpen s) : IsQuotientMap (s.restrictPreimage f) :=
  (isQuotientMap_iff _).2
    ⟨.restrictPreimage_of_isOpen hf.isCoinducing hs, hf.surjective.restrictPreimage _⟩

open scoped Set.Notation in
/--
lemma `isClosed_preimage_val` / 引理 `isClosed_preimage_val`

English:
lemma isClosed_preimage_val
  given: {s t : Set X}
  statement: IsClosed (s ↓inter t) ↔ s inter closure (s inter t) subseteq t
  proof: by
  rw [← closure_eq_iff_isClosed]; rw [IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]; rw [← Subtype.val_injective.image_injective.eq_iff]; rw [Subtype.image_preimage_coe]; rw [Subtype.image_preimage_coe]; rw [subset_antisymm_iff]; rw [and_iff_left]; rw [Set.subset_inter_iff]; rw [and_i

中文:
引理 isClosed_preimage_val
  条件: {s t : Set X}
  结论: IsClosed (s ↓inter t) ↔ s inter closure (s inter t) subseteq t
  证明: by
  rw [← closure_eq_iff_isClosed]; rw [IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]; rw [← Subtype.val_injective.image_injective.eq_iff]; rw [Subtype.image_preimage_coe]; rw [Subtype.image_preimage_coe]; rw [subset_antisymm_iff]; rw [and_iff_left]; rw [Set.subset_inter_iff]; rw [and_i

Depends on / 依赖: IsEmbedding, IsEmbedding.subtypeVal.closure_eq_preimage_closure_image, Set.inter_subset_left, Set.subset_inter, Set.subset_inter_iff, Subtype, Subtype.image_preimage_coe, Subtype.val_injective.image_injective.eq_iff, and_iff_left, and_iff_right, closure_eq_iff_isClosed, closure_eq_preimage_closure_image, eq_iff, exacts, image_injective, image_preimage_coe, inter_subset_left, subset_antisymm_iff, subset_closure, subset_inter
-/
lemma isClosed_preimage_val {s t : Set X} : IsClosed (s ↓inter t) ↔ s inter closure (s inter t) subseteq t := by
  rw [← closure_eq_iff_isClosed]; rw [IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]; rw [← Subtype.val_injective.image_injective.eq_iff]; rw [Subtype.image_preimage_coe]; rw [Subtype.image_preimage_coe]; rw [subset_antisymm_iff]; rw [and_iff_left]; rw [Set.subset_inter_iff]; rw [and_iff_right]
  exacts [Set.inter_subset_left, Set.subset_inter Set.inter_subset_left subset_closure]

/--
theorem `frontier_inter_open_inter` / 定理 `frontier_inter_open_inter`

English:
theorem frontier_inter_open_inter
  given: {s t : Set X} (ht : IsOpen t)
  proof: by
  simp only [Set.inter_comm _ t, ← Subtype.preimage_coe_eq_preimage_coe_iff,
    ht.isOpenMap_subtype_val.preimage_frontier_eq_frontier_preimage continuous_subtype_val,
    Subtype.preimage_coe_self_inter]

中文:
定理 frontier_inter_open_inter
  条件: {s t : Set X} (ht : IsOpen t)
  证明: by
  simp only [Set.inter_comm _ t, ← Subtype.preimage_coe_eq_preimage_coe_iff,
    ht.isOpenMap_subtype_val.preimage_frontier_eq_frontier_preimage continuous_subtype_val,
    Subtype.preimage_coe_self_inter]

Depends on / 依赖: Set.inter_comm, Subtype, Subtype.preimage_coe_eq_preimage_coe_iff, Subtype.preimage_coe_self_inter, continuous_subtype_val, ht.isOpenMap_subtype_val.preimage_frontier_eq_frontier_preimage, inter_comm, isOpenMap_subtype_val, preimage_coe_eq_preimage_coe_iff, preimage_coe_self_inter, preimage_frontier_eq_frontier_preimage
-/
theorem frontier_inter_open_inter {s t : Set X} (ht : IsOpen t) :
    frontier (s inter t) inter t = frontier s inter t := by
  simp only [Set.inter_comm _ t, ← Subtype.preimage_coe_eq_preimage_coe_iff,
    ht.isOpenMap_subtype_val.preimage_frontier_eq_frontier_preimage continuous_subtype_val,
    Subtype.preimage_coe_self_inter]

section SetNotation

open scoped Set.Notation

/--
lemma `IsOpen.preimage_val` / 引理 `IsOpen.preimage_val`

English:
lemma IsOpen.preimage_val
  given: {s t : Set X} (ht : IsOpen t)
  statement: IsOpen (s ↓inter t)
  proof: ht.preimage continuous_subtype_val

中文:
引理 IsOpen.preimage_val
  条件: {s t : Set X} (ht : IsOpen t)
  结论: IsOpen (s ↓inter t)
  证明: ht.preimage continuous_subtype_val

Depends on / 依赖: continuous_subtype_val, ht.preimage, preimage
-/
lemma IsOpen.preimage_val {s t : Set X} (ht : IsOpen t) : IsOpen (s ↓inter t) :=
  ht.preimage continuous_subtype_val

/--
lemma `IsOpen.image_val` / 引理 `IsOpen.image_val`

English:
lemma IsOpen.image_val
  given: {s : Set X} {t : Set s} (ht : IsOpen t)
  proof: by
  simpa using IsInducing.subtypeVal.image_eq_isOpen_inter_range ht

中文:
引理 IsOpen.image_val
  条件: {s : Set X} {t : Set s} (ht : IsOpen t)
  证明: by
  simpa using IsInducing.subtypeVal.image_eq_isOpen_inter_range ht

Depends on / 依赖: IsInducing, IsInducing.subtypeVal.image_eq_isOpen_inter_range, image_eq_isOpen_inter_range, subtypeVal
-/
lemma IsOpen.image_val {s : Set X} {t : Set s} (ht : IsOpen t) :
    exists c, IsOpen c ∧ Subtype.val '' t = c inter s := by
  simpa using IsInducing.subtypeVal.image_eq_isOpen_inter_range ht

/--
lemma `exists_open_dense_of_open_dense_subtype` / 引理 `exists_open_dense_of_open_dense_subtype`

English:
lemma exists_open_dense_of_open_dense_subtype
  statement: (hs : Dense s) {u : Set s} (huo : IsOpen u)
  proof: by
  choose v hv1 hv2 using huo
  refine ⟨v, hv1, ?_, hv2⟩
  rw [dense_iff_inter_open] at *
  intro t ht ht'
  subst hv2
  refine nonempty_of_nonempty_preimage (f := (Subtype.val : s -> X)) (hud (Subtype.val ⁻¹' t) ?_ ?_)
  · exact IsOpen.preimage_val ht
  · obtain ⟨x, hx⟩ := hs t ht ht'
    simpa u

中文:
引理 exists_open_dense_of_open_dense_subtype
  结论: (hs : Dense s) {u : Set s} (huo : IsOpen u)
  证明: by
  choose v hv1 hv2 using huo
  refine ⟨v, hv1, ?_, hv2⟩
  rw [dense_iff_inter_open] at *
  intro t ht ht'
  subst hv2
  refine nonempty_of_nonempty_preimage (f := (Subtype.val : s -> X)) (hud (Subtype.val ⁻¹' t) ?_ ?_)
  · exact IsOpen.preimage_val ht
  · obtain ⟨x, hx⟩ := hs t ht ht'
    simpa u

Depends on / 依赖: IsOpen, IsOpen.preimage_val, Subtype, Subtype.val, dense_iff_inter_open, nonempty_of_nonempty_preimage, preimage_val
-/
lemma exists_open_dense_of_open_dense_subtype (hs : Dense s) {u : Set s} (huo : IsOpen u)
    (hud : Dense u) :
    exists v : Set X, IsOpen v ∧ Dense v ∧ Subtype.val ⁻¹' v = u := by
  choose v hv1 hv2 using huo
  refine ⟨v, hv1, ?_, hv2⟩
  rw [dense_iff_inter_open] at *
  intro t ht ht'
  subst hv2
  refine nonempty_of_nonempty_preimage (f := (Subtype.val : s -> X)) (hud (Subtype.val ⁻¹' t) ?_ ?_)
  · exact IsOpen.preimage_val ht
  · obtain ⟨x, hx⟩ := hs t ht ht'
    simpa using ⟨⟨x, hx.2⟩, hx.1⟩

/--
lemma `IsClosed.preimage_val` / 引理 `IsClosed.preimage_val`

English:
lemma IsClosed.preimage_val
  given: {s t : Set X} (ht : IsClosed t)
  statement: IsClosed (s ↓inter t)
  proof: ht.preimage continuous_subtype_val

中文:
引理 IsClosed.preimage_val
  条件: {s t : Set X} (ht : IsClosed t)
  结论: IsClosed (s ↓inter t)
  证明: ht.preimage continuous_subtype_val

Depends on / 依赖: continuous_subtype_val, ht.preimage, preimage
-/
lemma IsClosed.preimage_val {s t : Set X} (ht : IsClosed t) : IsClosed (s ↓inter t) :=
  ht.preimage continuous_subtype_val

/--
lemma `IsClosed.image_val` / 引理 `IsClosed.image_val`

English:
lemma IsClosed.image_val
  given: {s : Set X} {t : Set s} (ht : IsClosed t)
  proof: by
  simpa using IsInducing.subtypeVal.image_eq_isClosed_inter_range ht

中文:
引理 IsClosed.image_val
  条件: {s : Set X} {t : Set s} (ht : IsClosed t)
  证明: by
  simpa using IsInducing.subtypeVal.image_eq_isClosed_inter_range ht

Depends on / 依赖: IsInducing, IsInducing.subtypeVal.image_eq_isClosed_inter_range, image_eq_isClosed_inter_range, subtypeVal
-/
lemma IsClosed.image_val {s : Set X} {t : Set s} (ht : IsClosed t) :
    exists c, IsClosed c ∧ Subtype.val '' t = c inter s := by
  simpa using IsInducing.subtypeVal.image_eq_isClosed_inter_range ht

/--
lemma `IsOpen.inter_preimage_val_iff` / 引理 `IsOpen.inter_preimage_val_iff`

English:
lemma IsOpen.inter_preimage_val_iff
  given: {s t : Set X} (hs : IsOpen s)
  proof: ⟨fun h => by simpa using hs.isOpenMap_subtype_val _ h,
    fun h => (Subtype.preimage_coe_self_inter _ _).symm ▸ h.preimage_val⟩

中文:
引理 IsOpen.inter_preimage_val_iff
  条件: {s t : Set X} (hs : IsOpen s)
  证明: ⟨fun h => by simpa using hs.isOpenMap_subtype_val _ h,
    fun h => (Subtype.preimage_coe_self_inter _ _).symm ▸ h.preimage_val⟩
-/
@[simp] lemma IsOpen.inter_preimage_val_iff {s t : Set X} (hs : IsOpen s) :
    IsOpen (s ↓inter t) ↔ IsOpen (s inter t) :=
  ⟨fun h => by simpa using hs.isOpenMap_subtype_val _ h,
    fun h => (Subtype.preimage_coe_self_inter _ _).symm ▸ h.preimage_val⟩

/--
lemma `IsClosed.inter_preimage_val_iff` / 引理 `IsClosed.inter_preimage_val_iff`

English:
lemma IsClosed.inter_preimage_val_iff
  given: {s t : Set X} (hs : IsClosed s)
  proof: ⟨fun h => by simpa using hs.isClosedMap_subtype_val _ h,
    fun h => (Subtype.preimage_coe_self_inter _ _).symm ▸ h.preimage_val⟩

中文:
引理 IsClosed.inter_preimage_val_iff
  条件: {s t : Set X} (hs : IsClosed s)
  证明: ⟨fun h => by simpa using hs.isClosedMap_subtype_val _ h,
    fun h => (Subtype.preimage_coe_self_inter _ _).symm ▸ h.preimage_val⟩
-/
@[simp] lemma IsClosed.inter_preimage_val_iff {s t : Set X} (hs : IsClosed s) :
    IsClosed (s ↓inter t) ↔ IsClosed (s inter t) :=
  ⟨fun h => by simpa using hs.isClosedMap_subtype_val _ h,
    fun h => (Subtype.preimage_coe_self_inter _ _).symm ▸ h.preimage_val⟩

end SetNotation

end Subtype

section Quotient

variable [TopologicalSpace X] [TopologicalSpace Y]
variable {r : X -> X -> Prop} {s : Setoid X}

/--
theorem `isQuotientMap_quot_mk` / 定理 `isQuotientMap_quot_mk`

English:
theorem isQuotientMap_quot_mk
  statement: IsQuotientMap (@Quot.mk X r)
  proof: ⟨⟨rfl⟩, Quot.exists_rep⟩

@[continuity, fun_prop]

中文:
定理 isQuotientMap_quot_mk
  结论: IsQuotientMap (@Quot.mk X r)
  证明: ⟨⟨rfl⟩, Quot.exists_rep⟩

@[continuity, fun_prop]

Depends on / 依赖: Quot.exists_rep, exists_rep
-/
theorem isQuotientMap_quot_mk : IsQuotientMap (@Quot.mk X r) :=
  ⟨⟨rfl⟩, Quot.exists_rep⟩

@[continuity, fun_prop]
/--
theorem `continuous_quot_mk` / 定理 `continuous_quot_mk`

English:
theorem continuous_quot_mk
  statement: Continuous (@Quot.mk X r)
  proof: continuous_coinduced_rng

@[continuity, fun_prop]

中文:
定理 continuous_quot_mk
  结论: Continuous (@Quot.mk X r)
  证明: continuous_coinduced_rng

@[continuity, fun_prop]

Depends on / 依赖: continuous_coinduced_rng
-/
theorem continuous_quot_mk : Continuous (@Quot.mk X r) :=
  continuous_coinduced_rng

@[continuity, fun_prop]
/--
theorem `continuous_quot_lift` / 定理 `continuous_quot_lift`

English:
theorem continuous_quot_lift
  given: {f : X -> Y} (hr : forall a b, r a b -> f a = f b) (h : Continuous f)
  proof: continuous_coinduced_dom.2 h

@[continuity, fun_prop]

中文:
定理 continuous_quot_lift
  条件: {f : X -> Y} (hr : 对任意 a b, r a b -> f a = f b) (h : Continuous f)
  证明: continuous_coinduced_dom.2 h

@[continuity, fun_prop]

Depends on / 依赖: continuous_coinduced_dom
-/
theorem continuous_quot_lift {f : X -> Y} (hr : forall a b, r a b -> f a = f b) (h : Continuous f) :
    Continuous (Quot.lift f hr : Quot r -> Y) :=
  continuous_coinduced_dom.2 h

@[continuity, fun_prop]
/--
theorem `continuous_quot_map` / 定理 `continuous_quot_map`

English:
theorem continuous_quot_map
  statement: {r' : Y -> Y -> Prop} {f : X -> Y} (hr : forall a b, r a b -> r' (f a) (f b))
  proof: continuous_quot_lift _ (continuous_quot_mk.comp h)

中文:
定理 continuous_quot_map
  结论: {r' : Y -> Y -> 命题} {f : X -> Y} (hr : 对任意 a b, r a b -> r' (f a) (f b))
  证明: continuous_quot_lift _ (continuous_quot_mk.comp h)

Depends on / 依赖: continuous_quot_lift, continuous_quot_mk, continuous_quot_mk.comp
-/
theorem continuous_quot_map {r' : Y -> Y -> Prop} {f : X -> Y} (hr : forall a b, r a b -> r' (f a) (f b))
    (h : Continuous f) :
    Continuous (Quot.map f hr : Quot r -> Quot r') :=
  continuous_quot_lift _ (continuous_quot_mk.comp h)

/--
theorem `isQuotientMap_quotient_mk'` / 定理 `isQuotientMap_quotient_mk'`

English:
theorem isQuotientMap_quotient_mk'
  statement: IsQuotientMap (@Quotient.mk' X s)
  proof: isQuotientMap_quot_mk

中文:
定理 isQuotientMap_quotient_mk'
  结论: IsQuotientMap (@Quotient.mk' X s)
  证明: isQuotientMap_quot_mk

Depends on / 依赖: isQuotientMap_quot_mk
-/
theorem isQuotientMap_quotient_mk' : IsQuotientMap (@Quotient.mk' X s) :=
  isQuotientMap_quot_mk

/--
theorem `continuous_quotient_mk'` / 定理 `continuous_quotient_mk'`

English:
theorem continuous_quotient_mk'
  statement: Continuous (@Quotient.mk' X s)
  proof: continuous_coinduced_rng

中文:
定理 continuous_quotient_mk'
  结论: Continuous (@Quotient.mk' X s)
  证明: continuous_coinduced_rng

Depends on / 依赖: continuous_coinduced_rng
-/
theorem continuous_quotient_mk' : Continuous (@Quotient.mk' X s) :=
  continuous_coinduced_rng

/--
theorem `Continuous.quotient_lift` / 定理 `Continuous.quotient_lift`

English:
theorem Continuous.quotient_lift
  given: {f : X -> Y} (h : Continuous f) (hs : forall a b, a ≈ b -> f a = f b)
  proof: continuous_coinduced_dom.2 h

中文:
定理 Continuous.quotient_lift
  条件: {f : X -> Y} (h : Continuous f) (hs : 对任意 a b, a ≈ b -> f a = f b)
  证明: continuous_coinduced_dom.2 h

Depends on / 依赖: continuous_coinduced_dom
-/
theorem Continuous.quotient_lift {f : X -> Y} (h : Continuous f) (hs : forall a b, a ≈ b -> f a = f b) :
    Continuous (Quotient.lift f hs : Quotient s -> Y) :=
  continuous_coinduced_dom.2 h

/--
theorem `Continuous.quotient_liftOn'` / 定理 `Continuous.quotient_liftOn'`

English:
theorem Continuous.quotient_liftOn'
  statement: {f : X -> Y} (h : Continuous f)
  proof: h.quotient_lift hs

中文:
定理 Continuous.quotient_liftOn'
  结论: {f : X -> Y} (h : Continuous f)
  证明: h.quotient_lift hs

Depends on / 依赖: h.quotient_lift, quotient_lift
-/
theorem Continuous.quotient_liftOn' {f : X -> Y} (h : Continuous f)
    (hs : forall a b, s a b -> f a = f b) :
    Continuous (fun x => Quotient.liftOn' x f hs : Quotient s -> Y) :=
  h.quotient_lift hs

open scoped Relator in
@[continuity, fun_prop]
/--
theorem `Continuous.quotient_map'` / 定理 `Continuous.quotient_map'`

English:
theorem Continuous.quotient_map'
  statement: {t : Setoid Y} {f : X -> Y} (hf : Continuous f)
  proof: (continuous_quotient_mk'.comp hf).quotient_lift _

中文:
定理 Continuous.quotient_map'
  结论: {t : Setoid Y} {f : X -> Y} (hf : Continuous f)
  证明: (continuous_quotient_mk'.comp hf).quotient_lift _

Depends on / 依赖: continuous_quotient_mk, quotient_lift
-/
theorem Continuous.quotient_map' {t : Setoid Y} {f : X -> Y} (hf : Continuous f)
    (H : (s.r ⇒ t.r) f f) : Continuous (Quotient.map' f H) :=
  (continuous_quotient_mk'.comp hf).quotient_lift _

end Quotient

section Pi

variable {ι : Type*} {A B : ι -> Type*} {κ : Type*} [TopologicalSpace X]
  [T : forall i, TopologicalSpace (A i)] [forall i, TopologicalSpace (B i)] {f : X -> forall i : ι, A i}

/--
theorem `continuous_pi_iff` / 定理 `continuous_pi_iff`

English:
theorem continuous_pi_iff
  statement: Continuous f ↔ forall i, Continuous fun a => f a i
  proof: by
  simp only [continuous_iInf_rng, continuous_induced_rng, comp_def]

@[continuity, fun_prop]

中文:
定理 continuous_pi_iff
  结论: Continuous f ↔ 对任意 i, Continuous fun a => f a i
  证明: by
  simp only [continuous_iInf_rng, continuous_induced_rng, comp_def]

@[continuity, fun_prop]

Depends on / 依赖: comp_def, continuous_iInf_rng, continuous_induced_rng
-/
theorem continuous_pi_iff : Continuous f ↔ forall i, Continuous fun a => f a i := by
  simp only [continuous_iInf_rng, continuous_induced_rng, comp_def]

@[continuity, fun_prop]
/--
theorem `continuous_pi` / 定理 `continuous_pi`

English:
theorem continuous_pi
  given: (h : forall i, Continuous fun a => f a i)
  statement: Continuous f
  proof: continuous_pi_iff.2 h

@[continuity, fun_prop]

中文:
定理 continuous_pi
  条件: (h : 对任意 i, Continuous fun a => f a i)
  结论: Continuous f
  证明: continuous_pi_iff.2 h

@[continuity, fun_prop]
-/
theorem continuous_pi (h : forall i, Continuous fun a => f a i) : Continuous f :=
  continuous_pi_iff.2 h

@[continuity, fun_prop]
/--
theorem `continuous_apply` / 定理 `continuous_apply`

English:
theorem continuous_apply
  given: (i : ι)
  statement: Continuous fun p : forall i, A i => p i
  proof: continuous_iInf_dom continuous_induced_dom

@[continuity]

中文:
定理 continuous_apply
  条件: (i : ι)
  结论: Continuous fun p : 对任意 i, A i => p i
  证明: continuous_iInf_dom continuous_induced_dom

@[continuity]
-/
theorem continuous_apply (i : ι) : Continuous fun p : forall i, A i => p i :=
  continuous_iInf_dom continuous_induced_dom

@[continuity]
/--
theorem `continuous_apply_apply` / 定理 `continuous_apply_apply`

English:
theorem continuous_apply_apply
  statement: {ρ : κ -> ι -> Type*} [forall j i, TopologicalSpace (ρ j i)] (j : κ)
  proof: (continuous_apply i).comp (continuous_apply j)

中文:
定理 continuous_apply_apply
  结论: {ρ : κ -> ι -> 类型} [对任意 j i, TopologicalSpace (ρ j i)] (j : κ)
  证明: (continuous_apply i).comp (continuous_apply j)

Depends on / 依赖: continuous_apply
-/
theorem continuous_apply_apply {ρ : κ -> ι -> Type*} [forall j i, TopologicalSpace (ρ j i)] (j : κ)
    (i : ι) : Continuous fun p : forall j, forall i, ρ j i => p j i :=
  (continuous_apply i).comp (continuous_apply j)

/--
theorem `continuousAt_apply` / 定理 `continuousAt_apply`

English:
theorem continuousAt_apply
  given: (i : ι) (x : forall i, A i)
  statement: ContinuousAt (fun p : forall i, A i => p i) x
  proof: (continuous_apply i).continuousAt

中文:
定理 continuousAt_apply
  条件: (i : ι) (x : 对任意 i, A i)
  结论: ContinuousAt (fun p : 对任意 i, A i => p i) x
  证明: (continuous_apply i).continuousAt

Depends on / 依赖: continuousAt, continuous_apply
-/
theorem continuousAt_apply (i : ι) (x : forall i, A i) : ContinuousAt (fun p : forall i, A i => p i) x :=
  (continuous_apply i).continuousAt

/--
theorem `Filter.Tendsto.apply_nhds` / 定理 `Filter.Tendsto.apply_nhds`

English:
theorem Filter.Tendsto.apply_nhds
  statement: {l : Filter Y} {f : Y -> forall i, A i} {x : forall i, A i}
  proof: (continuousAt_apply i _).tendsto.comp h

@[fun_prop]

中文:
定理 Filter.Tendsto.apply_nhds
  结论: {l : Filter Y} {f : Y -> 对任意 i, A i} {x : 对任意 i, A i}
  证明: (continuousAt_apply i _).tendsto.comp h

@[fun_prop]

Depends on / 依赖: continuousAt_apply, tendsto, tendsto.comp
-/
theorem Filter.Tendsto.apply_nhds {l : Filter Y} {f : Y -> forall i, A i} {x : forall i, A i}
    (h : Tendsto f l (𝓝 x)) (i : ι) : Tendsto (fun a => f a i) l (𝓝 <| x i) :=
  (continuousAt_apply i _).tendsto.comp h

@[fun_prop]
/--
theorem `Continuous.piMap` / 定理 `Continuous.piMap`

English:
theorem Continuous.piMap
  proof: continuous_pi fun i => (hf i).comp (continuous_apply i)

中文:
定理 Continuous.piMap
  证明: continuous_pi fun i => (hf i).comp (continuous_apply i)
-/
protected theorem Continuous.piMap
    {f : forall i, A i -> B i} (hf : forall i, Continuous (f i)) : Continuous (Pi.map f) :=
  continuous_pi fun i => (hf i).comp (continuous_apply i)

/--
theorem `nhds_pi` / 定理 `nhds_pi`

English:
theorem nhds_pi
  given: {a : forall i, A i}
  statement: 𝓝 a = pi fun i => 𝓝 (a i)
  proof: by
  simp only [nhds_iInf, nhds_induced, Filter.pi]

中文:
定理 nhds_pi
  条件: {a : 对任意 i, A i}
  结论: 𝓝 a = pi fun i => 𝓝 (a i)
  证明: by
  simp only [nhds_iInf, nhds_induced, Filter.pi]

Depends on / 依赖: Filter, Filter.pi, nhds_iInf, nhds_induced
-/
theorem nhds_pi {a : forall i, A i} : 𝓝 a = pi fun i => 𝓝 (a i) := by
  simp only [nhds_iInf, nhds_induced, Filter.pi]

/--
theorem `IsOpenMap.piMap` / 定理 `IsOpenMap.piMap`

English:
theorem IsOpenMap.piMap
  statement: {f : forall i, A i -> B i}
  proof: by
  refine IsOpenMap.of_nhds_le fun x => ?_
  rw [nhds_pi]; rw [nhds_pi]; rw [map_piMap_pi hsurj]
  exact Filter.pi_mono fun i => (hfo i).nhds_le _

中文:
定理 IsOpenMap.piMap
  结论: {f : 对任意 i, A i -> B i}
  证明: by
  refine IsOpenMap.of_nhds_le fun x => ?_
  rw [nhds_pi]; rw [nhds_pi]; rw [map_piMap_pi hsurj]
  exact Filter.pi_mono fun i => (hfo i).nhds_le _
-/
protected theorem IsOpenMap.piMap {f : forall i, A i -> B i}
    (hfo : forall i, IsOpenMap (f i)) (hsurj : forallᶠ i in cofinite, Surjective (f i)) :
    IsOpenMap (Pi.map f) := by
  refine IsOpenMap.of_nhds_le fun x => ?_
  rw [nhds_pi]; rw [nhds_pi]; rw [map_piMap_pi hsurj]
  exact Filter.pi_mono fun i => (hfo i).nhds_le _

/--
theorem `IsOpenQuotientMap.piMap` / 定理 `IsOpenQuotientMap.piMap`

English:
theorem IsOpenQuotientMap.piMap
  proof: ⟨.piMap fun i => (hf i).1, .piMap fun i => (hf i).2, .piMap (fun i => (hf i).3)
    .of_forall fun i => (hf i).1⟩

中文:
定理 IsOpenQuotientMap.piMap
  证明: ⟨.piMap fun i => (hf i).1, .piMap fun i => (hf i).2, .piMap (fun i => (hf i).3)
    .of_forall fun i => (hf i).1⟩
-/
protected theorem IsOpenQuotientMap.piMap
    {f : forall i, A i -> B i} (hf : forall i, IsOpenQuotientMap (f i)) : IsOpenQuotientMap (Pi.map f) :=
⟨.piMap fun i => (hf i).1, .piMap fun i => (hf i).2, .piMap (fun i => (hf i).3)
    .of_forall fun i => (hf i).1⟩

/--
theorem `tendsto_pi_nhds` / 定理 `tendsto_pi_nhds`

English:
theorem tendsto_pi_nhds
  given: {f : Y -> forall i, A i} {g : forall i, A i} {u : Filter Y}
  proof: by
  rw [nhds_pi]; rw [Filter.tendsto_pi]

中文:
定理 tendsto_pi_nhds
  条件: {f : Y -> 对任意 i, A i} {g : 对任意 i, A i} {u : Filter Y}
  证明: by
  rw [nhds_pi]; rw [Filter.tendsto_pi]

Depends on / 依赖: Filter, Filter.tendsto_pi, nhds_pi, tendsto_pi
-/
theorem tendsto_pi_nhds {f : Y -> forall i, A i} {g : forall i, A i} {u : Filter Y} :
    Tendsto f u (𝓝 g) ↔ forall x, Tendsto (fun i => f i x) u (𝓝 (g x)) := by
  rw [nhds_pi]; rw [Filter.tendsto_pi]

/--
theorem `continuousAt_pi` / 定理 `continuousAt_pi`

English:
theorem continuousAt_pi
  given: {f : X -> forall i, A i} {x : X}
  proof: tendsto_pi_nhds

@[fun_prop]

中文:
定理 continuousAt_pi
  条件: {f : X -> 对任意 i, A i} {x : X}
  证明: tendsto_pi_nhds

@[fun_prop]

Depends on / 依赖: tendsto_pi_nhds
-/
theorem continuousAt_pi {f : X -> forall i, A i} {x : X} :
    ContinuousAt f x ↔ forall i, ContinuousAt (fun y => f y i) x :=
  tendsto_pi_nhds

@[fun_prop]
/--
theorem `continuousAt_pi'` / 定理 `continuousAt_pi'`

English:
theorem continuousAt_pi'
  given: {f : X -> forall i, A i} {x : X} (hf : forall i, ContinuousAt (fun y => f y i) x)
  proof: continuousAt_pi.2 hf

@[fun_prop]

中文:
定理 continuousAt_pi'
  条件: {f : X -> 对任意 i, A i} {x : X} (hf : 对任意 i, ContinuousAt (fun y => f y i) x)
  证明: continuousAt_pi.2 hf

@[fun_prop]

Depends on / 依赖: continuousAt_pi
-/
theorem continuousAt_pi' {f : X -> forall i, A i} {x : X} (hf : forall i, ContinuousAt (fun y => f y i) x) :
    ContinuousAt f x :=
  continuousAt_pi.2 hf

@[fun_prop]
/--
theorem `ContinuousAt.piMap` / 定理 `ContinuousAt.piMap`

English:
theorem ContinuousAt.piMap
  statement: {f : forall i, A i -> B i} {x : forall i, A i}
  proof: continuousAt_pi.2 fun i => (hf i).comp (continuousAt_apply i x)

中文:
定理 ContinuousAt.piMap
  结论: {f : 对任意 i, A i -> B i} {x : 对任意 i, A i}
  证明: continuousAt_pi.2 fun i => (hf i).comp (continuousAt_apply i x)
-/
protected theorem ContinuousAt.piMap {f : forall i, A i -> B i} {x : forall i, A i}
    (hf : forall i, ContinuousAt (f i) (x i)) :
    ContinuousAt (Pi.map f) x :=
  continuousAt_pi.2 fun i => (hf i).comp (continuousAt_apply i x)

/--
lemma `Topology.IsInducing.piMap` / 引理 `Topology.IsInducing.piMap`

English:
lemma Topology.IsInducing.piMap
  statement: {f : forall i, A i -> B i}
  proof: by
  simp [isInducing_iff_nhds, nhds_pi, (hf _).nhds_eq_comap, Filter.pi_comap]

中文:
引理 Topology.IsInducing.piMap
  结论: {f : 对任意 i, A i -> B i}
  证明: by
  simp [isInducing_iff_nhds, nhds_pi, (hf _).nhds_eq_comap, Filter.pi_comap]
-/
protected lemma Topology.IsInducing.piMap {f : forall i, A i -> B i}
    (hf : forall i, IsInducing (f i)) : IsInducing (Pi.map f) := by
  simp [isInducing_iff_nhds, nhds_pi, (hf _).nhds_eq_comap, Filter.pi_comap]

/--
lemma `Topology.IsEmbedding.piMap` / 引理 `Topology.IsEmbedding.piMap`

English:
lemma Topology.IsEmbedding.piMap
  statement: {f : forall i, A i -> B i}
  proof: ⟨.piMap fun i => (hf i).1, .piMap fun i => (hf i).2⟩

中文:
引理 Topology.IsEmbedding.piMap
  结论: {f : 对任意 i, A i -> B i}
  证明: ⟨.piMap fun i => (hf i).1, .piMap fun i => (hf i).2⟩
-/
protected lemma Topology.IsEmbedding.piMap {f : forall i, A i -> B i}
    (hf : forall i, IsEmbedding (f i)) : IsEmbedding (Pi.map f) :=
  ⟨.piMap fun i => (hf i).1, .piMap fun i => (hf i).2⟩

/--
theorem `Pi.continuous_precomp'` / 定理 `Pi.continuous_precomp'`

English:
theorem Pi.continuous_precomp'
  given: {ι' : Type*} (φ : ι' -> ι)
  proof: continuous_pi fun j => continuous_apply (φ j)

中文:
定理 Pi.continuous_precomp'
  条件: {ι' : 类型} (φ : ι' -> ι)
  证明: continuous_pi fun j => continuous_apply (φ j)

Depends on / 依赖: continuous_apply, continuous_pi
-/
theorem Pi.continuous_precomp' {ι' : Type*} (φ : ι' -> ι) :
    Continuous (fun (f : (forall i, A i)) (j : ι') => f (φ j)) :=
  continuous_pi fun j => continuous_apply (φ j)

/--
theorem `Pi.continuous_precomp` / 定理 `Pi.continuous_precomp`

English:
theorem Pi.continuous_precomp
  given: {ι' : Type*} (φ : ι' -> ι)
  proof: Pi.continuous_precomp' φ

中文:
定理 Pi.continuous_precomp
  条件: {ι' : 类型} (φ : ι' -> ι)
  证明: Pi.continuous_precomp' φ

Depends on / 依赖: Pi.continuous_precomp, continuous_precomp
-/
theorem Pi.continuous_precomp {ι' : Type*} (φ : ι' -> ι) :
    Continuous (· ∘ φ : (ι -> X) -> (ι' -> X)) :=
  Pi.continuous_precomp' φ

/--
theorem `Pi.continuous_postcomp'` / 定理 `Pi.continuous_postcomp'`

English:
theorem Pi.continuous_postcomp'
  statement: {X : ι -> Type*} [forall i, TopologicalSpace (X i)]
  proof: continuous_pi fun i => (hg i).comp continuous_apply i

中文:
定理 Pi.continuous_postcomp'
  结论: {X : ι -> 类型} [对任意 i, TopologicalSpace (X i)]
  证明: continuous_pi fun i => (hg i).comp continuous_apply i

Depends on / 依赖: continuous_apply, continuous_pi
-/
theorem Pi.continuous_postcomp' {X : ι -> Type*} [forall i, TopologicalSpace (X i)]
    {g : forall i, A i -> X i} (hg : forall i, Continuous (g i)) :
    Continuous (fun (f : (forall i, A i)) (i : ι) => g i (f i)) :=
continuous_pi fun i => (hg i).comp continuous_apply i

/--
theorem `Pi.continuous_postcomp` / 定理 `Pi.continuous_postcomp`

English:
theorem Pi.continuous_postcomp
  given: [TopologicalSpace Y] {g : X -> Y} (hg : Continuous g)
  proof: Pi.continuous_postcomp' fun _ => hg

中文:
定理 Pi.continuous_postcomp
  条件: [TopologicalSpace Y] {g : X -> Y} (hg : Continuous g)
  证明: Pi.continuous_postcomp' fun _ => hg

Depends on / 依赖: Pi.continuous_postcomp, continuous_postcomp
-/
theorem Pi.continuous_postcomp [TopologicalSpace Y] {g : X -> Y} (hg : Continuous g) :
    Continuous (g ∘ · : (ι -> X) -> (ι -> Y)) :=
  Pi.continuous_postcomp' fun _ => hg

/--
lemma `Pi.induced_precomp'` / 引理 `Pi.induced_precomp'`

English:
lemma Pi.induced_precomp'
  given: {ι' : Type*} (φ : ι' -> ι)
  proof: by
  simp [Pi.topologicalSpace, induced_iInf, induced_compose, comp_def]

中文:
引理 Pi.induced_precomp'
  条件: {ι' : 类型} (φ : ι' -> ι)
  证明: by
  simp [Pi.topologicalSpace, induced_iInf, induced_compose, comp_def]

Depends on / 依赖: Pi.topologicalSpace, comp_def, induced_compose, induced_iInf, topologicalSpace
-/
lemma Pi.induced_precomp' {ι' : Type*} (φ : ι' -> ι) :
    induced (fun (f : (forall i, A i)) (j : ι') => f (φ j)) Pi.topologicalSpace =
    ⨅ i', induced (eval (φ i')) (T (φ i')) := by
  simp [Pi.topologicalSpace, induced_iInf, induced_compose, comp_def]

/--
lemma `Pi.induced_precomp` / 引理 `Pi.induced_precomp`

English:
lemma Pi.induced_precomp
  given: [TopologicalSpace Y] {ι' : Type*} (φ : ι' -> ι)
  proof: induced_precomp' φ

中文:
引理 Pi.induced_precomp
  条件: [TopologicalSpace Y] {ι' : 类型} (φ : ι' -> ι)
  证明: induced_precomp' φ

Depends on / 依赖: induced_precomp
-/
lemma Pi.induced_precomp [TopologicalSpace Y] {ι' : Type*} (φ : ι' -> ι) :
    induced (· ∘ φ) Pi.topologicalSpace =
    ⨅ i', induced (eval (φ i')) ‹TopologicalSpace Y› :=
  induced_precomp' φ

/-- Homeomorphism between `X → Y → Z` and `X × Y → Z` with product topologies. -/
@[simps]
/--
Definition of `Homeomorph.piCurry` / `Homeomorph.piCurry` 的定义

English:
definition Homeomorph.piCurry
  signature: {X Y Z : Type*}
  body: Function.curry
  invFun := Function.uncurry
  right_inv := congrFun rfl
  left_inv := congrFun rfl
  continuous_toFun := continuous_pi (fun i => Pi.continuous_precomp (Prod.mk i))

@[continuity, fun_prop]

中文:
定义 Homeomorph.piCurry
  签名: {X Y Z : 类型}
  定义体: Function.curry
  invFun := Function.uncurry
  right_inv := congrFun rfl
  left_inv := congrFun rfl
  continuous_toFun := continuous_pi (fun i => Pi.continuous_precomp (Prod.mk i))

@[continuity, fun_prop]

Depends on / 依赖: Function, Function.curry
-/
def Homeomorph.piCurry {X Y Z : Type*}
    [TopologicalSpace Z] :
    (X × Y -> Z) ≃ₜ (X -> Y -> Z) where
  toFun := Function.curry
  invFun := Function.uncurry
  right_inv := congrFun rfl
  left_inv := congrFun rfl
  continuous_toFun := continuous_pi (fun i => Pi.continuous_precomp (Prod.mk i))

@[continuity, fun_prop]
/--
lemma `Pi.continuous_domRestrict` / 引理 `Pi.continuous_domRestrict`

English:
lemma Pi.continuous_domRestrict
  given: (S : Set ι)
  proof: Pi.continuous_precomp' ((↑) : S -> ι)

@[deprecated (since := "2026-07-19")] alias Pi.continuous_restrict := Pi.continuous_domRestrict

@[continuity, fun_prop]

中文:
引理 Pi.continuous_domRestrict
  条件: (S : Set ι)
  证明: Pi.continuous_precomp' ((↑) : S -> ι)

@[deprecated (since := "2026-07-19")] alias Pi.continuous_restrict := Pi.continuous_domRestrict

@[continuity, fun_prop]

Depends on / 依赖: Pi.continuous_precomp, continuous_precomp
-/
lemma Pi.continuous_domRestrict (S : Set ι) :
    Continuous (S.domRestrict : (forall i : ι, A i) -> (forall i : S, A i)) :=
  Pi.continuous_precomp' ((↑) : S -> ι)

@[deprecated (since := "2026-07-19")] alias Pi.continuous_restrict := Pi.continuous_domRestrict

@[continuity, fun_prop]
/--
lemma `Pi.continuous_domRestrict₂` / 引理 `Pi.continuous_domRestrict₂`

English:
lemma Pi.continuous_domRestrict₂
  given: {s t : Set ι} (hst : s subseteq t)
  proof: continuous_pi fun _ => continuous_apply _

@[deprecated (since := "2026-07-19")] alias Pi.continuous_restrict₂ := Pi.continuous_domRestrict₂

@[continuity, fun_prop]

中文:
引理 Pi.continuous_domRestrict₂
  条件: {s t : Set ι} (hst : s subseteq t)
  证明: continuous_pi fun _ => continuous_apply _

@[deprecated (since := "2026-07-19")] alias Pi.continuous_restrict₂ := Pi.continuous_domRestrict₂

@[continuity, fun_prop]

Depends on / 依赖: continuous_apply, continuous_pi
-/
lemma Pi.continuous_domRestrict₂ {s t : Set ι} (hst : s subseteq t) :
    Continuous (domRestrict₂ (π := A) hst) := continuous_pi fun _ => continuous_apply _

@[deprecated (since := "2026-07-19")] alias Pi.continuous_restrict₂ := Pi.continuous_domRestrict₂

@[continuity, fun_prop]
/--
theorem `Finset.continuous_restrict` / 定理 `Finset.continuous_restrict`

English:
theorem Finset.continuous_restrict
  given: (s : Finset ι)
  statement: Continuous (s.restrict (π := A))
  proof: continuous_pi fun _ => continuous_apply _

@[continuity, fun_prop]

中文:
定理 Finset.continuous_restrict
  条件: (s : Finset ι)
  结论: Continuous (s.restrict (π := A))
  证明: continuous_pi fun _ => continuous_apply _

@[continuity, fun_prop]
-/
theorem Finset.continuous_restrict (s : Finset ι) : Continuous (s.restrict (π := A)) :=
  continuous_pi fun _ => continuous_apply _

@[continuity, fun_prop]
/--
theorem `Finset.continuous_restrict₂` / 定理 `Finset.continuous_restrict₂`

English:
theorem Finset.continuous_restrict₂
  given: {s t : Finset ι} (hst : s subseteq t)
  proof: continuous_pi fun _ => continuous_apply _

中文:
定理 Finset.continuous_restrict₂
  条件: {s t : Finset ι} (hst : s subseteq t)
  证明: continuous_pi fun _ => continuous_apply _
-/
theorem Finset.continuous_restrict₂ {s t : Finset ι} (hst : s subseteq t) :
    Continuous (Finset.restrict₂ (π := A) hst) :=
  continuous_pi fun _ => continuous_apply _

variable [TopologicalSpace Z]

@[continuity, fun_prop]
/--
theorem `Pi.continuous_domRestrict_apply` / 定理 `Pi.continuous_domRestrict_apply`

English:
theorem Pi.continuous_domRestrict_apply
  given: (s : Set X) {f : X -> Z} (hf : Continuous f)
  proof: hf.comp continuous_subtype_val

@[deprecated (since := "2026-07-19")]
alias Pi.continuous_restrict_apply := Pi.continuous_domRestrict_apply

@[continuity, fun_prop]

中文:
定理 Pi.continuous_domRestrict_apply
  条件: (s : Set X) {f : X -> Z} (hf : Continuous f)
  证明: hf.comp continuous_subtype_val

@[deprecated (since := "2026-07-19")]
alias Pi.continuous_restrict_apply := Pi.continuous_domRestrict_apply

@[continuity, fun_prop]

Depends on / 依赖: continuous_subtype_val, hf.comp
-/
theorem Pi.continuous_domRestrict_apply (s : Set X) {f : X -> Z} (hf : Continuous f) :
    Continuous (s.domRestrict f) := hf.comp continuous_subtype_val

@[deprecated (since := "2026-07-19")]
alias Pi.continuous_restrict_apply := Pi.continuous_domRestrict_apply

@[continuity, fun_prop]
/--
theorem `Pi.continuous_domRestrict₂_apply` / 定理 `Pi.continuous_domRestrict₂_apply`

English:
theorem Pi.continuous_domRestrict₂_apply
  statement: {s t : Set X} (hst : s subseteq t)
  proof: hf.comp (continuous_inclusion hst)

@[deprecated (since := "2026-07-19")]
alias Pi.continuous_restrict₂_apply := Pi.continuous_domRestrict₂_apply

@[continuity, fun_prop]

中文:
定理 Pi.continuous_domRestrict₂_apply
  结论: {s t : Set X} (hst : s subseteq t)
  证明: hf.comp (continuous_inclusion hst)

@[deprecated (since := "2026-07-19")]
alias Pi.continuous_restrict₂_apply := Pi.continuous_domRestrict₂_apply

@[continuity, fun_prop]

Depends on / 依赖: continuous_inclusion, hf.comp
-/
theorem Pi.continuous_domRestrict₂_apply {s t : Set X} (hst : s subseteq t)
    {f : t -> Z} (hf : Continuous f) :
    Continuous (domRestrict₂ (π := fun _ => Z) hst f) := hf.comp (continuous_inclusion hst)

@[deprecated (since := "2026-07-19")]
alias Pi.continuous_restrict₂_apply := Pi.continuous_domRestrict₂_apply

@[continuity, fun_prop]
/--
theorem `Finset.continuous_restrict_apply` / 定理 `Finset.continuous_restrict_apply`

English:
theorem Finset.continuous_restrict_apply
  given: (s : Finset X) {f : X -> Z} (hf : Continuous f)
  proof: hf.comp continuous_subtype_val

@[continuity, fun_prop]

中文:
定理 Finset.continuous_restrict_apply
  条件: (s : Finset X) {f : X -> Z} (hf : Continuous f)
  证明: hf.comp continuous_subtype_val

@[continuity, fun_prop]

Depends on / 依赖: continuous_subtype_val, hf.comp
-/
theorem Finset.continuous_restrict_apply (s : Finset X) {f : X -> Z} (hf : Continuous f) :
    Continuous (s.restrict f) := hf.comp continuous_subtype_val

@[continuity, fun_prop]
/--
theorem `Finset.continuous_restrict₂_apply` / 定理 `Finset.continuous_restrict₂_apply`

English:
theorem Finset.continuous_restrict₂_apply
  statement: {s t : Finset X} (hst : s subseteq t)
  proof: hf.comp (continuous_inclusion hst)

中文:
定理 Finset.continuous_restrict₂_apply
  结论: {s t : Finset X} (hst : s subseteq t)
  证明: hf.comp (continuous_inclusion hst)

Depends on / 依赖: continuous_inclusion, hf.comp
-/
theorem Finset.continuous_restrict₂_apply {s t : Finset X} (hst : s subseteq t)
    {f : t -> Z} (hf : Continuous f) :
    Continuous (restrict₂ (π := fun _ => Z) hst f) := hf.comp (continuous_inclusion hst)

/--
lemma `Pi.induced_domRestrict` / 引理 `Pi.induced_domRestrict`

English:
lemma Pi.induced_domRestrict
  given: (S : Set ι)
  proof: by
  simp +unfoldPartialApp [← iInf_subtype'', ← induced_precomp' ((↑) : S -> ι),
    domRestrict]

@[deprecated (since := "2026-07-19")] alias Pi.induced_restrict := Pi.induced_domRestrict

中文:
引理 Pi.induced_domRestrict
  条件: (S : Set ι)
  证明: by
  simp +unfoldPartialApp [← iInf_subtype'', ← induced_precomp' ((↑) : S -> ι),
    domRestrict]

@[deprecated (since := "2026-07-19")] alias Pi.induced_restrict := Pi.induced_domRestrict

Depends on / 依赖: domRestrict, iInf_subtype, induced_precomp, unfoldPartialApp
-/
lemma Pi.induced_domRestrict (S : Set ι) :
    induced (S.domRestrict) Pi.topologicalSpace =
    ⨅ i in S, induced (eval i) (T i) := by
  simp +unfoldPartialApp [← iInf_subtype'', ← induced_precomp' ((↑) : S -> ι),
    domRestrict]

@[deprecated (since := "2026-07-19")] alias Pi.induced_restrict := Pi.induced_domRestrict

/--
lemma `Pi.induced_domRestrict_sUnion` / 引理 `Pi.induced_domRestrict_sUnion`

English:
lemma Pi.induced_domRestrict_sUnion
  given: (𝔖 : Set (Set ι))
  proof: by
  simp_rw [Pi.induced_domRestrict, iInf_sUnion]

@[deprecated (since := "2026-07-19")]
alias Pi.induced_restrict_sUnion := Pi.induced_domRestrict_sUnion

中文:
引理 Pi.induced_domRestrict_sUnion
  条件: (𝔖 : Set (Set ι))
  证明: by
  simp_rw [Pi.induced_domRestrict, iInf_sUnion]

@[deprecated (since := "2026-07-19")]
alias Pi.induced_restrict_sUnion := Pi.induced_domRestrict_sUnion
-/
lemma Pi.induced_domRestrict_sUnion (𝔖 : Set (Set ι)) :
    induced (⋃₀ 𝔖).domRestrict (Pi.topologicalSpace (Y := fun i : (⋃₀ 𝔖) => A i)) =
    ⨅ S in 𝔖, induced S.domRestrict Pi.topologicalSpace := by
  simp_rw [Pi.induced_domRestrict, iInf_sUnion]

@[deprecated (since := "2026-07-19")]
alias Pi.induced_restrict_sUnion := Pi.induced_domRestrict_sUnion

/--
theorem `Filter.Tendsto.update` / 定理 `Filter.Tendsto.update`

English:
theorem Filter.Tendsto.update
  statement: [DecidableEq ι] {l : Filter Y} {f : Y -> forall i, A i} {x : forall i, A i}
  proof: tendsto_pi_nhds.2 fun j => by rcases eq_or_ne j i with (rfl | hj) <;> simp [*, hf.apply_nhds]

@[fun_prop]

中文:
定理 Filter.Tendsto.update
  结论: [DecidableEq ι] {l : Filter Y} {f : Y -> 对任意 i, A i} {x : 对任意 i, A i}
  证明: tendsto_pi_nhds.2 fun j => by rcases eq_or_ne j i with (rfl | hj) <;> simp [*, hf.apply_nhds]

@[fun_prop]

Depends on / 依赖: apply_nhds, eq_or_ne, hf.apply_nhds, tendsto_pi_nhds
-/
theorem Filter.Tendsto.update [DecidableEq ι] {l : Filter Y} {f : Y -> forall i, A i} {x : forall i, A i}
    (hf : Tendsto f l (𝓝 x)) (i : ι) {g : Y -> A i} {xi : A i} (hg : Tendsto g l (𝓝 xi)) :
    Tendsto (fun a => update (f a) i (g a)) l (𝓝 <| update x i xi) :=
  tendsto_pi_nhds.2 fun j => by rcases eq_or_ne j i with (rfl | hj) <;> simp [*, hf.apply_nhds]

@[fun_prop]
/--
theorem `ContinuousAt.update` / 定理 `ContinuousAt.update`

English:
theorem ContinuousAt.update
  statement: [DecidableEq ι] {x : X} (hf : ContinuousAt f x) (i : ι) {g : X -> A i}
  proof: hf.tendsto.update i hg

@[fun_prop]

中文:
定理 ContinuousAt.update
  结论: [DecidableEq ι] {x : X} (hf : ContinuousAt f x) (i : ι) {g : X -> A i}
  证明: hf.tendsto.update i hg

@[fun_prop]

Depends on / 依赖: hf.tendsto.update, tendsto, update
-/
theorem ContinuousAt.update [DecidableEq ι] {x : X} (hf : ContinuousAt f x) (i : ι) {g : X -> A i}
    (hg : ContinuousAt g x) : ContinuousAt (fun a => update (f a) i (g a)) x :=
  hf.tendsto.update i hg

@[fun_prop]
/--
theorem `Continuous.update` / 定理 `Continuous.update`

English:
theorem Continuous.update
  statement: [DecidableEq ι] (hf : Continuous f) (i : ι) {g : X -> A i}
  proof: continuous_iff_continuousAt.2 fun _ => hf.continuousAt.update i hg.continuousAt

中文:
定理 Continuous.update
  结论: [DecidableEq ι] (hf : Continuous f) (i : ι) {g : X -> A i}
  证明: continuous_iff_continuousAt.2 fun _ => hf.continuousAt.update i hg.continuousAt

Depends on / 依赖: continuousAt, continuous_iff_continuousAt, hf.continuousAt.update, hg.continuousAt, update
-/
theorem Continuous.update [DecidableEq ι] (hf : Continuous f) (i : ι) {g : X -> A i}
    (hg : Continuous g) : Continuous fun a => update (f a) i (g a) :=
  continuous_iff_continuousAt.2 fun _ => hf.continuousAt.update i hg.continuousAt

/-- `Function.update f i x` is continuous in `(f, x)`. -/
@[continuity, fun_prop]
/--
theorem `continuous_update` / 定理 `continuous_update`

English:
theorem continuous_update
  given: [DecidableEq ι] (i : ι)
  proof: continuous_fst.update i continuous_snd

中文:
定理 continuous_update
  条件: [DecidableEq ι] (i : ι)
  证明: continuous_fst.update i continuous_snd

Depends on / 依赖: continuous_fst, continuous_fst.update, continuous_snd, update
-/
theorem continuous_update [DecidableEq ι] (i : ι) :
    Continuous fun f : (forall j, A j) × A i => update f.1 i f.2 :=
  continuous_fst.update i continuous_snd

/-- `Pi.mulSingle i x` is continuous in `x`. -/
@[to_additive (attr := continuity, fun_prop) /-- `Pi.single i x` is continuous in `x`. -/]
/--
theorem `continuous_mulSingle` / 定理 `continuous_mulSingle`

English:
theorem continuous_mulSingle
  given: [forall i, One (A i)] [DecidableEq ι] (i : ι)
  proof: continuous_const.update _ continuous_id

中文:
定理 continuous_mulSingle
  条件: [对任意 i, One (A i)] [DecidableEq ι] (i : ι)
  证明: continuous_const.update _ continuous_id

Depends on / 依赖: continuous_const, continuous_const.update, continuous_id, update
-/
theorem continuous_mulSingle [forall i, One (A i)] [DecidableEq ι] (i : ι) :
    Continuous fun x => (Pi.mulSingle i x : forall i, A i) :=
  continuous_const.update _ continuous_id

section Fin
variable {n : Nat} {A : Fin (n + 1) -> Type*} [forall i, TopologicalSpace (A i)]

/--
theorem `Filter.Tendsto.finCons` / 定理 `Filter.Tendsto.finCons`

English:
theorem Filter.Tendsto.finCons
  proof: tendsto_pi_nhds.2 fun j => Fin.cases (by simpa) (by simpa using tendsto_pi_nhds.1 hg) j

@[fun_prop]

中文:
定理 Filter.Tendsto.finCons
  证明: tendsto_pi_nhds.2 fun j => Fin.cases (by simpa) (by simpa using tendsto_pi_nhds.1 hg) j

@[fun_prop]

Depends on / 依赖: Fin.cases, tendsto_pi_nhds
-/
theorem Filter.Tendsto.finCons
    {f : Y -> A 0} {g : Y -> forall j : Fin n, A j.succ} {l : Filter Y} {x : A 0} {y : forall j, A (Fin.succ j)}
    (hf : Tendsto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) :
    Tendsto (fun a => Fin.cons (f a) (g a)) l (𝓝 <| Fin.cons x y) :=
  tendsto_pi_nhds.2 fun j => Fin.cases (by simpa) (by simpa using tendsto_pi_nhds.1 hg) j

@[fun_prop]
/--
theorem `ContinuousAt.finCons` / 定理 `ContinuousAt.finCons`

English:
theorem ContinuousAt.finCons
  statement: {f : X -> A 0} {g : X -> forall j : Fin n, A (Fin.succ j)} {x : X}
  proof: hf.tendsto.finCons hg

@[fun_prop]

中文:
定理 ContinuousAt.finCons
  结论: {f : X -> A 0} {g : X -> 对任意 j : Fin n, A (Fin.succ j)} {x : X}
  证明: hf.tendsto.finCons hg

@[fun_prop]

Depends on / 依赖: finCons, hf.tendsto.finCons, tendsto
-/
theorem ContinuousAt.finCons {f : X -> A 0} {g : X -> forall j : Fin n, A (Fin.succ j)} {x : X}
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (fun a => Fin.cons (f a) (g a)) x :=
  hf.tendsto.finCons hg

@[fun_prop]
/--
theorem `Continuous.finCons` / 定理 `Continuous.finCons`

English:
theorem Continuous.finCons
  statement: {f : X -> A 0} {g : X -> forall j : Fin n, A (Fin.succ j)}
  proof: continuous_iff_continuousAt.2 fun _ => hf.continuousAt.finCons hg.continuousAt

中文:
定理 Continuous.finCons
  结论: {f : X -> A 0} {g : X -> 对任意 j : Fin n, A (Fin.succ j)}
  证明: continuous_iff_continuousAt.2 fun _ => hf.continuousAt.finCons hg.continuousAt

Depends on / 依赖: continuousAt, continuous_iff_continuousAt, finCons, hf.continuousAt.finCons, hg.continuousAt
-/
theorem Continuous.finCons {f : X -> A 0} {g : X -> forall j : Fin n, A (Fin.succ j)}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun a => Fin.cons (f a) (g a) :=
  continuous_iff_continuousAt.2 fun _ => hf.continuousAt.finCons hg.continuousAt

/--
theorem `Filter.Tendsto.matrixVecCons` / 定理 `Filter.Tendsto.matrixVecCons`

English:
theorem Filter.Tendsto.matrixVecCons
  proof: hf.finCons hg

@[fun_prop]

中文:
定理 Filter.Tendsto.matrixVecCons
  证明: hf.finCons hg

@[fun_prop]

Depends on / 依赖: finCons, hf.finCons
-/
theorem Filter.Tendsto.matrixVecCons
    {f : Y -> Z} {g : Y -> Fin n -> Z} {l : Filter Y} {x : Z} {y : Fin n -> Z}
    (hf : Tendsto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) :
    Tendsto (fun a => Matrix.vecCons (f a) (g a)) l (𝓝 <| Matrix.vecCons x y) :=
  hf.finCons hg

@[fun_prop]
/--
theorem `ContinuousAt.matrixVecCons` / 定理 `ContinuousAt.matrixVecCons`

English:
theorem ContinuousAt.matrixVecCons
  proof: hf.finCons hg

@[fun_prop]

中文:
定理 ContinuousAt.matrixVecCons
  证明: hf.finCons hg

@[fun_prop]

Depends on / 依赖: finCons, hf.finCons
-/
theorem ContinuousAt.matrixVecCons
    {f : X -> Z} {g : X -> Fin n -> Z} {x : X} (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (fun a => Matrix.vecCons (f a) (g a)) x :=
  hf.finCons hg

@[fun_prop]
/--
theorem `Continuous.matrixVecCons` / 定理 `Continuous.matrixVecCons`

English:
theorem Continuous.matrixVecCons
  proof: hf.finCons hg

中文:
定理 Continuous.matrixVecCons
  证明: hf.finCons hg

Depends on / 依赖: finCons, hf.finCons
-/
theorem Continuous.matrixVecCons
    {f : X -> Z} {g : X -> Fin n -> Z} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun a => Matrix.vecCons (f a) (g a) :=
  hf.finCons hg

/--
theorem `Filter.Tendsto.finSnoc` / 定理 `Filter.Tendsto.finSnoc`

English:
theorem Filter.Tendsto.finSnoc
  proof: tendsto_pi_nhds.2 fun j => Fin.lastCases (by simpa) (by simpa using tendsto_pi_nhds.1 hf) j

@[fun_prop]

中文:
定理 Filter.Tendsto.finSnoc
  证明: tendsto_pi_nhds.2 fun j => Fin.lastCases (by simpa) (by simpa using tendsto_pi_nhds.1 hf) j

@[fun_prop]

Depends on / 依赖: Fin.lastCases, lastCases, tendsto_pi_nhds
-/
theorem Filter.Tendsto.finSnoc
    {f : Y -> forall j : Fin n, A j.castSucc} {g : Y -> A (Fin.last _)}
    {l : Filter Y} {x : forall j, A (Fin.castSucc j)} {y : A (Fin.last _)}
    (hf : Tendsto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) :
    Tendsto (fun a => Fin.snoc (f a) (g a)) l (𝓝 <| Fin.snoc x y) :=
  tendsto_pi_nhds.2 fun j => Fin.lastCases (by simpa) (by simpa using tendsto_pi_nhds.1 hf) j

@[fun_prop]
/--
theorem `ContinuousAt.finSnoc` / 定理 `ContinuousAt.finSnoc`

English:
theorem ContinuousAt.finSnoc
  statement: {f : X -> forall j : Fin n, A j.castSucc} {g : X -> A (Fin.last _)} {x : X}
  proof: hf.tendsto.finSnoc hg

@[fun_prop]

中文:
定理 ContinuousAt.finSnoc
  结论: {f : X -> 对任意 j : Fin n, A j.castSucc} {g : X -> A (Fin.last _)} {x : X}
  证明: hf.tendsto.finSnoc hg

@[fun_prop]

Depends on / 依赖: finSnoc, hf.tendsto.finSnoc, tendsto
-/
theorem ContinuousAt.finSnoc {f : X -> forall j : Fin n, A j.castSucc} {g : X -> A (Fin.last _)} {x : X}
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (fun a => Fin.snoc (f a) (g a)) x :=
  hf.tendsto.finSnoc hg

@[fun_prop]
/--
theorem `Continuous.finSnoc` / 定理 `Continuous.finSnoc`

English:
theorem Continuous.finSnoc
  statement: {f : X -> forall j : Fin n, A j.castSucc} {g : X -> A (Fin.last _)}
  proof: continuous_iff_continuousAt.2 fun _ => hf.continuousAt.finSnoc hg.continuousAt

中文:
定理 Continuous.finSnoc
  结论: {f : X -> 对任意 j : Fin n, A j.castSucc} {g : X -> A (Fin.last _)}
  证明: continuous_iff_continuousAt.2 fun _ => hf.continuousAt.finSnoc hg.continuousAt

Depends on / 依赖: continuousAt, continuous_iff_continuousAt, finSnoc, hf.continuousAt.finSnoc, hg.continuousAt
-/
theorem Continuous.finSnoc {f : X -> forall j : Fin n, A j.castSucc} {g : X -> A (Fin.last _)}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun a => Fin.snoc (f a) (g a) :=
  continuous_iff_continuousAt.2 fun _ => hf.continuousAt.finSnoc hg.continuousAt

/--
theorem `Filter.Tendsto.finInsertNth` / 定理 `Filter.Tendsto.finInsertNth`

English:
theorem Filter.Tendsto.finInsertNth
  proof: tendsto_pi_nhds.2 fun j => Fin.succAboveCases i (by simpa) (by simpa using tendsto_pi_nhds.1 hg) j

@[fun_prop]

中文:
定理 Filter.Tendsto.finInsertNth
  证明: tendsto_pi_nhds.2 fun j => Fin.succAboveCases i (by simpa) (by simpa using tendsto_pi_nhds.1 hg) j

@[fun_prop]

Depends on / 依赖: Fin.succAboveCases, succAboveCases, tendsto_pi_nhds
-/
theorem Filter.Tendsto.finInsertNth
    (i : Fin (n + 1)) {f : Y -> A i} {g : Y -> forall j : Fin n, A (i.succAbove j)} {l : Filter Y}
    {x : A i} {y : forall j, A (i.succAbove j)} (hf : Tendsto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) :
    Tendsto (fun a => i.insertNth (f a) (g a)) l (𝓝 <| i.insertNth x y) :=
  tendsto_pi_nhds.2 fun j => Fin.succAboveCases i (by simpa) (by simpa using tendsto_pi_nhds.1 hg) j

@[fun_prop]
/--
theorem `ContinuousAt.finInsertNth` / 定理 `ContinuousAt.finInsertNth`

English:
theorem ContinuousAt.finInsertNth
  proof: hf.tendsto.finInsertNth i hg

@[fun_prop]

中文:
定理 ContinuousAt.finInsertNth
  证明: hf.tendsto.finInsertNth i hg

@[fun_prop]

Depends on / 依赖: finInsertNth, hf.tendsto.finInsertNth, tendsto
-/
theorem ContinuousAt.finInsertNth
    (i : Fin (n + 1)) {f : X -> A i} {g : X -> forall j : Fin n, A (i.succAbove j)} {x : X}
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (fun a => i.insertNth (f a) (g a)) x :=
  hf.tendsto.finInsertNth i hg

@[fun_prop]
/--
theorem `Continuous.finInsertNth` / 定理 `Continuous.finInsertNth`

English:
theorem Continuous.finInsertNth
  proof: continuous_iff_continuousAt.2 fun _ => hf.continuousAt.finInsertNth i hg.continuousAt

中文:
定理 Continuous.finInsertNth
  证明: continuous_iff_continuousAt.2 fun _ => hf.continuousAt.finInsertNth i hg.continuousAt

Depends on / 依赖: continuousAt, continuous_iff_continuousAt, finInsertNth, hf.continuousAt.finInsertNth, hg.continuousAt
-/
theorem Continuous.finInsertNth
    (i : Fin (n + 1)) {f : X -> A i} {g : X -> forall j : Fin n, A (i.succAbove j)}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun a => i.insertNth (f a) (g a) :=
  continuous_iff_continuousAt.2 fun _ => hf.continuousAt.finInsertNth i hg.continuousAt

/--
theorem `Filter.Tendsto.finInit` / 定理 `Filter.Tendsto.finInit`

English:
theorem Filter.Tendsto.finInit
  statement: {f : Y -> forall j : Fin (n + 1), A j} {l : Filter Y} {x : forall j, A j}
  proof: tendsto_pi_nhds.2 fun j => apply_nhds hg j.castSucc

@[fun_prop]

中文:
定理 Filter.Tendsto.finInit
  结论: {f : Y -> 对任意 j : Fin (n + 1), A j} {l : Filter Y} {x : 对任意 j, A j}
  证明: tendsto_pi_nhds.2 fun j => apply_nhds hg j.castSucc

@[fun_prop]

Depends on / 依赖: apply_nhds, castSucc, j.castSucc, tendsto_pi_nhds
-/
theorem Filter.Tendsto.finInit {f : Y -> forall j : Fin (n + 1), A j} {l : Filter Y} {x : forall j, A j}
    (hg : Tendsto f l (𝓝 x)) : Tendsto (fun a => Fin.init (f a)) l (𝓝 <| Fin.init x) :=
  tendsto_pi_nhds.2 fun j => apply_nhds hg j.castSucc

@[fun_prop]
/--
theorem `ContinuousAt.finInit` / 定理 `ContinuousAt.finInit`

English:
theorem ContinuousAt.finInit
  statement: {f : X -> forall j : Fin (n + 1), A j} {x : X}
  proof: hf.tendsto.finInit

@[fun_prop]

中文:
定理 ContinuousAt.finInit
  结论: {f : X -> 对任意 j : Fin (n + 1), A j} {x : X}
  证明: hf.tendsto.finInit

@[fun_prop]

Depends on / 依赖: finInit, hf.tendsto.finInit, tendsto
-/
theorem ContinuousAt.finInit {f : X -> forall j : Fin (n + 1), A j} {x : X}
    (hf : ContinuousAt f x) : ContinuousAt (fun a => Fin.init (f a)) x :=
  hf.tendsto.finInit

@[fun_prop]
/--
theorem `Continuous.finInit` / 定理 `Continuous.finInit`

English:
theorem Continuous.finInit
  given: {f : X -> forall j : Fin (n + 1), A j} (hf : Continuous f)
  proof: continuous_iff_continuousAt.2 fun _ => hf.continuousAt.finInit

中文:
定理 Continuous.finInit
  条件: {f : X -> 对任意 j : Fin (n + 1), A j} (hf : Continuous f)
  证明: continuous_iff_continuousAt.2 fun _ => hf.continuousAt.finInit

Depends on / 依赖: continuousAt, continuous_iff_continuousAt, finInit, hf.continuousAt.finInit
-/
theorem Continuous.finInit {f : X -> forall j : Fin (n + 1), A j} (hf : Continuous f) :
    Continuous fun a => Fin.init (f a) :=
  continuous_iff_continuousAt.2 fun _ => hf.continuousAt.finInit

/--
theorem `Filter.Tendsto.finTail` / 定理 `Filter.Tendsto.finTail`

English:
theorem Filter.Tendsto.finTail
  statement: {f : Y -> forall j : Fin (n + 1), A j} {l : Filter Y} {x : forall j, A j}
  proof: tendsto_pi_nhds.2 fun j => apply_nhds hg j.succ

@[fun_prop]

中文:
定理 Filter.Tendsto.finTail
  结论: {f : Y -> 对任意 j : Fin (n + 1), A j} {l : Filter Y} {x : 对任意 j, A j}
  证明: tendsto_pi_nhds.2 fun j => apply_nhds hg j.succ

@[fun_prop]

Depends on / 依赖: apply_nhds, j.succ, tendsto_pi_nhds
-/
theorem Filter.Tendsto.finTail {f : Y -> forall j : Fin (n + 1), A j} {l : Filter Y} {x : forall j, A j}
    (hg : Tendsto f l (𝓝 x)) : Tendsto (fun a => Fin.tail (f a)) l (𝓝 <| Fin.tail x) :=
  tendsto_pi_nhds.2 fun j => apply_nhds hg j.succ

@[fun_prop]
/--
theorem `ContinuousAt.finTail` / 定理 `ContinuousAt.finTail`

English:
theorem ContinuousAt.finTail
  statement: {f : X -> forall j : Fin (n + 1), A j} {x : X}
  proof: hf.tendsto.finTail

@[fun_prop]

中文:
定理 ContinuousAt.finTail
  结论: {f : X -> 对任意 j : Fin (n + 1), A j} {x : X}
  证明: hf.tendsto.finTail

@[fun_prop]

Depends on / 依赖: finTail, hf.tendsto.finTail, tendsto
-/
theorem ContinuousAt.finTail {f : X -> forall j : Fin (n + 1), A j} {x : X}
    (hf : ContinuousAt f x) : ContinuousAt (fun a => Fin.tail (f a)) x :=
  hf.tendsto.finTail

@[fun_prop]
/--
theorem `Continuous.finTail` / 定理 `Continuous.finTail`

English:
theorem Continuous.finTail
  given: {f : X -> forall j : Fin (n + 1), A j} (hf : Continuous f)
  proof: continuous_iff_continuousAt.2 fun _ => hf.continuousAt.finTail

中文:
定理 Continuous.finTail
  条件: {f : X -> 对任意 j : Fin (n + 1), A j} (hf : Continuous f)
  证明: continuous_iff_continuousAt.2 fun _ => hf.continuousAt.finTail

Depends on / 依赖: continuousAt, continuous_iff_continuousAt, finTail, hf.continuousAt.finTail
-/
theorem Continuous.finTail {f : X -> forall j : Fin (n + 1), A j} (hf : Continuous f) :
    Continuous fun a => Fin.tail (f a) :=
  continuous_iff_continuousAt.2 fun _ => hf.continuousAt.finTail

end Fin

/--
theorem `isOpen_set_pi` / 定理 `isOpen_set_pi`

English:
theorem isOpen_set_pi
  statement: {i : Set ι} {s : forall a, Set (A a)} (hi : i.Finite)
  proof: by
  rw [pi_def]; exact hi.isOpen_biInter fun a ha => (hs _ ha).preimage (continuous_apply _)

中文:
定理 isOpen_set_pi
  结论: {i : Set ι} {s : 对任意 a, Set (A a)} (hi : i.Finite)
  证明: by
  rw [pi_def]; exact hi.isOpen_biInter fun a ha => (hs _ ha).preimage (continuous_apply _)

Depends on / 依赖: continuous_apply, hi.isOpen_biInter, isOpen_biInter, pi_def, preimage
-/
theorem isOpen_set_pi {i : Set ι} {s : forall a, Set (A a)} (hi : i.Finite)
    (hs : forall a in i, IsOpen (s a)) : IsOpen (pi i s) := by
  rw [pi_def]; exact hi.isOpen_biInter fun a ha => (hs _ ha).preimage (continuous_apply _)

/--
theorem `isOpen_pi_iff` / 定理 `isOpen_pi_iff`

English:
theorem isOpen_pi_iff
  given: {s : Set (forall a, A a)}
  proof: by
  rw [isOpen_iff_nhds]
  simp_rw [le_principal_iff, nhds_pi, Filter.mem_pi', mem_nhds_iff]
  refine forall₂_congr fun a _ => ⟨?_, ?_⟩
  · rintro ⟨I, t, ⟨h1, h2⟩⟩
    refine ⟨I, fun a => eval a '' (I : Set ι).pi fun a => (h1 a).choose, fun i hi => ?_, ?_⟩
    · simp_rw [eval_image_pi (Finset.mem_c

中文:
定理 isOpen_pi_iff
  条件: {s : Set (对任意 a, A a)}
  证明: by
  rw [isOpen_iff_nhds]
  simp_rw [le_principal_iff, nhds_pi, Filter.mem_pi', mem_nhds_iff]
  refine forall₂_congr fun a _ => ⟨?_, ?_⟩
  · rintro ⟨I, t, ⟨h1, h2⟩⟩
    refine ⟨I, fun a => eval a '' (I : Set ι).pi fun a => (h1 a).choose, fun i hi => ?_, ?_⟩
    · simp_rw [eval_image_pi (Finset.mem_c

Depends on / 依赖: Filter, Filter.mem_pi, Finset, Finset.mem_coe.mpr, Subset, Subset.trans, choose_spec, eval_image_pi, eval_image_pi_subset, isOpen_iff_nhds, le_principal_iff, mem_coe, mem_nhds_iff, mem_pi, nhds_pi, pi_mono, pi_nonempty_iff, pi_nonempty_iff.mpr, simp_rw
-/
theorem isOpen_pi_iff {s : Set (forall a, A a)} :
    IsOpen s ↔
      forall f, f in s -> exists (I : Finset ι) (u : forall a, Set (A a)),
        (forall a, a in I -> IsOpen (u a) ∧ f a in u a) ∧ (I : Set ι).pi u subseteq s := by
  rw [isOpen_iff_nhds]
  simp_rw [le_principal_iff, nhds_pi, Filter.mem_pi', mem_nhds_iff]
  refine forall₂_congr fun a _ => ⟨?_, ?_⟩
  · rintro ⟨I, t, ⟨h1, h2⟩⟩
    refine ⟨I, fun a => eval a '' (I : Set ι).pi fun a => (h1 a).choose, fun i hi => ?_, ?_⟩
    · simp_rw [eval_image_pi (Finset.mem_coe.mpr hi)
          (pi_nonempty_iff.mpr fun i => ⟨_, fun _ => (h1 i).choose_spec.2.2⟩)]
      exact (h1 i).choose_spec.2
    · exact Subset.trans
        (pi_mono fun i hi => (eval_image_pi_subset hi).trans (h1 i).choose_spec.1) h2
  · rintro ⟨I, t, ⟨h1, h2⟩⟩
    classical
    refine ⟨I, fun a => ite (a in I) (t a) univ, fun i => ?_, ?_⟩
    · by_cases hi : i in I
      · use t i
        simp_rw [if_pos hi]
        exact ⟨Subset.rfl, (h1 i) hi⟩
      · use univ
        simp_rw [if_neg hi]
        exact ⟨Subset.rfl, isOpen_univ, mem_univ _⟩
    · rw [← univ_pi_ite]
      simp only [← ite_and, ← Finset.mem_coe, and_self_iff, univ_pi_ite, h2]

/--
theorem `isOpen_pi_iff'` / 定理 `isOpen_pi_iff'`

English:
theorem isOpen_pi_iff'
  given: [Finite ι] {s : Set (forall a, A a)}
  proof: by
  cases nonempty_fintype ι
  rw [isOpen_iff_nhds]
  simp_rw [le_principal_iff, nhds_pi, Filter.mem_pi', mem_nhds_iff]
  refine forall₂_congr fun a _ => ⟨?_, ?_⟩
  · rintro ⟨I, t, ⟨h1, h2⟩⟩
    refine
      ⟨fun i => (h1 i).choose,
        ⟨fun i => (h1 i).choose_spec.2,
          (pi_mono fun i _

中文:
定理 isOpen_pi_iff'
  条件: [Finite ι] {s : Set (对任意 a, A a)}
  证明: by
  cases nonempty_fintype ι
  rw [isOpen_iff_nhds]
  simp_rw [le_principal_iff, nhds_pi, Filter.mem_pi', mem_nhds_iff]
  refine forall₂_congr fun a _ => ⟨?_, ?_⟩
  · rintro ⟨I, t, ⟨h1, h2⟩⟩
    refine
      ⟨fun i => (h1 i).choose,
        ⟨fun i => (h1 i).choose_spec.2,
          (pi_mono fun i _

Depends on / 依赖: Filter, Filter.mem_pi, Finset, Finset.coe_univ, Finset.univ, Subset, Subset.trans, choose_spec, coe_univ, inter_subset_left, isOpen_iff_nhds, le_principal_iff, mem_nhds_iff, mem_pi, nhds_pi, nonempty_fintype, pi_inter_compl, pi_mono, rfl.subset, simp_rw
-/
theorem isOpen_pi_iff' [Finite ι] {s : Set (forall a, A a)} :
    IsOpen s ↔
      forall f, f in s -> exists u : forall a, Set (A a), (forall a, IsOpen (u a) ∧ f a in u a) ∧ univ.pi u subseteq s := by
  cases nonempty_fintype ι
  rw [isOpen_iff_nhds]
  simp_rw [le_principal_iff, nhds_pi, Filter.mem_pi', mem_nhds_iff]
  refine forall₂_congr fun a _ => ⟨?_, ?_⟩
  · rintro ⟨I, t, ⟨h1, h2⟩⟩
    refine
      ⟨fun i => (h1 i).choose,
        ⟨fun i => (h1 i).choose_spec.2,
          (pi_mono fun i _ => (h1 i).choose_spec.1).trans (Subset.trans ?_ h2)⟩⟩
    rw [← pi_inter_compl (I : Set ι)]
    exact inter_subset_left
  · exact fun ⟨u, ⟨h1, _⟩⟩ =>
      ⟨Finset.univ, u, ⟨fun i => ⟨u i, ⟨rfl.subset, h1 i⟩⟩, by rwa [Finset.coe_univ]⟩⟩

/--
theorem `isClosed_set_pi` / 定理 `isClosed_set_pi`

English:
theorem isClosed_set_pi
  given: {i : Set ι} {s : forall a, Set (A a)} (hs : forall a in i, IsClosed (s a))
  proof: by
  rw [pi_def]; exact isClosed_biInter fun a ha => (hs _ ha).preimage (continuous_apply _)

中文:
定理 isClosed_set_pi
  条件: {i : Set ι} {s : 对任意 a, Set (A a)} (hs : 对任意 a in i, IsClosed (s a))
  证明: by
  rw [pi_def]; exact isClosed_biInter fun a ha => (hs _ ha).preimage (continuous_apply _)

Depends on / 依赖: continuous_apply, isClosed_biInter, pi_def, preimage
-/
theorem isClosed_set_pi {i : Set ι} {s : forall a, Set (A a)} (hs : forall a in i, IsClosed (s a)) :
    IsClosed (pi i s) := by
  rw [pi_def]; exact isClosed_biInter fun a ha => (hs _ ha).preimage (continuous_apply _)

/--
lemma `Topology.IsClosedEmbedding.piMap` / 引理 `Topology.IsClosedEmbedding.piMap`

English:
lemma Topology.IsClosedEmbedding.piMap
  statement: {f : forall i, A i -> B i}
  proof: ⟨.piMap fun i => (hf i).1, by simpa using isClosed_set_pi fun i _ => (hf i).2⟩

中文:
引理 Topology.IsClosedEmbedding.piMap
  结论: {f : 对任意 i, A i -> B i}
  证明: ⟨.piMap fun i => (hf i).1, by simpa using isClosed_set_pi fun i _ => (hf i).2⟩
-/
protected lemma Topology.IsClosedEmbedding.piMap {f : forall i, A i -> B i}
    (hf : forall i, IsClosedEmbedding (f i)) : IsClosedEmbedding (Pi.map f) :=
  ⟨.piMap fun i => (hf i).1, by simpa using isClosed_set_pi fun i _ => (hf i).2⟩

/--
lemma `Topology.IsOpenEmbedding.piMap` / 引理 `Topology.IsOpenEmbedding.piMap`

English:
lemma Topology.IsOpenEmbedding.piMap
  statement: [Finite ι] {f : forall i, A i -> B i}
  proof: ⟨.piMap fun i => (hf i).1, by simpa using isOpen_set_pi Set.finite_univ fun i _ => (hf i).2⟩

中文:
引理 Topology.IsOpenEmbedding.piMap
  结论: [Finite ι] {f : 对任意 i, A i -> B i}
  证明: ⟨.piMap fun i => (hf i).1, by simpa using isOpen_set_pi Set.finite_univ fun i _ => (hf i).2⟩
-/
protected lemma Topology.IsOpenEmbedding.piMap [Finite ι] {f : forall i, A i -> B i}
    (hf : forall i, IsOpenEmbedding (f i)) : IsOpenEmbedding (Pi.map f) :=
  ⟨.piMap fun i => (hf i).1, by simpa using isOpen_set_pi Set.finite_univ fun i _ => (hf i).2⟩

/--
theorem `mem_nhds_of_pi_mem_nhds` / 定理 `mem_nhds_of_pi_mem_nhds`

English:
theorem mem_nhds_of_pi_mem_nhds
  statement: {I : Set ι} {s : forall i, Set (A i)} (a : forall i, A i) (hs : I.pi s in 𝓝 a)
  proof: by
  rw [nhds_pi] at hs; exact mem_of_pi_mem_pi hs hi

中文:
定理 mem_nhds_of_pi_mem_nhds
  结论: {I : Set ι} {s : 对任意 i, Set (A i)} (a : 对任意 i, A i) (hs : I.pi s in 𝓝 a)
  证明: by
  rw [nhds_pi] at hs; exact mem_of_pi_mem_pi hs hi

Depends on / 依赖: mem_of_pi_mem_pi, nhds_pi
-/
theorem mem_nhds_of_pi_mem_nhds {I : Set ι} {s : forall i, Set (A i)} (a : forall i, A i) (hs : I.pi s in 𝓝 a)
    {i : ι} (hi : i in I) : s i in 𝓝 (a i) := by
  rw [nhds_pi] at hs; exact mem_of_pi_mem_pi hs hi

/--
theorem `set_pi_mem_nhds` / 定理 `set_pi_mem_nhds`

English:
theorem set_pi_mem_nhds
  statement: {i : Set ι} {s : forall a, Set (A a)} {x : forall a, A a} (hi : i.Finite)
  proof: by
  rw [pi_def]; rw [biInter_mem hi]
  exact fun a ha => (continuous_apply a).continuousAt (hs a ha)

中文:
定理 set_pi_mem_nhds
  结论: {i : Set ι} {s : 对任意 a, Set (A a)} {x : 对任意 a, A a} (hi : i.Finite)
  证明: by
  rw [pi_def]; rw [biInter_mem hi]
  exact fun a ha => (continuous_apply a).continuousAt (hs a ha)

Depends on / 依赖: biInter_mem, continuousAt, continuous_apply, pi_def
-/
theorem set_pi_mem_nhds {i : Set ι} {s : forall a, Set (A a)} {x : forall a, A a} (hi : i.Finite)
    (hs : forall a in i, s a in 𝓝 (x a)) : pi i s in 𝓝 x := by
  rw [pi_def]; rw [biInter_mem hi]
  exact fun a ha => (continuous_apply a).continuousAt (hs a ha)

/--
theorem `set_pi_mem_nhds_iff` / 定理 `set_pi_mem_nhds_iff`

English:
theorem set_pi_mem_nhds_iff
  given: {I : Set ι} (hI : I.Finite) {s : forall i, Set (A i)} (a : forall i, A i)
  proof: by
  rw [nhds_pi]; rw [pi_mem_pi_iff hI]

中文:
定理 set_pi_mem_nhds_iff
  条件: {I : Set ι} (hI : I.Finite) {s : 对任意 i, Set (A i)} (a : 对任意 i, A i)
  证明: by
  rw [nhds_pi]; rw [pi_mem_pi_iff hI]

Depends on / 依赖: nhds_pi, pi_mem_pi_iff
-/
theorem set_pi_mem_nhds_iff {I : Set ι} (hI : I.Finite) {s : forall i, Set (A i)} (a : forall i, A i) :
    I.pi s in 𝓝 a ↔ forall i : ι, i in I -> s i in 𝓝 (a i) := by
  rw [nhds_pi]; rw [pi_mem_pi_iff hI]

/--
theorem `interior_pi_set` / 定理 `interior_pi_set`

English:
theorem interior_pi_set
  given: {I : Set ι} (hI : I.Finite) {s : forall i, Set (A i)}
  proof: by
  ext a
  simp only [Set.mem_pi, mem_interior_iff_mem_nhds, set_pi_mem_nhds_iff hI]

中文:
定理 interior_pi_set
  条件: {I : Set ι} (hI : I.Finite) {s : 对任意 i, Set (A i)}
  证明: by
  ext a
  simp only [Set.mem_pi, mem_interior_iff_mem_nhds, set_pi_mem_nhds_iff hI]

Depends on / 依赖: Set.mem_pi, mem_interior_iff_mem_nhds, mem_pi, set_pi_mem_nhds_iff
-/
theorem interior_pi_set {I : Set ι} (hI : I.Finite) {s : forall i, Set (A i)} :
    interior (pi I s) = I.pi fun i => interior (s i) := by
  ext a
  simp only [Set.mem_pi, mem_interior_iff_mem_nhds, set_pi_mem_nhds_iff hI]

/--
theorem `exists_finset_piecewise_mem_of_mem_nhds` / 定理 `exists_finset_piecewise_mem_of_mem_nhds`

English:
theorem exists_finset_piecewise_mem_of_mem_nhds
  statement: [DecidableEq ι] {s : Set (forall a, A a)} {x : forall a, A a}
  proof: by
  simp only [nhds_pi, Filter.mem_pi'] at hs
  rcases hs with ⟨I, t, htx, hts⟩
  refine ⟨I, hts fun i hi => ?_⟩
  simpa [Finset.mem_coe.1 hi] using mem_of_mem_nhds (htx i)

中文:
定理 exists_finset_piecewise_mem_of_mem_nhds
  结论: [DecidableEq ι] {s : Set (对任意 a, A a)} {x : 对任意 a, A a}
  证明: by
  simp only [nhds_pi, Filter.mem_pi'] at hs
  rcases hs with ⟨I, t, htx, hts⟩
  refine ⟨I, hts fun i hi => ?_⟩
  simpa [Finset.mem_coe.1 hi] using mem_of_mem_nhds (htx i)

Depends on / 依赖: Filter, Filter.mem_pi, Finset, Finset.mem_coe, mem_coe, mem_of_mem_nhds, mem_pi, nhds_pi
-/
theorem exists_finset_piecewise_mem_of_mem_nhds [DecidableEq ι] {s : Set (forall a, A a)} {x : forall a, A a}
    (hs : s in 𝓝 x) (y : forall a, A a) : exists I : Finset ι, I.piecewise x y in s := by
  simp only [nhds_pi, Filter.mem_pi'] at hs
  rcases hs with ⟨I, t, htx, hts⟩
  refine ⟨I, hts fun i hi => ?_⟩
  simpa [Finset.mem_coe.1 hi] using mem_of_mem_nhds (htx i)

/--
theorem `pi_generateFrom_eq` / 定理 `pi_generateFrom_eq`

English:
theorem pi_generateFrom_eq
  given: {A : ι -> Type*} {g : forall a, Set (Set (A a))}
  proof: by
  refine le_antisymm ?_ ?_
  · apply le_generateFrom
    rintro _ ⟨s, i, hi, rfl⟩
    let := fun a => generateFrom (g a)
    exact isOpen_set_pi i.finite_toSet (fun a ha => GenerateOpen.basic _ (hi a ha))
  · classical
refine le_iInf fun i => coinduced_le_iff_le_induced.1 le_generateFrom fun s hs

中文:
定理 pi_generateFrom_eq
  条件: {A : ι -> 类型} {g : 对任意 a, Set (Set (A a))}
  证明: by
  refine le_antisymm ?_ ?_
  · apply le_generateFrom
    rintro _ ⟨s, i, hi, rfl⟩
    let := fun a => generateFrom (g a)
    exact isOpen_set_pi i.finite_toSet (fun a ha => GenerateOpen.basic _ (hi a ha))
  · classical
refine le_iInf fun i => coinduced_le_iff_le_induced.1 le_generateFrom fun s hs

Depends on / 依赖: GenerateOpen, GenerateOpen.basic, classical, coinduced_le_iff_le_induced, finite_toSet, generateFrom, i.finite_toSet, isOpen_set_pi, le_antisymm, le_generateFrom, le_iInf, update
-/
theorem pi_generateFrom_eq {A : ι -> Type*} {g : forall a, Set (Set (A a))} :
    (@Pi.topologicalSpace ι A fun a => generateFrom (g a)) =
      generateFrom
        { t | exists (s : forall a, Set (A a)) (i : Finset ι), (forall a in i, s a in g a) ∧ t = pi (↑i) s } := by
  refine le_antisymm ?_ ?_
  · apply le_generateFrom
    rintro _ ⟨s, i, hi, rfl⟩
    let := fun a => generateFrom (g a)
    exact isOpen_set_pi i.finite_toSet (fun a ha => GenerateOpen.basic _ (hi a ha))
  · classical
refine le_iInf fun i => coinduced_le_iff_le_induced.1 le_generateFrom fun s hs => ?_
    refine GenerateOpen.basic _ ⟨update (fun i => univ) i s, {i}, ?_⟩
    simp [hs]

/--
theorem `pi_eq_generateFrom` / 定理 `pi_eq_generateFrom`

English:
theorem pi_eq_generateFrom
  proof: calc Pi.topologicalSpace
  _ = @Pi.topologicalSpace ι A fun _ => generateFrom { s | IsOpen s } := by
    simp +instances only [generateFrom_setOfPred_isOpen]
  _ = _ := pi_generateFrom_eq

中文:
定理 pi_eq_generateFrom
  证明: calc Pi.topologicalSpace
  _ = @Pi.topologicalSpace ι A fun _ => generateFrom { s | IsOpen s } := by
    simp +instances only [generateFrom_setOfPred_isOpen]
  _ = _ := pi_generateFrom_eq

Depends on / 依赖: IsOpen, Pi.topologicalSpace, generateFrom, generateFrom_setOfPred_isOpen, instances, pi_generateFrom_eq, topologicalSpace
-/
theorem pi_eq_generateFrom :
    Pi.topologicalSpace =
      generateFrom
        { g | exists (s : forall a, Set (A a)) (i : Finset ι), (forall a in i, IsOpen (s a)) ∧ g = pi (↑i) s } :=
  calc Pi.topologicalSpace
  _ = @Pi.topologicalSpace ι A fun _ => generateFrom { s | IsOpen s } := by
    simp +instances only [generateFrom_setOfPred_isOpen]
  _ = _ := pi_generateFrom_eq

/--
theorem `pi_generateFrom_eq_finite` / 定理 `pi_generateFrom_eq_finite`

English:
theorem pi_generateFrom_eq_finite
  statement: {X : ι -> Type*} {g : forall a, Set (Set (X a))} [Finite ι]
  proof: by
  cases nonempty_fintype ι
  rw [pi_generateFrom_eq]
  refine le_antisymm (generateFrom_anti ?_) (le_generateFrom ?_)
  · exact fun s ⟨t, ht, Eq⟩ => ⟨t, Finset.univ, by simp [ht, Eq]⟩
  · rintro s ⟨t, i, ht, rfl⟩
    let := generateFrom { t | exists s : forall a, Set (X a), (forall a, s a in g a)

中文:
定理 pi_generateFrom_eq_finite
  结论: {X : ι -> 类型} {g : 对任意 a, Set (Set (X a))} [Finite ι]
  证明: by
  cases nonempty_fintype ι
  rw [pi_generateFrom_eq]
  refine le_antisymm (generateFrom_anti ?_) (le_generateFrom ?_)
  · exact fun s ⟨t, ht, Eq⟩ => ⟨t, Finset.univ, by simp [ht, Eq]⟩
  · rintro s ⟨t, i, ht, rfl⟩
    let := generateFrom { t | exists s : forall a, Set (X a), (forall a, s a in g a)

Depends on / 依赖: Finset, Finset.univ, generateFrom, generateFrom_anti, inter_subset_left, isOpen_iff_forall_mem_open, le_antisymm, le_generateFrom, nonempty_fintype, pi_generateFrom_eq, sUnion_eq_univ_iff
-/
theorem pi_generateFrom_eq_finite {X : ι -> Type*} {g : forall a, Set (Set (X a))} [Finite ι]
    (hg : forall a, ⋃₀ g a = univ) :
    (@Pi.topologicalSpace ι X fun a => generateFrom (g a)) =
      generateFrom { t | exists s : forall a, Set (X a), (forall a, s a in g a) ∧ t = pi univ s } := by
  cases nonempty_fintype ι
  rw [pi_generateFrom_eq]
  refine le_antisymm (generateFrom_anti ?_) (le_generateFrom ?_)
  · exact fun s ⟨t, ht, Eq⟩ => ⟨t, Finset.univ, by simp [ht, Eq]⟩
  · rintro s ⟨t, i, ht, rfl⟩
    let := generateFrom { t | exists s : forall a, Set (X a), (forall a, s a in g a) ∧ t = pi univ s }
    refine isOpen_iff_forall_mem_open.2 fun f hf => ?_
    choose c hcg hfc using fun a => sUnion_eq_univ_iff.1 (hg a) (f a)
    refine ⟨pi i t inter pi ((↑i)ᶜ : Set ι) c, inter_subset_left, ?_, ⟨hf, fun a _ => hfc a⟩⟩
    classical
    rw [← univ_pi_piecewise]
    refine GenerateOpen.basic _ ⟨_, fun a => ?_, rfl⟩
    by_cases a in i <;> simp [*]

/--
theorem `induced_to_pi` / 定理 `induced_to_pi`

English:
theorem induced_to_pi
  given: {X : Type*} (f : X -> forall i, A i)
  proof: by
  simp_rw [Pi.topologicalSpace, induced_iInf, induced_compose, Function.comp_def]

中文:
定理 induced_to_pi
  条件: {X : 类型} (f : X -> 对任意 i, A i)
  证明: by
  simp_rw [Pi.topologicalSpace, induced_iInf, induced_compose, Function.comp_def]

Depends on / 依赖: Function, Function.comp_def, Pi.topologicalSpace, comp_def, induced_compose, induced_iInf, simp_rw, topologicalSpace
-/
theorem induced_to_pi {X : Type*} (f : X -> forall i, A i) :
    induced f Pi.topologicalSpace = ⨅ i, induced (f · i) inferInstance := by
  simp_rw [Pi.topologicalSpace, induced_iInf, induced_compose, Function.comp_def]

/--
theorem `inducing_iInf_to_pi` / 定理 `inducing_iInf_to_pi`

English:
theorem inducing_iInf_to_pi
  given: {X : Type*} (f : forall i, X -> A i)
  proof: letI := ⨅ i, induced (f i) inferInstance; ⟨(induced_to_pi _).symm⟩

中文:
定理 inducing_iInf_to_pi
  条件: {X : 类型} (f : 对任意 i, X -> A i)
  证明: letI := ⨅ i, induced (f i) inferInstance; ⟨(induced_to_pi _).symm⟩

Depends on / 依赖: induced, induced_to_pi
-/
theorem inducing_iInf_to_pi {X : Type*} (f : forall i, X -> A i) :
    @IsInducing X (forall i, A i) (⨅ i, induced (f i) inferInstance) _ fun x i => f i x :=
  letI := ⨅ i, induced (f i) inferInstance; ⟨(induced_to_pi _).symm⟩

variable [Finite ι] [forall i, DiscreteTopology (A i)]

/--
Instance `Pi.discreteTopology` / 实例 `Pi.discreteTopology`

English:
instance Pi.discreteTopology
  signature: : DiscreteTopology (forall i, A i)
  body: discreteTopology_iff_isOpen_singleton.mpr fun x => by
    rw [← univ_pi_singleton]
    exact isOpen_set_pi finite_univ fun i _ => (isOpen_discrete {x i})

中文:
实例 Pi.discreteTopology
  签名: : DiscreteTopology (对任意 i, A i)
  定义体: discreteTopology_iff_isOpen_singleton.mpr fun x => by
    rw [← univ_pi_singleton]
    exact isOpen_set_pi finite_univ fun i _ => (isOpen_discrete {x i})

Depends on / 依赖: discreteTopology_iff_isOpen_singleton, discreteTopology_iff_isOpen_singleton.mpr, finite_univ, isOpen_discrete, isOpen_set_pi, univ_pi_singleton
-/
instance Pi.discreteTopology : DiscreteTopology (forall i, A i) :=
  discreteTopology_iff_isOpen_singleton.mpr fun x => by
    rw [← univ_pi_singleton]
    exact isOpen_set_pi finite_univ fun i _ => (isOpen_discrete {x i})

/--
lemma `Function.Surjective.isEmbedding_comp` / 引理 `Function.Surjective.isEmbedding_comp`

English:
lemma Function.Surjective.isEmbedding_comp
  given: {n m : Type*} (f : m -> n) (hf : Function.Surjective f)
  proof: by
  refine ⟨isInducing_iff_nhds.mpr fun x => ?_, hf.injective_comp_right⟩
  simp only [nhds_pi, Filter.pi, Filter.comap_iInf, ← hf.iInf_congr, Filter.comap_comap,
    Function.comp_def]

中文:
引理 Function.Surjective.isEmbedding_comp
  条件: {n m : 类型} (f : m -> n) (hf : Function.Surjective f)
  证明: by
  refine ⟨isInducing_iff_nhds.mpr fun x => ?_, hf.injective_comp_right⟩
  simp only [nhds_pi, Filter.pi, Filter.comap_iInf, ← hf.iInf_congr, Filter.comap_comap,
    Function.comp_def]

Depends on / 依赖: Filter, Filter.comap_comap, Filter.comap_iInf, Filter.pi, Function, Function.comp_def, comap_comap, comap_iInf, comp_def, hf.iInf_congr, hf.injective_comp_right, iInf_congr, injective_comp_right, isInducing_iff_nhds, isInducing_iff_nhds.mpr, nhds_pi
-/
lemma Function.Surjective.isEmbedding_comp {n m : Type*} (f : m -> n) (hf : Function.Surjective f) :
    IsEmbedding ((· ∘ f) : (n -> X) -> (m -> X)) := by
  refine ⟨isInducing_iff_nhds.mpr fun x => ?_, hf.injective_comp_right⟩
  simp only [nhds_pi, Filter.pi, Filter.comap_iInf, ← hf.iInf_congr, Filter.comap_comap,
    Function.comp_def]

end Pi

section Sigma

variable {ι κ : Type*} {σ : ι -> Type*} {τ : κ -> Type*} [forall i, TopologicalSpace (σ i)]
  [forall k, TopologicalSpace (τ k)] [TopologicalSpace X]

@[continuity, fun_prop]
/--
theorem `continuous_sigmaMk` / 定理 `continuous_sigmaMk`

English:
theorem continuous_sigmaMk
  given: {i : ι}
  statement: Continuous (@Sigma.mk ι σ i)
  proof: continuous_iSup_rng continuous_coinduced_rng

中文:
定理 continuous_sigmaMk
  条件: {i : ι}
  结论: Continuous (@Sigma.mk ι σ i)
  证明: continuous_iSup_rng continuous_coinduced_rng

Depends on / 依赖: continuous_coinduced_rng, continuous_iSup_rng
-/
theorem continuous_sigmaMk {i : ι} : Continuous (@Sigma.mk ι σ i) :=
  continuous_iSup_rng continuous_coinduced_rng

/--
theorem `isOpen_sigma_iff` / 定理 `isOpen_sigma_iff`

English:
theorem isOpen_sigma_iff
  given: {s : Set (Sigma σ)}
  statement: IsOpen s ↔ forall i, IsOpen (Sigma.mk i ⁻¹' s)
  proof: by
  rw [isOpen_iSup_iff]
  rfl

中文:
定理 isOpen_sigma_iff
  条件: {s : Set (Sigma σ)}
  结论: IsOpen s ↔ 对任意 i, IsOpen (Sigma.mk i ⁻¹' s)
  证明: by
  rw [isOpen_iSup_iff]
  rfl

Depends on / 依赖: isOpen_iSup_iff
-/
theorem isOpen_sigma_iff {s : Set (Sigma σ)} : IsOpen s ↔ forall i, IsOpen (Sigma.mk i ⁻¹' s) := by
  rw [isOpen_iSup_iff]
  rfl

/--
theorem `isClosed_sigma_iff` / 定理 `isClosed_sigma_iff`

English:
theorem isClosed_sigma_iff
  given: {s : Set (Sigma σ)}
  statement: IsClosed s ↔ forall i, IsClosed (Sigma.mk i ⁻¹' s)
  proof: by
  simp only [← isOpen_compl_iff, isOpen_sigma_iff, preimage_compl]

中文:
定理 isClosed_sigma_iff
  条件: {s : Set (Sigma σ)}
  结论: IsClosed s ↔ 对任意 i, IsClosed (Sigma.mk i ⁻¹' s)
  证明: by
  simp only [← isOpen_compl_iff, isOpen_sigma_iff, preimage_compl]

Depends on / 依赖: isOpen_compl_iff, isOpen_sigma_iff, preimage_compl
-/
theorem isClosed_sigma_iff {s : Set (Sigma σ)} : IsClosed s ↔ forall i, IsClosed (Sigma.mk i ⁻¹' s) := by
  simp only [← isOpen_compl_iff, isOpen_sigma_iff, preimage_compl]

/--
theorem `isOpenMap_sigmaMk` / 定理 `isOpenMap_sigmaMk`

English:
theorem isOpenMap_sigmaMk
  given: {i : ι}
  statement: IsOpenMap (@Sigma.mk ι σ i)
  proof: by
  intro s hs
  rw [isOpen_sigma_iff]
  intro j
  rcases eq_or_ne j i with (rfl | hne)
  · rwa [preimage_image_eq _ sigma_mk_injective]
  · rw [preimage_image_sigmaMk_of_ne hne]
    exact isOpen_empty

中文:
定理 isOpenMap_sigmaMk
  条件: {i : ι}
  结论: IsOpenMap (@Sigma.mk ι σ i)
  证明: by
  intro s hs
  rw [isOpen_sigma_iff]
  intro j
  rcases eq_or_ne j i with (rfl | hne)
  · rwa [preimage_image_eq _ sigma_mk_injective]
  · rw [preimage_image_sigmaMk_of_ne hne]
    exact isOpen_empty

Depends on / 依赖: eq_or_ne, isOpen_empty, isOpen_sigma_iff, preimage_image_eq, preimage_image_sigmaMk_of_ne, sigma_mk_injective
-/
theorem isOpenMap_sigmaMk {i : ι} : IsOpenMap (@Sigma.mk ι σ i) := by
  intro s hs
  rw [isOpen_sigma_iff]
  intro j
  rcases eq_or_ne j i with (rfl | hne)
  · rwa [preimage_image_eq _ sigma_mk_injective]
  · rw [preimage_image_sigmaMk_of_ne hne]
    exact isOpen_empty

/--
theorem `isOpen_range_sigmaMk` / 定理 `isOpen_range_sigmaMk`

English:
theorem isOpen_range_sigmaMk
  given: {i : ι}
  statement: IsOpen (range (@Sigma.mk ι σ i))
  proof: isOpenMap_sigmaMk.isOpen_range

中文:
定理 isOpen_range_sigmaMk
  条件: {i : ι}
  结论: IsOpen (range (@Sigma.mk ι σ i))
  证明: isOpenMap_sigmaMk.isOpen_range

Depends on / 依赖: isOpenMap_sigmaMk, isOpenMap_sigmaMk.isOpen_range, isOpen_range
-/
theorem isOpen_range_sigmaMk {i : ι} : IsOpen (range (@Sigma.mk ι σ i)) :=
  isOpenMap_sigmaMk.isOpen_range

/--
theorem `isClosedMap_sigmaMk` / 定理 `isClosedMap_sigmaMk`

English:
theorem isClosedMap_sigmaMk
  given: {i : ι}
  statement: IsClosedMap (@Sigma.mk ι σ i)
  proof: by
  intro s hs
  rw [isClosed_sigma_iff]
  intro j
  rcases eq_or_ne j i with (rfl | hne)
  · rwa [preimage_image_eq _ sigma_mk_injective]
  · rw [preimage_image_sigmaMk_of_ne hne]
    exact isClosed_empty

中文:
定理 isClosedMap_sigmaMk
  条件: {i : ι}
  结论: IsClosedMap (@Sigma.mk ι σ i)
  证明: by
  intro s hs
  rw [isClosed_sigma_iff]
  intro j
  rcases eq_or_ne j i with (rfl | hne)
  · rwa [preimage_image_eq _ sigma_mk_injective]
  · rw [preimage_image_sigmaMk_of_ne hne]
    exact isClosed_empty

Depends on / 依赖: eq_or_ne, isClosed_empty, isClosed_sigma_iff, preimage_image_eq, preimage_image_sigmaMk_of_ne, sigma_mk_injective
-/
theorem isClosedMap_sigmaMk {i : ι} : IsClosedMap (@Sigma.mk ι σ i) := by
  intro s hs
  rw [isClosed_sigma_iff]
  intro j
  rcases eq_or_ne j i with (rfl | hne)
  · rwa [preimage_image_eq _ sigma_mk_injective]
  · rw [preimage_image_sigmaMk_of_ne hne]
    exact isClosed_empty

/--
theorem `isClosed_range_sigmaMk` / 定理 `isClosed_range_sigmaMk`

English:
theorem isClosed_range_sigmaMk
  given: {i : ι}
  statement: IsClosed (range (@Sigma.mk ι σ i))
  proof: isClosedMap_sigmaMk.isClosed_range

中文:
定理 isClosed_range_sigmaMk
  条件: {i : ι}
  结论: IsClosed (range (@Sigma.mk ι σ i))
  证明: isClosedMap_sigmaMk.isClosed_range

Depends on / 依赖: isClosedMap_sigmaMk, isClosedMap_sigmaMk.isClosed_range, isClosed_range
-/
theorem isClosed_range_sigmaMk {i : ι} : IsClosed (range (@Sigma.mk ι σ i)) :=
  isClosedMap_sigmaMk.isClosed_range

/--
lemma `Topology.IsOpenEmbedding.sigmaMk` / 引理 `Topology.IsOpenEmbedding.sigmaMk`

English:
lemma Topology.IsOpenEmbedding.sigmaMk
  given: {i : ι}
  statement: IsOpenEmbedding (@Sigma.mk ι σ i)
  proof: .of_continuous_injective_isOpenMap continuous_sigmaMk sigma_mk_injective isOpenMap_sigmaMk

中文:
引理 Topology.IsOpenEmbedding.sigmaMk
  条件: {i : ι}
  结论: IsOpenEmbedding (@Sigma.mk ι σ i)
  证明: .of_continuous_injective_isOpenMap continuous_sigmaMk sigma_mk_injective isOpenMap_sigmaMk

Depends on / 依赖: continuous_sigmaMk, isOpenMap_sigmaMk, of_continuous_injective_isOpenMap, sigma_mk_injective
-/
lemma Topology.IsOpenEmbedding.sigmaMk {i : ι} : IsOpenEmbedding (@Sigma.mk ι σ i) :=
  .of_continuous_injective_isOpenMap continuous_sigmaMk sigma_mk_injective isOpenMap_sigmaMk

/--
lemma `Topology.IsClosedEmbedding.sigmaMk` / 引理 `Topology.IsClosedEmbedding.sigmaMk`

English:
lemma Topology.IsClosedEmbedding.sigmaMk
  given: {i : ι}
  statement: IsClosedEmbedding (@Sigma.mk ι σ i)
  proof: .of_continuous_injective_isClosedMap continuous_sigmaMk sigma_mk_injective isClosedMap_sigmaMk

中文:
引理 Topology.IsClosedEmbedding.sigmaMk
  条件: {i : ι}
  结论: IsClosedEmbedding (@Sigma.mk ι σ i)
  证明: .of_continuous_injective_isClosedMap continuous_sigmaMk sigma_mk_injective isClosedMap_sigmaMk

Depends on / 依赖: continuous_sigmaMk, isClosedMap_sigmaMk, of_continuous_injective_isClosedMap, sigma_mk_injective
-/
lemma Topology.IsClosedEmbedding.sigmaMk {i : ι} : IsClosedEmbedding (@Sigma.mk ι σ i) :=
  .of_continuous_injective_isClosedMap continuous_sigmaMk sigma_mk_injective isClosedMap_sigmaMk

/--
lemma `Topology.IsEmbedding.sigmaMk` / 引理 `Topology.IsEmbedding.sigmaMk`

English:
lemma Topology.IsEmbedding.sigmaMk
  given: {i : ι}
  statement: IsEmbedding (@Sigma.mk ι σ i)
  proof: IsClosedEmbedding.sigmaMk.1

中文:
引理 Topology.IsEmbedding.sigmaMk
  条件: {i : ι}
  结论: IsEmbedding (@Sigma.mk ι σ i)
  证明: IsClosedEmbedding.sigmaMk.1

Depends on / 依赖: IsClosedEmbedding, IsClosedEmbedding.sigmaMk, sigmaMk
-/
lemma Topology.IsEmbedding.sigmaMk {i : ι} : IsEmbedding (@Sigma.mk ι σ i) :=
  IsClosedEmbedding.sigmaMk.1

/--
theorem `Sigma.nhds_mk` / 定理 `Sigma.nhds_mk`

English:
theorem Sigma.nhds_mk
  given: (i : ι) (x : σ i)
  statement: 𝓝 (⟨i, x⟩ : Sigma σ) = Filter.map (Sigma.mk i) (𝓝 x)
  proof: (IsOpenEmbedding.sigmaMk.map_nhds_eq x).symm

中文:
定理 Sigma.nhds_mk
  条件: (i : ι) (x : σ i)
  结论: 𝓝 (⟨i, x⟩ : Sigma σ) = Filter.map (Sigma.mk i) (𝓝 x)
  证明: (IsOpenEmbedding.sigmaMk.map_nhds_eq x).symm

Depends on / 依赖: IsOpenEmbedding, IsOpenEmbedding.sigmaMk.map_nhds_eq, map_nhds_eq, sigmaMk
-/
theorem Sigma.nhds_mk (i : ι) (x : σ i) : 𝓝 (⟨i, x⟩ : Sigma σ) = Filter.map (Sigma.mk i) (𝓝 x) :=
  (IsOpenEmbedding.sigmaMk.map_nhds_eq x).symm

/--
theorem `Sigma.nhds_eq` / 定理 `Sigma.nhds_eq`

English:
theorem Sigma.nhds_eq
  given: (x : Sigma σ)
  statement: 𝓝 x = Filter.map (Sigma.mk x.1) (𝓝 x.2)
  proof: by
  cases x
  apply Sigma.nhds_mk

中文:
定理 Sigma.nhds_eq
  条件: (x : Sigma σ)
  结论: 𝓝 x = Filter.map (Sigma.mk x.1) (𝓝 x.2)
  证明: by
  cases x
  apply Sigma.nhds_mk

Depends on / 依赖: Sigma.nhds_mk, nhds_mk
-/
theorem Sigma.nhds_eq (x : Sigma σ) : 𝓝 x = Filter.map (Sigma.mk x.1) (𝓝 x.2) := by
  cases x
  apply Sigma.nhds_mk

/--
theorem `comap_sigmaMk_nhds` / 定理 `comap_sigmaMk_nhds`

English:
theorem comap_sigmaMk_nhds
  given: (i : ι) (x : σ i)
  statement: comap (Sigma.mk i) (𝓝 ⟨i, x⟩) = 𝓝 x
  proof: (IsEmbedding.sigmaMk.nhds_eq_comap _).symm

中文:
定理 comap_sigmaMk_nhds
  条件: (i : ι) (x : σ i)
  结论: comap (Sigma.mk i) (𝓝 ⟨i, x⟩) = 𝓝 x
  证明: (IsEmbedding.sigmaMk.nhds_eq_comap _).symm

Depends on / 依赖: IsEmbedding, IsEmbedding.sigmaMk.nhds_eq_comap, nhds_eq_comap, sigmaMk
-/
theorem comap_sigmaMk_nhds (i : ι) (x : σ i) : comap (Sigma.mk i) (𝓝 ⟨i, x⟩) = 𝓝 x :=
  (IsEmbedding.sigmaMk.nhds_eq_comap _).symm

/--
theorem `isOpen_sigma_fst_preimage` / 定理 `isOpen_sigma_fst_preimage`

English:
theorem isOpen_sigma_fst_preimage
  given: (s : Set ι)
  statement: IsOpen (Sigma.fst ⁻¹' s : Set (Σ a, σ a))
  proof: by
  rw [← biUnion_of_singleton s]; rw [preimage_iUnion₂]
  simp only [← range_sigmaMk]
  exact isOpen_biUnion fun _ _ => isOpen_range_sigmaMk

中文:
定理 isOpen_sigma_fst_preimage
  条件: (s : Set ι)
  结论: IsOpen (Sigma.fst ⁻¹' s : Set (Σ a, σ a))
  证明: by
  rw [← biUnion_of_singleton s]; rw [preimage_iUnion₂]
  simp only [← range_sigmaMk]
  exact isOpen_biUnion fun _ _ => isOpen_range_sigmaMk

Depends on / 依赖: biUnion_of_singleton, isOpen_biUnion, isOpen_range_sigmaMk, range_sigmaMk
-/
theorem isOpen_sigma_fst_preimage (s : Set ι) : IsOpen (Sigma.fst ⁻¹' s : Set (Σ a, σ a)) := by
  rw [← biUnion_of_singleton s]; rw [preimage_iUnion₂]
  simp only [← range_sigmaMk]
  exact isOpen_biUnion fun _ _ => isOpen_range_sigmaMk

/-- A map out of a sum type is continuous iff its restriction to each summand is. -/
@[simp]
/--
theorem `continuous_sigma_iff` / 定理 `continuous_sigma_iff`

English:
theorem continuous_sigma_iff
  given: {f : Sigma σ -> X}
  proof: by
  delta instTopologicalSpaceSigma
  rw [continuous_iSup_dom]
  exact forall_congr' fun _ => continuous_coinduced_dom

中文:
定理 continuous_sigma_iff
  条件: {f : Sigma σ -> X}
  证明: by
  delta instTopologicalSpaceSigma
  rw [continuous_iSup_dom]
  exact forall_congr' fun _ => continuous_coinduced_dom

Depends on / 依赖: continuous_coinduced_dom, continuous_iSup_dom, forall_congr, instTopologicalSpaceSigma
-/
theorem continuous_sigma_iff {f : Sigma σ -> X} :
    Continuous f ↔ forall i, Continuous fun a => f ⟨i, a⟩ := by
  delta instTopologicalSpaceSigma
  rw [continuous_iSup_dom]
  exact forall_congr' fun _ => continuous_coinduced_dom

-- NB. This is a bad `fun_prop` theorem: because of its hypotheses, this would be classified as a
-- transition theorem, and most likely never fire.
/-- A map out of a sum type is continuous if its restriction to each summand is. -/
@[continuity]
/--
theorem `continuous_sigma` / 定理 `continuous_sigma`

English:
theorem continuous_sigma
  given: {f : Sigma σ -> X} (hf : forall i, Continuous fun a => f ⟨i, a⟩)
  proof: continuous_sigma_iff.2 hf

中文:
定理 continuous_sigma
  条件: {f : Sigma σ -> X} (hf : 对任意 i, Continuous fun a => f ⟨i, a⟩)
  证明: continuous_sigma_iff.2 hf

Depends on / 依赖: continuous_sigma_iff
-/
theorem continuous_sigma {f : Sigma σ -> X} (hf : forall i, Continuous fun a => f ⟨i, a⟩) :
    Continuous f :=
  continuous_sigma_iff.2 hf

/--
theorem `inducing_sigma` / 定理 `inducing_sigma`

English:
theorem inducing_sigma
  given: {f : Sigma σ -> X}
  proof: by
  refine ⟨fun h => ⟨fun i => h.comp IsEmbedding.sigmaMk.1, fun i => ?_⟩, ?_⟩
  · rcases h.isOpen_iff.1 (isOpen_range_sigmaMk (i := i)) with ⟨U, hUo, hU⟩
    refine ⟨U, hUo, ?_⟩
    simpa [Set.ext_iff] using hU
  · refine fun ⟨h₁, h₂⟩ => isInducing_iff_nhds.2 fun ⟨i, x⟩ => ?_
    rw [Sigma.nhds_mk

中文:
定理 inducing_sigma
  条件: {f : Sigma σ -> X}
  证明: by
  refine ⟨fun h => ⟨fun i => h.comp IsEmbedding.sigmaMk.1, fun i => ?_⟩, ?_⟩
  · rcases h.isOpen_iff.1 (isOpen_range_sigmaMk (i := i)) with ⟨U, hUo, hU⟩
    refine ⟨U, hUo, ?_⟩
    simpa [Set.ext_iff] using hU
  · refine fun ⟨h₁, h₂⟩ => isInducing_iff_nhds.2 fun ⟨i, x⟩ => ?_
    rw [Sigma.nhds_mk

Depends on / 依赖: IsEmbedding, IsEmbedding.sigmaMk, Set.ext_iff, Sigma.nhds_mk, comap_comap, comp_apply, ext_iff, filter_upwards, h.comp, h.isOpen_iff, hUo.mem_nhds, isInducing_iff_nhds, isOpen_iff, isOpen_range_sigmaMk, map_comap_of_mem, mem_nhds, nhds_eq_comap, nhds_mk, preimage_mem_comap, sigmaMk
-/
theorem inducing_sigma {f : Sigma σ -> X} :
    IsInducing f ↔ (forall i, IsInducing (f ∘ Sigma.mk i)) ∧
      (forall i, exists U, IsOpen U ∧ forall x, f x in U ↔ x.1 = i) := by
  refine ⟨fun h => ⟨fun i => h.comp IsEmbedding.sigmaMk.1, fun i => ?_⟩, ?_⟩
  · rcases h.isOpen_iff.1 (isOpen_range_sigmaMk (i := i)) with ⟨U, hUo, hU⟩
    refine ⟨U, hUo, ?_⟩
    simpa [Set.ext_iff] using hU
  · refine fun ⟨h₁, h₂⟩ => isInducing_iff_nhds.2 fun ⟨i, x⟩ => ?_
    rw [Sigma.nhds_mk]; rw [(h₁ i).nhds_eq_comap]; rw [comp_apply]; rw [← comap_comap]; rw [map_comap_of_mem]
    rcases h₂ i with ⟨U, hUo, hU⟩
    filter_upwards [preimage_mem_comap <| hUo.mem_nhds <| (hU _).2 rfl] with y hy
    simpa [hU] using hy

@[simp 1100]
/--
theorem `continuous_sigma_map` / 定理 `continuous_sigma_map`

English:
theorem continuous_sigma_map
  given: {f₁ : ι -> κ} {f₂ : forall i, σ i -> τ (f₁ i)}
  proof: continuous_sigma_iff.trans by
    simp only [Sigma.map, IsEmbedding.sigmaMk.continuous_iff, comp_def]

@[continuity, fun_prop]

中文:
定理 continuous_sigma_map
  条件: {f₁ : ι -> κ} {f₂ : 对任意 i, σ i -> τ (f₁ i)}
  证明: continuous_sigma_iff.trans by
    simp only [Sigma.map, IsEmbedding.sigmaMk.continuous_iff, comp_def]

@[continuity, fun_prop]

Depends on / 依赖: IsEmbedding, IsEmbedding.sigmaMk.continuous_iff, Sigma.map, comp_def, continuous_iff, continuous_sigma_iff, continuous_sigma_iff.trans, sigmaMk
-/
theorem continuous_sigma_map {f₁ : ι -> κ} {f₂ : forall i, σ i -> τ (f₁ i)} :
    Continuous (Sigma.map f₁ f₂) ↔ forall i, Continuous (f₂ i) :=
continuous_sigma_iff.trans by
    simp only [Sigma.map, IsEmbedding.sigmaMk.continuous_iff, comp_def]

@[continuity, fun_prop]
/--
theorem `Continuous.sigma_map` / 定理 `Continuous.sigma_map`

English:
theorem Continuous.sigma_map
  given: {f₁ : ι -> κ} {f₂ : forall i, σ i -> τ (f₁ i)} (hf : forall i, Continuous (f₂ i))
  proof: continuous_sigma_map.2 hf

中文:
定理 Continuous.sigma_map
  条件: {f₁ : ι -> κ} {f₂ : 对任意 i, σ i -> τ (f₁ i)} (hf : 对任意 i, Continuous (f₂ i))
  证明: continuous_sigma_map.2 hf

Depends on / 依赖: continuous_sigma_map
-/
theorem Continuous.sigma_map {f₁ : ι -> κ} {f₂ : forall i, σ i -> τ (f₁ i)} (hf : forall i, Continuous (f₂ i)) :
    Continuous (Sigma.map f₁ f₂) :=
  continuous_sigma_map.2 hf

/--
theorem `isOpenMap_sigma` / 定理 `isOpenMap_sigma`

English:
theorem isOpenMap_sigma
  given: {f : Sigma σ -> X}
  statement: IsOpenMap f ↔ forall i, IsOpenMap fun a => f ⟨i, a⟩
  proof: by
  simp only [isOpenMap_iff_nhds_le, Sigma.forall, Sigma.nhds_eq, map_map, comp_def]

中文:
定理 isOpenMap_sigma
  条件: {f : Sigma σ -> X}
  结论: IsOpenMap f ↔ 对任意 i, IsOpenMap fun a => f ⟨i, a⟩
  证明: by
  simp only [isOpenMap_iff_nhds_le, Sigma.forall, Sigma.nhds_eq, map_map, comp_def]

Depends on / 依赖: Sigma.forall, Sigma.nhds_eq, comp_def, isOpenMap_iff_nhds_le, map_map, nhds_eq
-/
theorem isOpenMap_sigma {f : Sigma σ -> X} : IsOpenMap f ↔ forall i, IsOpenMap fun a => f ⟨i, a⟩ := by
  simp only [isOpenMap_iff_nhds_le, Sigma.forall, Sigma.nhds_eq, map_map, comp_def]

/--
theorem `isOpenMap_sigma_map` / 定理 `isOpenMap_sigma_map`

English:
theorem isOpenMap_sigma_map
  given: {f₁ : ι -> κ} {f₂ : forall i, σ i -> τ (f₁ i)}
  proof: isOpenMap_sigma.trans
    forall_congr' fun i => (@IsOpenEmbedding.sigmaMk _ _ _ (f₁ i)).isOpenMap_iff.symm

中文:
定理 isOpenMap_sigma_map
  条件: {f₁ : ι -> κ} {f₂ : 对任意 i, σ i -> τ (f₁ i)}
  证明: isOpenMap_sigma.trans
    forall_congr' fun i => (@IsOpenEmbedding.sigmaMk _ _ _ (f₁ i)).isOpenMap_iff.symm

Depends on / 依赖: IsOpenEmbedding, IsOpenEmbedding.sigmaMk, forall_congr, isOpenMap_iff, isOpenMap_iff.symm, isOpenMap_sigma, isOpenMap_sigma.trans, sigmaMk
-/
theorem isOpenMap_sigma_map {f₁ : ι -> κ} {f₂ : forall i, σ i -> τ (f₁ i)} :
    IsOpenMap (Sigma.map f₁ f₂) ↔ forall i, IsOpenMap (f₂ i) :=
isOpenMap_sigma.trans
    forall_congr' fun i => (@IsOpenEmbedding.sigmaMk _ _ _ (f₁ i)).isOpenMap_iff.symm

/--
lemma `Topology.isInducing_sigmaMap` / 引理 `Topology.isInducing_sigmaMap`

English:
lemma Topology.isInducing_sigmaMap
  statement: {f₁ : ι -> κ} {f₂ : forall i, σ i -> τ (f₁ i)}
  proof: by
  simp only [isInducing_iff_nhds, Sigma.forall, Sigma.nhds_mk, Sigma.map_mk,
    ← map_sigma_mk_comap h₁, map_inj sigma_mk_injective]

中文:
引理 Topology.isInducing_sigmaMap
  结论: {f₁ : ι -> κ} {f₂ : 对任意 i, σ i -> τ (f₁ i)}
  证明: by
  simp only [isInducing_iff_nhds, Sigma.forall, Sigma.nhds_mk, Sigma.map_mk,
    ← map_sigma_mk_comap h₁, map_inj sigma_mk_injective]

Depends on / 依赖: Sigma.forall, Sigma.map_mk, Sigma.nhds_mk, isInducing_iff_nhds, map_inj, map_mk, map_sigma_mk_comap, nhds_mk, sigma_mk_injective
-/
lemma Topology.isInducing_sigmaMap {f₁ : ι -> κ} {f₂ : forall i, σ i -> τ (f₁ i)}
    (h₁ : Injective f₁) : IsInducing (Sigma.map f₁ f₂) ↔ forall i, IsInducing (f₂ i) := by
  simp only [isInducing_iff_nhds, Sigma.forall, Sigma.nhds_mk, Sigma.map_mk,
    ← map_sigma_mk_comap h₁, map_inj sigma_mk_injective]

/--
lemma `Topology.isEmbedding_sigmaMap` / 引理 `Topology.isEmbedding_sigmaMap`

English:
lemma Topology.isEmbedding_sigmaMap
  statement: {f₁ : ι -> κ} {f₂ : forall i, σ i -> τ (f₁ i)}
  proof: by
  simp only [isEmbedding_iff, isInducing_sigmaMap h, forall_and,
    h.sigma_map_iff]

中文:
引理 Topology.isEmbedding_sigmaMap
  结论: {f₁ : ι -> κ} {f₂ : 对任意 i, σ i -> τ (f₁ i)}
  证明: by
  simp only [isEmbedding_iff, isInducing_sigmaMap h, forall_and,
    h.sigma_map_iff]

Depends on / 依赖: forall_and, h.sigma_map_iff, isEmbedding_iff, isInducing_sigmaMap, sigma_map_iff
-/
lemma Topology.isEmbedding_sigmaMap {f₁ : ι -> κ} {f₂ : forall i, σ i -> τ (f₁ i)}
    (h : Injective f₁) : IsEmbedding (Sigma.map f₁ f₂) ↔ forall i, IsEmbedding (f₂ i) := by
  simp only [isEmbedding_iff, isInducing_sigmaMap h, forall_and,
    h.sigma_map_iff]

/--
lemma `Topology.isOpenEmbedding_sigmaMap` / 引理 `Topology.isOpenEmbedding_sigmaMap`

English:
lemma Topology.isOpenEmbedding_sigmaMap
  given: {f₁ : ι -> κ} {f₂ : forall i, σ i -> τ (f₁ i)} (h : Injective f₁)
  proof: by
  simp only [isOpenEmbedding_iff_isEmbedding_isOpenMap, isOpenMap_sigma_map, isEmbedding_sigmaMap h,
    forall_and]

中文:
引理 Topology.isOpenEmbedding_sigmaMap
  条件: {f₁ : ι -> κ} {f₂ : 对任意 i, σ i -> τ (f₁ i)} (h : Injective f₁)
  证明: by
  simp only [isOpenEmbedding_iff_isEmbedding_isOpenMap, isOpenMap_sigma_map, isEmbedding_sigmaMap h,
    forall_and]

Depends on / 依赖: forall_and, isEmbedding_sigmaMap, isOpenEmbedding_iff_isEmbedding_isOpenMap, isOpenMap_sigma_map
-/
lemma Topology.isOpenEmbedding_sigmaMap {f₁ : ι -> κ} {f₂ : forall i, σ i -> τ (f₁ i)} (h : Injective f₁) :
    IsOpenEmbedding (Sigma.map f₁ f₂) ↔ forall i, IsOpenEmbedding (f₂ i) := by
  simp only [isOpenEmbedding_iff_isEmbedding_isOpenMap, isOpenMap_sigma_map, isEmbedding_sigmaMap h,
    forall_and]

end Sigma

section ULift

set_option backward.isDefEq.respectTransparency false in
/--
theorem `ULift.isOpen_iff` / 定理 `ULift.isOpen_iff`

English:
theorem ULift.isOpen_iff
  given: [TopologicalSpace X] {s : Set (ULift.{v} X)}
  proof: by
  rw [ULift.topologicalSpace]; rw [← Equiv.ulift_apply]; rw [← Equiv.ulift.coinduced_symm]; rw [← isOpen_coinduced]

中文:
定理 ULift.isOpen_iff
  条件: [TopologicalSpace X] {s : Set (ULift.{v} X)}
  证明: by
  rw [ULift.topologicalSpace]; rw [← Equiv.ulift_apply]; rw [← Equiv.ulift.coinduced_symm]; rw [← isOpen_coinduced]

Depends on / 依赖: Equiv.ulift.coinduced_symm, Equiv.ulift_apply, ULift.topologicalSpace, coinduced_symm, isOpen_coinduced, topologicalSpace, ulift_apply
-/
theorem ULift.isOpen_iff [TopologicalSpace X] {s : Set (ULift.{v} X)} :
    IsOpen s ↔ IsOpen (ULift.up ⁻¹' s) := by
  rw [ULift.topologicalSpace]; rw [← Equiv.ulift_apply]; rw [← Equiv.ulift.coinduced_symm]; rw [← isOpen_coinduced]

/--
theorem `ULift.isClosed_iff` / 定理 `ULift.isClosed_iff`

English:
theorem ULift.isClosed_iff
  given: [TopologicalSpace X] {s : Set (ULift.{v} X)}
  proof: by
  rw [← isOpen_compl_iff]; rw [← isOpen_compl_iff]; rw [isOpen_iff]; rw [preimage_compl]

@[continuity, fun_prop]

中文:
定理 ULift.isClosed_iff
  条件: [TopologicalSpace X] {s : Set (ULift.{v} X)}
  证明: by
  rw [← isOpen_compl_iff]; rw [← isOpen_compl_iff]; rw [isOpen_iff]; rw [preimage_compl]

@[continuity, fun_prop]

Depends on / 依赖: isOpen_compl_iff, isOpen_iff, preimage_compl
-/
theorem ULift.isClosed_iff [TopologicalSpace X] {s : Set (ULift.{v} X)} :
    IsClosed s ↔ IsClosed (ULift.up ⁻¹' s) := by
  rw [← isOpen_compl_iff]; rw [← isOpen_compl_iff]; rw [isOpen_iff]; rw [preimage_compl]

@[continuity, fun_prop]
/--
theorem `continuous_uliftDown` / 定理 `continuous_uliftDown`

English:
theorem continuous_uliftDown
  given: [TopologicalSpace X]
  statement: Continuous (ULift.down : ULift.{v, u} X -> X)
  proof: continuous_induced_dom

@[continuity, fun_prop]

中文:
定理 continuous_uliftDown
  条件: [TopologicalSpace X]
  结论: Continuous (ULift.down : ULift.{v, u} X -> X)
  证明: continuous_induced_dom

@[continuity, fun_prop]

Depends on / 依赖: continuous_induced_dom
-/
theorem continuous_uliftDown [TopologicalSpace X] : Continuous (ULift.down : ULift.{v, u} X -> X) :=
  continuous_induced_dom

@[continuity, fun_prop]
/--
theorem `continuous_uliftUp` / 定理 `continuous_uliftUp`

English:
theorem continuous_uliftUp
  given: [TopologicalSpace X]
  statement: Continuous (ULift.up : X -> ULift.{v, u} X)
  proof: continuous_induced_rng.2 continuous_id

@[continuity, fun_prop]

中文:
定理 continuous_uliftUp
  条件: [TopologicalSpace X]
  结论: Continuous (ULift.up : X -> ULift.{v, u} X)
  证明: continuous_induced_rng.2 continuous_id

@[continuity, fun_prop]

Depends on / 依赖: continuous_id, continuous_induced_rng
-/
theorem continuous_uliftUp [TopologicalSpace X] : Continuous (ULift.up : X -> ULift.{v, u} X) :=
  continuous_induced_rng.2 continuous_id

@[continuity, fun_prop]
/--
theorem `continuous_uliftMap` / 定理 `continuous_uliftMap`

English:
theorem continuous_uliftMap
  statement: [TopologicalSpace X] [TopologicalSpace Y]
  proof: by
  change Continuous (ULift.up ∘ f ∘ ULift.down)
  fun_prop

@[fun_prop]

中文:
定理 continuous_uliftMap
  结论: [TopologicalSpace X] [TopologicalSpace Y]
  证明: by
  change Continuous (ULift.up ∘ f ∘ ULift.down)
  fun_prop

@[fun_prop]

Depends on / 依赖: Continuous, ULift.down, ULift.up, fun_prop
-/
theorem continuous_uliftMap [TopologicalSpace X] [TopologicalSpace Y]
    (f : X -> Y) (hf : Continuous f) :
    Continuous (ULift.map f : ULift.{u'} X -> ULift.{v'} Y) := by
  change Continuous (ULift.up ∘ f ∘ ULift.down)
  fun_prop

@[fun_prop]
/--
lemma `Topology.IsEmbedding.uliftDown` / 引理 `Topology.IsEmbedding.uliftDown`

English:
lemma Topology.IsEmbedding.uliftDown
  given: [TopologicalSpace X]
  proof: ⟨⟨rfl⟩, ULift.down_injective⟩

@[fun_prop]

中文:
引理 Topology.IsEmbedding.uliftDown
  条件: [TopologicalSpace X]
  证明: ⟨⟨rfl⟩, ULift.down_injective⟩

@[fun_prop]

Depends on / 依赖: ULift.down_injective, down_injective
-/
lemma Topology.IsEmbedding.uliftDown [TopologicalSpace X] :
    IsEmbedding (ULift.down : ULift.{v, u} X -> X) := ⟨⟨rfl⟩, ULift.down_injective⟩

@[fun_prop]
/--
lemma `Topology.IsClosedEmbedding.uliftDown` / 引理 `Topology.IsClosedEmbedding.uliftDown`

English:
lemma Topology.IsClosedEmbedding.uliftDown
  given: [TopologicalSpace X]
  proof: ⟨.uliftDown, by simp only [ULift.down_surjective.range_eq, isClosed_univ]⟩

中文:
引理 Topology.IsClosedEmbedding.uliftDown
  条件: [TopologicalSpace X]
  证明: ⟨.uliftDown, by simp only [ULift.down_surjective.range_eq, isClosed_univ]⟩

Depends on / 依赖: ULift.down_surjective.range_eq, down_surjective, isClosed_univ, range_eq, uliftDown
-/
lemma Topology.IsClosedEmbedding.uliftDown [TopologicalSpace X] :
    IsClosedEmbedding (ULift.down : ULift.{v, u} X -> X) :=
  ⟨.uliftDown, by simp only [ULift.down_surjective.range_eq, isClosed_univ]⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [TopologicalSpace
  signature: X] [DiscreteTopology X] : DiscreteTopology (ULift X)
  body: IsEmbedding.uliftDown.discreteTopology

中文:
实例 [TopologicalSpace
  签名: X] [DiscreteTopology X] : DiscreteTopology (ULift X)
  定义体: IsEmbedding.uliftDown.discreteTopology

Depends on / 依赖: IsEmbedding, IsEmbedding.uliftDown.discreteTopology, discreteTopology, uliftDown
-/
instance [TopologicalSpace X] [DiscreteTopology X] : DiscreteTopology (ULift X) :=
  IsEmbedding.uliftDown.discreteTopology

/-- Continuous maps between `ULift X` and `ULift Y` are equivalent to continuous maps between `X`
and `Y`. -/
@[simps]
/--
Definition of `ContinuousMap.uliftEquiv` / `ContinuousMap.uliftEquiv` 的定义

English:
definition ContinuousMap.uliftEquiv
  signature: (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
  body: ⟨ULift.down ∘ f ∘ ULift.up, by fun_prop⟩
  invFun f := ⟨ULift.up ∘ f ∘ ULift.down, by fun_prop⟩

中文:
定义 ContinuousMap.uliftEquiv
  签名: (X : 类型u) (Y : 类型v) [TopologicalSpace X] [TopologicalSpace Y]
  定义体: ⟨ULift.down ∘ f ∘ ULift.up, by fun_prop⟩
  invFun f := ⟨ULift.up ∘ f ∘ ULift.down, by fun_prop⟩

Depends on / 依赖: ULift.down, ULift.up, fun_prop
-/
def ContinuousMap.uliftEquiv (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y] :
    C(ULift.{v} X, ULift.{u} Y) ≃ C(X, Y) where
  toFun f := ⟨ULift.down ∘ f ∘ ULift.up, by fun_prop⟩
  invFun f := ⟨ULift.up ∘ f ∘ ULift.down, by fun_prop⟩

end ULift

section Monad

variable [TopologicalSpace X] {s : Set X} {t : Set s}

/--
theorem `IsOpen.trans` / 定理 `IsOpen.trans`

English:
theorem IsOpen.trans
  given: (ht : IsOpen t) (hs : IsOpen s)
  statement: IsOpen (t : Set X)
  proof: by
  rcases isOpen_induced_iff.mp ht with ⟨s', hs', rfl⟩
  rw [Subtype.image_preimage_coe]
  exact hs.inter hs'

中文:
定理 IsOpen.trans
  条件: (ht : IsOpen t) (hs : IsOpen s)
  结论: IsOpen (t : Set X)
  证明: by
  rcases isOpen_induced_iff.mp ht with ⟨s', hs', rfl⟩
  rw [Subtype.image_preimage_coe]
  exact hs.inter hs'

Depends on / 依赖: Subtype, Subtype.image_preimage_coe, hs.inter, image_preimage_coe, isOpen_induced_iff, isOpen_induced_iff.mp
-/
theorem IsOpen.trans (ht : IsOpen t) (hs : IsOpen s) : IsOpen (t : Set X) := by
  rcases isOpen_induced_iff.mp ht with ⟨s', hs', rfl⟩
  rw [Subtype.image_preimage_coe]
  exact hs.inter hs'

/--
theorem `IsClosed.trans` / 定理 `IsClosed.trans`

English:
theorem IsClosed.trans
  given: (ht : IsClosed t) (hs : IsClosed s)
  statement: IsClosed (t : Set X)
  proof: by
  rcases isClosed_induced_iff.mp ht with ⟨s', hs', rfl⟩
  rw [Subtype.image_preimage_coe]
  exact hs.inter hs'

中文:
定理 IsClosed.trans
  条件: (ht : IsClosed t) (hs : IsClosed s)
  结论: IsClosed (t : Set X)
  证明: by
  rcases isClosed_induced_iff.mp ht with ⟨s', hs', rfl⟩
  rw [Subtype.image_preimage_coe]
  exact hs.inter hs'

Depends on / 依赖: Subtype, Subtype.image_preimage_coe, hs.inter, image_preimage_coe, isClosed_induced_iff, isClosed_induced_iff.mp
-/
theorem IsClosed.trans (ht : IsClosed t) (hs : IsClosed s) : IsClosed (t : Set X) := by
  rcases isClosed_induced_iff.mp ht with ⟨s', hs', rfl⟩
  rw [Subtype.image_preimage_coe]
  exact hs.inter hs'

end Monad

section NhdsSet
variable [TopologicalSpace X] [TopologicalSpace Y]
  {s : Set X} {t : Set Y}

/--
theorem `nhdsSet_prod_le` / 定理 `nhdsSet_prod_le`

English:
theorem nhdsSet_prod_le
  given: (s : Set X) (t : Set Y)
  statement: 𝓝ˢ (s ×ˢ t) <= 𝓝ˢ s ×ˢ 𝓝ˢ t
  proof: ((hasBasis_nhdsSet _).prod (hasBasis_nhdsSet _)).ge_iff.2 fun (_u, _v) ⟨⟨huo, hsu⟩, hvo, htv⟩ =>
(huo.prod hvo).mem_nhdsSet.2 prod_mono hsu htv

中文:
定理 nhdsSet_prod_le
  条件: (s : Set X) (t : Set Y)
  结论: 𝓝ˢ (s ×ˢ t) <= 𝓝ˢ s ×ˢ 𝓝ˢ t
  证明: ((hasBasis_nhdsSet _).prod (hasBasis_nhdsSet _)).ge_iff.2 fun (_u, _v) ⟨⟨huo, hsu⟩, hvo, htv⟩ =>
(huo.prod hvo).mem_nhdsSet.2 prod_mono hsu htv

Depends on / 依赖: ge_iff, hasBasis_nhdsSet, huo.prod, mem_nhdsSet, prod_mono
-/
theorem nhdsSet_prod_le (s : Set X) (t : Set Y) : 𝓝ˢ (s ×ˢ t) <= 𝓝ˢ s ×ˢ 𝓝ˢ t :=
  ((hasBasis_nhdsSet _).prod (hasBasis_nhdsSet _)).ge_iff.2 fun (_u, _v) ⟨⟨huo, hsu⟩, hvo, htv⟩ =>
(huo.prod hvo).mem_nhdsSet.2 prod_mono hsu htv

/--
theorem `Filter.eventually_nhdsSet_prod_iff` / 定理 `Filter.eventually_nhdsSet_prod_iff`

English:
theorem Filter.eventually_nhdsSet_prod_iff
  given: {p : X × Y -> Prop}
  proof: by
  simp_rw [eventually_nhdsSet_iff_forall, forall_prod_set, nhds_prod_eq, eventually_prod_iff]

中文:
定理 Filter.eventually_nhdsSet_prod_iff
  条件: {p : X × Y -> 命题}
  证明: by
  simp_rw [eventually_nhdsSet_iff_forall, forall_prod_set, nhds_prod_eq, eventually_prod_iff]

Depends on / 依赖: eventually_nhdsSet_iff_forall, eventually_prod_iff, forall_prod_set, nhds_prod_eq, simp_rw
-/
theorem Filter.eventually_nhdsSet_prod_iff {p : X × Y -> Prop} :
    (forallᶠ q in 𝓝ˢ (s ×ˢ t), p q) ↔
      forall x in s, forall y in t,
          exists px : X -> Prop, (forallᶠ x' in 𝓝 x, px x') ∧ exists py : Y -> Prop, (forallᶠ y' in 𝓝 y, py y') ∧
            forall {x : X}, px x -> forall {y : Y}, py y -> p (x, y) := by
  simp_rw [eventually_nhdsSet_iff_forall, forall_prod_set, nhds_prod_eq, eventually_prod_iff]

/--
theorem `Filter.Eventually.prod_nhdsSet` / 定理 `Filter.Eventually.prod_nhdsSet`

English:
theorem Filter.Eventually.prod_nhdsSet
  statement: {p : X × Y -> Prop} {px : X -> Prop} {py : Y -> Prop}
  proof: nhdsSet_prod_le _ _ (mem_of_superset (prod_mem_prod hs ht) fun _ ⟨hx, hy⟩ => hp hx hy)

中文:
定理 Filter.Eventually.prod_nhdsSet
  结论: {p : X × Y -> 命题} {px : X -> 命题} {py : Y -> 命题}
  证明: nhdsSet_prod_le _ _ (mem_of_superset (prod_mem_prod hs ht) fun _ ⟨hx, hy⟩ => hp hx hy)

Depends on / 依赖: mem_of_superset, nhdsSet_prod_le, prod_mem_prod
-/
theorem Filter.Eventually.prod_nhdsSet {p : X × Y -> Prop} {px : X -> Prop} {py : Y -> Prop}
    (hp : forall {x : X}, px x -> forall {y : Y}, py y -> p (x, y)) (hs : forallᶠ x in 𝓝ˢ s, px x)
    (ht : forallᶠ y in 𝓝ˢ t, py y) : forallᶠ q in 𝓝ˢ (s ×ˢ t), p q :=
  nhdsSet_prod_le _ _ (mem_of_superset (prod_mem_prod hs ht) fun _ ⟨hx, hy⟩ => hp hx hy)

end NhdsSet
