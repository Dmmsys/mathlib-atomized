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

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {r : X → X → Prop} [t : TopologicalSpace X] : TopologicalSpace (Quot r) :=
  coinduced (Quot.mk r) t
/-
**instTopologicalSpaceQuotient** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instTopologicalSpaceQuotient {s : Setoid X} [t : TopologicalSpace X] : Top
ologicalSpace (Quotient s)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)
-/
instance instTopologicalSpaceQuotient {s : Setoid X} [t : TopologicalSpace X] :
    TopologicalSpace (Quotient s) :=
  coinduced Quotient.mk' t
/-
**instTopologicalSpaceSigma** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instTopologicalSpaceSigma {ι : Type*} {X : ι -> Type v} [t₂ : forall i, To
pologicalSpace (X i)] : TopologicalSpace (Sigma X)
参数：X i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instTopologicalSpaceSigma {ι : Type*} {X : ι → Type v} [t₂ : ∀ i, TopologicalSpace (X i)] :
    TopologicalSpace (Sigma X) :=
  ⨆ i, coinduced (Sigma.mk i) (t₂ i)
/-
**Pi.topologicalSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.topologicalSpace {ι : Type*} {Y : ι -> Type v} [t₂ : (i : ι) -> Topolog
icalSpace (Y i)] : TopologicalSpace ((i : ι) -> Y i)
参数：i : ι；Y i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Pi.topologicalSpace {ι : Type*} {Y : ι → Type v} [t₂ : (i : ι) → TopologicalSpace (Y i)] :
    TopologicalSpace ((i : ι) → Y i) :=
  ⨅ i, induced (fun f => f i) (t₂ i)
/-
**ULift.topologicalSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ULift.topologicalSpace [t : TopologicalSpace X] : TopologicalSpace (ULift.
{v, u} X)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : TopologicalSpace (Additive X) := ‹TopologicalSpace X›
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : TopologicalSpace (Multiplicative X) := ‹TopologicalSpace X›
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DiscreteTopology X] : DiscreteTopology (Additive X) := ‹DiscreteTopology X›
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DiscreteTopology X] : DiscreteTopology (Multiplicative X) := ‹DiscreteTopology X›
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CompactSpace X] : CompactSpace (Additive X) := ‹CompactSpace X›
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CompactSpace X] : CompactSpace (Multiplicative X) := ‹CompactSpace X›
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NoncompactSpace X] : NoncompactSpace (Additive X) := ‹NoncompactSpace X›
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NoncompactSpace X] : NoncompactSpace (Multiplicative X) := ‹NoncompactSpace X›
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [WeaklyLocallyCompactSpace X] : WeaklyLocallyCompactSpace (Additive X) :=
  ‹WeaklyLocallyCompactSpace X›
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [WeaklyLocallyCompactSpace X] : WeaklyLocallyCompactSpace (Multiplicative X) :=
  ‹WeaklyLocallyCompactSpace X›
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LocallyCompactSpace X] : LocallyCompactSpace (Additive X) := ‹LocallyCompactSpace X›
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LocallyCompactSpace X] : LocallyCompactSpace (Multiplicative X) := ‹LocallyCompactSpace X›
/-
**continuous_ofMul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_ofMul : Continuous (ofMul : X -> Additive X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
theorem continuous_ofMul : Continuous (ofMul : X → Additive X) := continuous_id
/-
**continuous_toMul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_toMul : Continuous (toMul : Additive X -> X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
theorem continuous_toMul : Continuous (toMul : Additive X → X) := continuous_id
/-
**continuous_ofAdd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_ofAdd : Continuous (ofAdd : X -> Multiplicative X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
theorem continuous_ofAdd : Continuous (ofAdd : X → Multiplicative X) := continuous_id
/-
**continuous_toAdd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_toAdd : Continuous (toAdd : Multiplicative X -> X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
theorem continuous_toAdd : Continuous (toAdd : Multiplicative X → X) := continuous_id
/-
**isOpenMap_ofMul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpenMap_ofMul : IsOpenMap (ofMul : X -> Additive X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenMap.id`：∀ {X : Type u_1} [inst : TopologicalSpace X], IsOpenMap id
-/
theorem isOpenMap_ofMul : IsOpenMap (ofMul : X → Additive X) := IsOpenMap.id
/-
**isOpenMap_toMul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpenMap_toMul : IsOpenMap (toMul : Additive X -> X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenMap.id`：∀ {X : Type u_1} [inst : TopologicalSpace X], IsOpenMap id
-/
theorem isOpenMap_toMul : IsOpenMap (toMul : Additive X → X) := IsOpenMap.id
/-
**isOpenMap_ofAdd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpenMap_ofAdd : IsOpenMap (ofAdd : X -> Multiplicative X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenMap.id`：∀ {X : Type u_1} [inst : TopologicalSpace X], IsOpenMap id
-/
theorem isOpenMap_ofAdd : IsOpenMap (ofAdd : X → Multiplicative X) := IsOpenMap.id
/-
**isOpenMap_toAdd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpenMap_toAdd : IsOpenMap (toAdd : Multiplicative X -> X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenMap.id`：∀ {X : Type u_1} [inst : TopologicalSpace X], IsOpenMap id
-/
theorem isOpenMap_toAdd : IsOpenMap (toAdd : Multiplicative X → X) := IsOpenMap.id
/-
**isClosedMap_ofMul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosedMap_ofMul : IsClosedMap (ofMul : X -> Additive X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosedMap.id`：∀ {X : Type u_1} [inst : TopologicalSpace X], IsClosedMa
p id
-/
theorem isClosedMap_ofMul : IsClosedMap (ofMul : X → Additive X) := IsClosedMap.id
/-
**isClosedMap_toMul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosedMap_toMul : IsClosedMap (toMul : Additive X -> X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosedMap.id`：∀ {X : Type u_1} [inst : TopologicalSpace X], IsClosedMa
p id
-/
theorem isClosedMap_toMul : IsClosedMap (toMul : Additive X → X) := IsClosedMap.id
/-
**isClosedMap_ofAdd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosedMap_ofAdd : IsClosedMap (ofAdd : X -> Multiplicative X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosedMap.id`：∀ {X : Type u_1} [inst : TopologicalSpace X], IsClosedMa
p id
-/
theorem isClosedMap_ofAdd : IsClosedMap (ofAdd : X → Multiplicative X) := IsClosedMap.id
/-
**isClosedMap_toAdd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosedMap_toAdd : IsClosedMap (toAdd : Multiplicative X -> X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosedMap.id`：∀ {X : Type u_1} [inst : TopologicalSpace X], IsClosedMa
p id
-/
theorem isClosedMap_toAdd : IsClosedMap (toAdd : Multiplicative X → X) := IsClosedMap.id
/-
**nhds_ofMul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_ofMul (x : X) : 𝓝 (ofMul x) = map ofMul (𝓝 x)
参数：x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nhds_ofMul (x : X) : 𝓝 (ofMul x) = map ofMul (𝓝 x) := rfl
/-
**nhds_ofAdd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_ofAdd (x : X) : 𝓝 (ofAdd x) = map ofAdd (𝓝 x)
参数：x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nhds_ofAdd (x : X) : 𝓝 (ofAdd x) = map ofAdd (𝓝 x) := rfl
/-
**nhds_toMul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_toMul (x : Additive X) : 𝓝 x.toMul = map toMul (𝓝 x)
参数：x : Additive X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nhds_toMul (x : Additive X) : 𝓝 x.toMul = map toMul (𝓝 x) := rfl
/-
**nhds_toAdd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_toAdd (x : Multiplicative X) : 𝓝 x.toAdd = map toAdd (𝓝 x)
参数：x : Multiplicative X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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

/-
**OrderDual.instTopologicalSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：OrderDual.instTopologicalSpace : TopologicalSpace Xᵒᵈ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance OrderDual.instTopologicalSpace : TopologicalSpace Xᵒᵈ := ‹_›
/-
**OrderDual.instDiscreteTopology** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：OrderDual.instDiscreteTopology [DiscreteTopology X] : DiscreteTopology Xᵒᵈ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance OrderDual.instDiscreteTopology [DiscreteTopology X] : DiscreteTopology Xᵒᵈ := ‹_›
/-
**continuous_toDual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_toDual : Continuous (toDual : X -> Xᵒᵈ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
theorem continuous_toDual : Continuous (toDual : X → Xᵒᵈ) := continuous_id
/-
**continuous_ofDual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_ofDual : Continuous (ofDual : Xᵒᵈ -> X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
theorem continuous_ofDual : Continuous (ofDual : Xᵒᵈ → X) := continuous_id
/-
**isOpenMap_toDual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpenMap_toDual : IsOpenMap (toDual : X -> Xᵒᵈ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenMap.id`：∀ {X : Type u_1} [inst : TopologicalSpace X], IsOpenMap id
-/
theorem isOpenMap_toDual : IsOpenMap (toDual : X → Xᵒᵈ) := IsOpenMap.id
/-
**isOpenMap_ofDual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpenMap_ofDual : IsOpenMap (ofDual : Xᵒᵈ -> X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenMap.id`：∀ {X : Type u_1} [inst : TopologicalSpace X], IsOpenMap id
-/
theorem isOpenMap_ofDual : IsOpenMap (ofDual : Xᵒᵈ → X) := IsOpenMap.id
/-
**isClosedMap_toDual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosedMap_toDual : IsClosedMap (toDual : X -> Xᵒᵈ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosedMap.id`：∀ {X : Type u_1} [inst : TopologicalSpace X], IsClosedMa
p id
-/
theorem isClosedMap_toDual : IsClosedMap (toDual : X → Xᵒᵈ) := IsClosedMap.id
/-
**isClosedMap_ofDual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosedMap_ofDual : IsClosedMap (ofDual : Xᵒᵈ -> X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosedMap.id`：∀ {X : Type u_1} [inst : TopologicalSpace X], IsClosedMa
p id
-/
theorem isClosedMap_ofDual : IsClosedMap (ofDual : Xᵒᵈ → X) := IsClosedMap.id
/-
**nhds_toDual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_toDual (x : X) : 𝓝 (toDual x) = map toDual (𝓝 x)
参数：x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nhds_toDual (x : X) : 𝓝 (toDual x) = map toDual (𝓝 x) := rfl
/-
**nhds_ofDual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_ofDual (x : X) : 𝓝 (ofDual x) = map ofDual (𝓝 x)
参数：x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nhds_ofDual (x : X) : 𝓝 (ofDual x) = map ofDual (𝓝 x) := rfl

variable [Preorder X] {x : X}
/-
**OrderDual.instNeBotNhdsWithinIoi** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：OrderDual.instNeBotNhdsWithinIoi [(𝓝[<] x).NeBot] : (𝓝[>] toDual x).NeBot
参数：𝓝[<] x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance OrderDual.instNeBotNhdsWithinIoi [(𝓝[<] x).NeBot] : (𝓝[>] toDual x).NeBot := ‹_›
/-
**OrderDual.instNeBotNhdsWithinIio** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：OrderDual.instNeBotNhdsWithinIio [(𝓝[>] x).NeBot] : (𝓝[<] toDual x).NeBot
参数：𝓝[>] x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance OrderDual.instNeBotNhdsWithinIio [(𝓝[>] x).NeBot] : (𝓝[<] toDual x).NeBot := ‹_›

end

/-
**Quotient.preimage_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Quotient.preimage_mem_nhds [TopologicalSpace X] [s : Setoid X] {V : Set <|
 Quotient s} {x : X} (hs : V in 𝓝 (Quotient.mk' x)) : Quotient.mk' ⁻¹' V in 𝓝 x
参数：hs : V in 𝓝 (Quotient.mk' x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)
· 使用定理 `preimage_nhds_coinduced`：preimage_nhds_coinduced [TopologicalSpace α] {π
 : α -> β} {s : Set β} {a : α} (hs : s in @nhds β (TopologicalSpace.coinduced π 
‹_›) (π a)) :…
-/
theorem Quotient.preimage_mem_nhds [TopologicalSpace X] [s : Setoid X] {V : Set <| Quotient s}
    {x : X} (hs : V ∈ 𝓝 (Quotient.mk' x)) : Quotient.mk' ⁻¹' V ∈ 𝓝 x :=
  preimage_nhds_coinduced hs

/-- The image of a dense set under `Quotient.mk'` is a dense set. -/
/-
**Dense.quotient** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Dense.quotient [Setoid X] [TopologicalSpace X] {s : Set X} (H : Dense s) :
 Dense (Quotient.mk' '' s)
参数：H : Dense s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DenseRange.dense_image`：DenseRange.dense_image {f : X -> Y} (hf' : Dense
Range f) (hf : Continuous f) (hs : Dense s) : Dense (f '' s)
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `Function.Surjective.denseRange`：Function.Surjective.denseRange (hf : Fun
ction.Surjective f) : DenseRange f
· 使用定理 `Quotient.mk''_surjective`：∀ {α : Sort u_1} {s₁ : Setoid α}, Function.Sur
jective Quotient.mk''
· 使用定理 `continuous_coinduced_rng`：continuous_coinduced_rng {t : TopologicalSpace
 α} : Continuous[t, coinduced f t] f

--- 原说明 ---
The image of a dense set under `Quotient.mk'` is a dense set.
-/
theorem Dense.quotient [Setoid X] [TopologicalSpace X] {s : Set X} (H : Dense s) :
    Dense (Quotient.mk' '' s) :=
  Quotient.mk''_surjective.denseRange.dense_image continuous_coinduced_rng H

/-- The composition of `Quotient.mk'` and a function with dense range has dense range. -/
/-
**DenseRange.quotient** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DenseRange.quotient [Setoid X] [TopologicalSpace X] {f : Y -> X} (hf : Den
seRange f) : DenseRange (Quotient.mk' ∘ f)
参数：hf : DenseRange f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DenseRange.comp`：DenseRange.comp {g : Y -> Z} {f : α -> Y} (hg : DenseRa
nge g) (hf : DenseRange f) (cg : Continuous g) : DenseRange (g ∘ f)
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `Function.Surjective.denseRange`：Function.Surjective.denseRange (hf : Fun
ction.Surjective f) : DenseRange f
· 使用定理 `Quotient.mk''_surjective`：∀ {α : Sort u_1} {s₁ : Setoid α}, Function.Sur
jective Quotient.mk''
· 使用定理 `continuous_coinduced_rng`：continuous_coinduced_rng {t : TopologicalSpace
 α} : Continuous[t, coinduced f t] f

--- 原说明 ---
The composition of `Quotient.mk'` and a function with dense range has dense rang
e.
-/
theorem DenseRange.quotient [Setoid X] [TopologicalSpace X] {f : Y → X} (hf : DenseRange f) :
    DenseRange (Quotient.mk' ∘ f) :=
  Quotient.mk''_surjective.denseRange.comp hf continuous_coinduced_rng
/-
**continuous_map_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_map_of_le {α : Type*} [TopologicalSpace α] {s t : Setoid α} (h 
: s <= t) : Continuous (Setoid.map_of_le h)
参数：h : s <= t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_coinduced_rng`：continuous_coinduced_rng {t : TopologicalSpace
 α} : Continuous[t, coinduced f t] f
-/
theorem continuous_map_of_le {α : Type*} [TopologicalSpace α]
    {s t : Setoid α} (h : s ≤ t) : Continuous (Setoid.map_of_le h) :=
  continuous_coinduced_rng
/-
**continuous_map_sInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_map_sInf {α : Type*} [TopologicalSpace α] {S : Set (Setoid α)} 
{s : Setoid α} (h : s in S) : Continuous (Setoid.map_sInf h)
参数：Setoid α；h : s in S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_coinduced_rng`：continuous_coinduced_rng {t : TopologicalSpace
 α} : Continuous[t, coinduced f t] f
-/
theorem continuous_map_sInf {α : Type*} [TopologicalSpace α]
    {S : Set (Setoid α)} {s : Setoid α} (h : s ∈ S) : Continuous (Setoid.map_sInf h) :=
  continuous_coinduced_rng
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {p : X → Prop} [TopologicalSpace X] [DiscreteTopology X] : DiscreteTopology (Subtype p) :=
  ⟨bot_unique fun s _ => ⟨(↑) '' s, isOpen_discrete _, preimage_image_eq _ Subtype.val_injective⟩⟩
/-
**Sum.discreteTopology** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Sum.discreteTopology [TopologicalSpace X] [TopologicalSpace Y] [h : Discre
teTopology X] [hY : DiscreteTopology Y] : DiscreteTopology (X oplus Y)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sup_eq_bot_iff`：sup_eq_bot_iff : a ⊔ b = ⊥ ↔ a = ⊥ ∧ b = ⊥
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `DiscreteTopology.eq_bot`：∀ {α : Type u_2} {t : TopologicalSpace α} [self
 : DiscreteTopology α], t = ⊥
· 使用定理 `coinduced_bot`：coinduced_bot : (⊥ : TopologicalSpace α).coinduced f = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
instance Sum.discreteTopology [TopologicalSpace X] [TopologicalSpace Y] [h : DiscreteTopology X]
    [hY : DiscreteTopology Y] : DiscreteTopology (X ⊕ Y) :=
  ⟨sup_eq_bot_iff.2 <| by simp [h.eq_bot, hY.eq_bot]⟩
/-
**Sigma.discreteTopology** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Sigma.discreteTopology {ι : Type*} {Y : ι -> Type v} [forall i, Topologica
lSpace (Y i)] [h : forall i, DiscreteTopology (Y i)] : DiscreteTopology (Sigma Y
)
参数：Y i；Y i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `iSup_eq_bot`：iSup_eq_bot : iSup s = ⊥ ↔ forall i, s i = ⊥
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DiscreteTopology.eq_bot`：∀ {α : Type u_2} {t : TopologicalSpace α} [self
 : DiscreteTopology α], t = ⊥
· 使用定理 `coinduced_bot`：coinduced_bot : (⊥ : TopologicalSpace α).coinduced f = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance Sigma.discreteTopology {ι : Type*} {Y : ι → Type v} [∀ i, TopologicalSpace (Y i)]
    [h : ∀ i, DiscreteTopology (Y i)] : DiscreteTopology (Sigma Y) :=
  ⟨iSup_eq_bot.2 fun _ => by simp only [(h _).eq_bot, coinduced_bot]⟩
/-
**Prod.indiscreteTopology** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.indiscreteTopology [TopologicalSpace X] [TopologicalSpace Y] [h : Ind
iscreteTopology X] [hY : IndiscreteTopology Y] : IndiscreteTopology (X × Y)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inf_eq_top_iff`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : Ord
erTop α] {a b : α}, a ⊓ b = ⊤ ↔ a = ⊤ ∧ b = ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IndiscreteTopology.eq_top`：∀ (α : Type u_2) {inst : TopologicalSpace α} 
[self : IndiscreteTopology α], inst = ⊤
· 使用定理 `induced_top`：induced_top : (⊤ : TopologicalSpace α).induced g = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
instance Prod.indiscreteTopology [TopologicalSpace X] [TopologicalSpace Y]
    [h : IndiscreteTopology X] [hY : IndiscreteTopology Y] : IndiscreteTopology (X × Y) :=
  ⟨inf_eq_top_iff.2 <| by simp [h.eq_top, hY.eq_top]⟩
/-
**Pi.indiscreteTopology** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.indiscreteTopology {ι : Type*} {Y : ι -> Type v} [forall i, Topological
Space (Y i)] [h : forall i, IndiscreteTopology (Y i)] : IndiscreteTopology ((i :
 ι) -> Y i)
参数：Y i；Y i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `iInf_eq_top`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] 
{s : ι → α}, iInf s = ⊤ ↔ ∀ (i : ι), s i = ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IndiscreteTopology.eq_top`：∀ (α : Type u_2) {inst : TopologicalSpace α} 
[self : IndiscreteTopology α], inst = ⊤
· 使用定理 `induced_top`：induced_top : (⊤ : TopologicalSpace α).induced g = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance Pi.indiscreteTopology {ι : Type*} {Y : ι → Type v} [∀ i, TopologicalSpace (Y i)]
    [h : ∀ i, IndiscreteTopology (Y i)] : IndiscreteTopology ((i : ι) → Y i) :=
  ⟨iInf_eq_top.2 fun _ => by simp only [(h _).eq_top, induced_top]⟩
/-
**comap_nhdsWithin_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_5} {β : Type u_6} [inst : TopologicalSpace β] (f : α → β) (y
 : β),   Filter.comap f (nhdsWithin y (Set.range f)) = Filter.comap f (nhds y)
参数：f : α → β；y : β；nhdsWithin y (Set.range f)；nhds y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.comap_inf_principal_range`：comap_inf_principal_range : comap m (g
 ⊓ 𝓟 (range m)) = comap m g
-/
@[simp] lemma comap_nhdsWithin_range {α β} [TopologicalSpace β] (f : α → β) (y : β) :
    comap f (𝓝[range f] y) = comap f (𝓝 y) := comap_inf_principal_range

section Top

variable [TopologicalSpace X]

/-
The 𝓝 filter and the subspace topology.
-/
/-
**mem_nhds_subtype** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_nhds_subtype (s : Set X) (x : { x // x in s }) (t : Set { x // x in s 
}) : t in 𝓝 x ↔ exists u in 𝓝 (x : X), Subtype.val ⁻¹' u subseteq t
参数：s : Set X；x : { x // x in s }；t : Set { x // x in s }。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_nhds_induced`：mem_nhds_induced [T : TopologicalSpace α] (f : β -> α)
 (a : β) (s : Set β) : s in @nhds β (TopologicalSpace.induced f T) a ↔ exists u 
in 𝓝 (…

--- 原说明 ---
The 𝓝 filter and the subspace topology.
-/
theorem mem_nhds_subtype (s : Set X) (x : { x // x ∈ s }) (t : Set { x // x ∈ s }) :
    t ∈ 𝓝 x ↔ ∃ u ∈ 𝓝 (x : X), Subtype.val ⁻¹' u ⊆ t :=
  mem_nhds_induced _ x t
/-
**nhds_subtype** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_subtype (s : Set X) (x : { x // x in s }) : 𝓝 x = comap (↑) (𝓝 (x : X
))
参数：s : Set X；x : { x // x in s }。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhds_induced`：nhds_induced [T : TopologicalSpace α] (f : β -> α) (a : β)
 : @nhds β (TopologicalSpace.induced f T) a = comap f (𝓝 (f a))
-/
theorem nhds_subtype (s : Set X) (x : { x // x ∈ s }) : 𝓝 x = comap (↑) (𝓝 (x : X)) :=
  nhds_induced _ x
/-
**nhds_subtype_eq_comap_nhdsWithin** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nhds_subtype_eq_comap_nhdsWithin (s : Set X) (x : { x // x in s }) : 𝓝 x =
 comap (↑) (𝓝[s] (x : X))
参数：s : Set X；x : { x // x in s }。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_subtype`：nhds_subtype (s : Set X) (x : { x // x in s }) : 𝓝 x = com
ap (↑) (𝓝 (x : X))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `comap_nhdsWithin_range`：∀ {α : Type u_5} {β : Type u_6} [inst : Topologi
calSpace β] (f : α → β) (y : β),   Filter.comap f (nhdsWithin y (Set.range f)) =
 Filter.coma…
· 使用定理 `Subtype.range_val`：range_val {s : Set α} : range (Subtype.val : s -> α) 
= s
-/
lemma nhds_subtype_eq_comap_nhdsWithin (s : Set X) (x : { x // x ∈ s }) :
    𝓝 x = comap (↑) (𝓝[s] (x : X)) := by
  rw [nhds_subtype, ← comap_nhdsWithin_range, Subtype.range_val]
/-
**nhdsWithin_subtype_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsWithin_subtype_eq_bot_iff {s t : Set X} {x : s} : 𝓝[((↑) : s -> X) ⁻¹'
 t] x = ⊥ ↔ 𝓝[t] (x : X) ⊓ 𝓟 s = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.inf_principal_eq_bot_iff_comap`：inf_principal_eq_bot_iff_comap {F
 : Filter α} {s : Set α} : F ⊓ 𝓟 s = ⊥ ↔ comap ((↑) : s -> α) F = ⊥
· 使用定理 `nhdsWithin.eq_1`：∀ {X : Type u_1} [inst : TopologicalSpace X] (x : X) (s
 : Set X), nhdsWithin x s = nhds x ⊓ Filter.principal s
· 使用定理 `Filter.comap_inf`：∀ {α : Type u_1} {β : Type u_2} {g₁ g₂ : Filter β} {m 
: α → β},   Filter.comap m (g₁ ⊓ g₂) = Filter.comap m g₁ ⊓ Filter.comap m g₂
· 使用定理 `Filter.comap_principal`：comap_principal {t : Set β} : comap m (𝓟 t) = 𝓟 
(m ⁻¹' t)
· 使用定理 `nhds_induced`：nhds_induced [T : TopologicalSpace α] (f : β -> α) (a : β)
 : @nhds β (TopologicalSpace.induced f T) a = comap f (𝓝 (f a))
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem nhdsWithin_subtype_eq_bot_iff {s t : Set X} {x : s} :
    𝓝[((↑) : s → X) ⁻¹' t] x = ⊥ ↔ 𝓝[t] (x : X) ⊓ 𝓟 s = ⊥ := by
  rw [inf_principal_eq_bot_iff_comap, nhdsWithin, nhdsWithin, comap_inf, comap_principal,
    nhds_induced]
/-
**nhds_ne_subtype_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_ne_subtype_eq_bot_iff {S : Set X} {x : S} : 𝓝[!=] x = ⊥ ↔ 𝓝[!=] (x : 
X) ⊓ 𝓟 S = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsWithin_subtype_eq_bot_iff`：nhdsWithin_subtype_eq_bot_iff {s t : Set 
X} {x : s} : 𝓝[((↑) : s -> X) ⁻¹' t] x = ⊥ ↔ 𝓝[t] (x : X) ⊓ 𝓟 s = ⊥
· 使用定理 `Set.preimage_compl`：preimage_compl {s : Set β} : f ⁻¹' sᶜ = (f ⁻¹' s)ᶜ
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `Function.Injective.preimage_image`：∀ {α : Type u_1} {β : Type u_2} {f : 
α → β}, Function.Injective f → ∀ (s : Set α), f ⁻¹' f '' s = s
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem nhds_ne_subtype_eq_bot_iff {S : Set X} {x : S} :
    𝓝[≠] x = ⊥ ↔ 𝓝[≠] (x : X) ⊓ 𝓟 S = ⊥ := by
  rw [← nhdsWithin_subtype_eq_bot_iff, preimage_compl, ← image_singleton,
    Subtype.coe_injective.preimage_image]
/-
**nhds_ne_subtype_neBot_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_ne_subtype_neBot_iff {S : Set X} {x : S} : (𝓝[!=] x).NeBot ↔ (𝓝[!=] (
x : X) ⊓ 𝓟 S).NeBot
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.neBot_iff`：neBot_iff {f : Filter α} : NeBot f ↔ f != ⊥
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `nhds_ne_subtype_eq_bot_iff`：nhds_ne_subtype_eq_bot_iff {S : Set X} {x : 
S} : 𝓝[!=] x = ⊥ ↔ 𝓝[!=] (x : X) ⊓ 𝓟 S = ⊥
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem nhds_ne_subtype_neBot_iff {S : Set X} {x : S} :
    (𝓝[≠] x).NeBot ↔ (𝓝[≠] (x : X) ⊓ 𝓟 S).NeBot := by
  rw [neBot_iff, neBot_iff, not_iff_not, nhds_ne_subtype_eq_bot_iff]

end Top

section IsDiscrete

variable {X : Type*} [TopologicalSpace X] {s : Set X}

/-- A subset `s` is **discrete** if the corresponding subtype (with the subspace topology) is a
discrete space. -/
/-
**IsDiscrete** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{X : Type u_5} → [TopologicalSpace X] → Set X → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subset `s` is **discrete** if the corresponding subtype (with the subspace top
ology) is a
discrete space.
-/
structure IsDiscrete (s : Set X) : Prop where
  to_subtype : DiscreteTopology ↥s
/-
**isDiscrete_iff_discreteTopology** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isDiscrete_iff_discreteTopology : IsDiscrete s ↔ DiscreteTopology s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDiscrete.to_subtype`：∀ {X : Type u_5} [inst : TopologicalSpace X] {s :
 Set X}, IsDiscrete s → DiscreteTopology ↑s
-/
lemma isDiscrete_iff_discreteTopology : IsDiscrete s ↔ DiscreteTopology s :=
  ⟨fun s ↦ s.to_subtype, fun s ↦ ⟨s⟩⟩
/-
**SetLike.isDiscrete_iff_discreteTopology** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SetLike.isDiscrete_iff_discreteTopology {S : Type*} [SetLike S X] {s : S} 
: IsDiscrete (s : Set X) ↔ DiscreteTopology s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDiscrete.to_subtype`：∀ {X : Type u_5} [inst : TopologicalSpace X] {s :
 Set X}, IsDiscrete s → DiscreteTopology ↑s
-/
lemma SetLike.isDiscrete_iff_discreteTopology {S : Type*} [SetLike S X] {s : S} :
    IsDiscrete (s : Set X) ↔ DiscreteTopology s :=
  ⟨fun s ↦ s.to_subtype, fun s ↦ ⟨s⟩⟩
/-
**DiscreteTopology.isDiscrete** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：DiscreteTopology.isDiscrete [DiscreteTopology s] : IsDiscrete s
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma DiscreteTopology.isDiscrete [DiscreteTopology s] : IsDiscrete s := ⟨inferInstance⟩

end IsDiscrete

/-- Cofinite topology. A set is open if it's empty or cofinite. -/
@[implicit_reducible]
/-
**TopologicalSpace.cofinite** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalSpace`。
形式化陈述：{X : Type u_5} → TopologicalSpace X
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Cofinite topology. A set is open if it's empty or cofinite.
-/
protected def TopologicalSpace.cofinite {X : Type*} : TopologicalSpace X where
  IsOpen s := s.Nonempty → Set.Finite sᶜ
  isOpen_univ := by simp
  isOpen_inter s t := by
    rintro hs ht ⟨x, hxs, hxt⟩
    rw [compl_inter]
    exact (hs ⟨x, hxs⟩).union (ht ⟨x, hxt⟩)
  isOpen_sUnion := by
    rintro s h ⟨x, t, hts, hzt⟩
    rw [compl_sUnion]
    exact Finite.sInter (mem_image_of_mem _ hts) (h t hts ⟨x, hzt⟩)

/-- A type synonym equipped with the topology whose open sets are the empty set and the sets with
finite complements. -/
/-
**CofiniteTopology** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：CofiniteTopology (X : Type*)
参数：X : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type synonym equipped with the topology whose open sets are the empty set and 
the sets with
finite complements.
-/
abbrev CofiniteTopology (X : Type*) :=
  WithTopology X .cofinite

namespace CofiniteTopology

/-- The identity equivalence between `X` and `CofiniteTopology X`. -/
/-
**CofiniteTopology.of** 是 Mathlib 中的一个定义，位于命名空间 `CofiniteTopology`。
形式化陈述：of : X ≃ CofiniteTopology X
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The identity equivalence between `X` and `CofiniteTopology X`.
-/
def of : X ≃ CofiniteTopology X := (WithTopology.equiv _ _).symm
/-
**CofiniteTopology.** 是 Mathlib 中的一个实例，位于命名空间 `CofiniteTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited X] : Inhabited (CofiniteTopology X) where default := of default

set_option backward.isDefEq.respectTransparency false in
/-
**CofiniteTopology.isOpen_iff** 是 Mathlib 中的一个定理，位于命名空间 `CofiniteTopology`。
形式化陈述：isOpen_iff {s : Set (CofiniteTopology X)} : IsOpen s ↔ s.Nonempty -> sᶜ.Fi
nite
参数：CofiniteTopology X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `WithTopology.preimage_toTopology`：preimage_toTopology (s : Set (WithTopo
logy X t)) : toTopology t ⁻¹' s = ofTopology '' s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.finite_image_iff`：finite_image_iff {s : Set α} {f : α -> β} (hi : In
jOn f s) : (f '' s).Finite ↔ s.Finite
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用引理 `WithTopology.ofTopology_injective`：ofTopology_injective : Function.Injec
tive (ofTopology (t
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isOpen_iff {s : Set (CofiniteTopology X)} : IsOpen s ↔ s.Nonempty → sᶜ.Finite := by
  simp_rw [isOpen_coinduced, TopologicalSpace.cofinite, isOpen_mk, ← Set.preimage_compl,
    WithTopology.preimage_toTopology, image_nonempty,
    finite_image_iff (WithTopology.ofTopology_injective _).injOn]
/-
**CofiniteTopology.isOpen_iff'** 是 Mathlib 中的一个定理，位于命名空间 `CofiniteTopology`。
形式化陈述：isOpen_iff' {s : Set (CofiniteTopology X)} : IsOpen s ↔ s = ∅ ∨ sᶜ.Finite
参数：CofiniteTopology X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isOpen_iff' {s : Set (CofiniteTopology X)} : IsOpen s ↔ s = ∅ ∨ sᶜ.Finite := by
  simp only [isOpen_iff, nonempty_iff_ne_empty, or_iff_not_imp_left]
/-
**CofiniteTopology.isClosed_iff** 是 Mathlib 中的一个定理，位于命名空间 `CofiniteTopology`。
形式化陈述：isClosed_iff {s : Set (CofiniteTopology X)} : IsClosed s ↔ s = univ ∨ s.Fi
nite
参数：CofiniteTopology X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isClosed_iff {s : Set (CofiniteTopology X)} : IsClosed s ↔ s = univ ∨ s.Finite := by
  simp only [← isOpen_compl_iff, isOpen_iff', compl_compl, compl_empty_iff]
/-
**CofiniteTopology.nhds_eq** 是 Mathlib 中的一个定理，位于命名空间 `CofiniteTopology`。
形式化陈述：nhds_eq (x : CofiniteTopology X) : 𝓝 x = pure x ⊔ cofinite
参数：x : CofiniteTopology X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.ext`：∀ {α : Type u_1} {f g : Filter α}, (∀ (s : Set α), s ∈ f ↔ s
 ∈ g) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.mem_sup`：mem_sup {f g : Filter α} {s : Set α} : s in f ⊔ g ↔ s in
 f ∧ s in g
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
theorem nhds_eq (x : CofiniteTopology X) : 𝓝 x = pure x ⊔ cofinite := by
  ext U
  simp_rw [mem_nhds_iff, isOpen_iff]
  constructor
  · rintro ⟨V, hVU, V_op, haV⟩
    exact mem_sup.mpr ⟨hVU haV, mem_of_superset (V_op ⟨_, haV⟩) hVU⟩
  · rintro ⟨hU : x ∈ U, hU' : Uᶜ.Finite⟩
    exact ⟨U, Subset.rfl, fun _ => hU', hU⟩
/-
**CofiniteTopology.mem_nhds_iff** 是 Mathlib 中的一个定理，位于命名空间 `CofiniteTopology`。
形式化陈述：mem_nhds_iff {x : CofiniteTopology X} {s : Set (CofiniteTopology X)} : s i
n 𝓝 x ↔ x in s ∧ sᶜ.Finite
参数：CofiniteTopology X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CofiniteTopology.nhds_eq`：nhds_eq (x : CofiniteTopology X) : 𝓝 x = pure 
x ⊔ cofinite
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_nhds_iff {x : CofiniteTopology X} {s : Set (CofiniteTopology X)} :
    s ∈ 𝓝 x ↔ x ∈ s ∧ sᶜ.Finite := by simp [nhds_eq]

end CofiniteTopology

end Constructions

section Prod

variable [TopologicalSpace X] [TopologicalSpace Y]

/-
**MapClusterPt.curry_prodMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MapClusterPt.curry_prodMap {α β : Type*} {f : α -> X} {g : β -> Y} {la : F
ilter α} {lb : Filter β} {x : X} {y : Y} (hf : MapClusterPt x la f) (hg : MapClu
sterPt y lb g) : MapClusterPt (x, y) (la.curry lb) (.map f g)
参数：hf : MapClusterPt x la f；hg : MapClusterPt y lb g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.mapClusterPt_iff_frequently`：Filter.HasBasis.mapClusterP
t_iff_frequently {ι : Sort*} {p : ι -> Prop} {s : ι -> Set X} (hx : (𝓝 x).HasBas
is p s) : MapClusterPt x F u ↔ fo…
· 使用定理 `Filter.HasBasis.prod_nhds`：Filter.HasBasis.prod_nhds {ιX ιY : Type*} {px
 : ιX -> Prop} {py : ιY -> Prop} {sx : ιX -> Set X} {sy : ιY -> Set Y} {x : X} {
y : Y} (hx : (𝓝…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
· 使用定理 `Filter.frequently_curry_iff`：frequently_curry_iff (p : (α × β) -> Prop) 
: (existsᶠ x in l.curry m, p x) ↔ existsᶠ x in l, existsᶠ y in m, p (x, y)
· 使用定理 `Filter.Frequently.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∃ᶠ (x : α) in f, q x
· 使用定理 `mapClusterPt_iff_frequently`：mapClusterPt_iff_frequently : MapClusterPt 
x F u ↔ forall s in 𝓝 x, existsᶠ a in F, u a in s
-/
theorem MapClusterPt.curry_prodMap {α β : Type*}
    {f : α → X} {g : β → Y} {la : Filter α} {lb : Filter β} {x : X} {y : Y}
    (hf : MapClusterPt x la f) (hg : MapClusterPt y lb g) :
    MapClusterPt (x, y) (la.curry lb) (.map f g) := by
  rw [mapClusterPt_iff_frequently] at hf hg
  rw [((𝓝 x).basis_sets.prod_nhds (𝓝 y).basis_sets).mapClusterPt_iff_frequently]
  rintro ⟨s, t⟩ ⟨hs, ht⟩
  rw [frequently_curry_iff]
  exact (hf s hs).mono fun x hx ↦ (hg t ht).mono fun y hy ↦ ⟨hx, hy⟩
/-
**MapClusterPt.prodMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MapClusterPt.prodMap {α β : Type*} {f : α -> X} {g : β -> Y} {la : Filter 
α} {lb : Filter β} {x : X} {y : Y} (hf : MapClusterPt x la f) (hg : MapClusterPt
 y lb g) : MapClusterPt (x, y) (la ×ˢ lb) (.map f g)
参数：hf : MapClusterPt x la f；hg : MapClusterPt y lb g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MapClusterPt.mono`：MapClusterPt.mono {G : Filter α} (h : MapClusterPt x 
F u) (hle : F <= G) : MapClusterPt x G u
· 使用定理 `MapClusterPt.curry_prodMap`：MapClusterPt.curry_prodMap {α β : Type*} {f 
: α -> X} {g : β -> Y} {la : Filter α} {lb : Filter β} {x : X} {y : Y} (hf : Map
ClusterPt x la f…
· 使用定理 `Filter.map_mono`：map_mono : Monotone (map m)
· 使用定理 `Filter.curry_le_prod`：curry_le_prod : l.curry m <= l ×ˢ m
-/
theorem MapClusterPt.prodMap {α β : Type*}
    {f : α → X} {g : β → Y} {la : Filter α} {lb : Filter β} {x : X} {y : Y}
    (hf : MapClusterPt x la f) (hg : MapClusterPt y lb g) :
    MapClusterPt (x, y) (la ×ˢ lb) (.map f g) :=
  (hf.curry_prodMap hg).mono <| map_mono curry_le_prod

end Prod

section Bool

/-
**continuous_bool_rng** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：continuous_bool_rng [TopologicalSpace X] {f : X -> Bool} (b : Bool) : Cont
inuous f ↔ IsClopen (f ⁻¹' {b})
参数：b : Bool。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuous_discrete_rng`：continuous_discrete_rng {α} [TopologicalSpace α
] [TopologicalSpace β] [DiscreteTopology β] {f : α -> β} : Continuous f ↔ forall
 b : β, IsOpe…
· 使用定理 `instDiscreteTopologyBool`：DiscreteTopology Bool
· 使用定理 `Bool.forall_bool'`：∀ {p : Bool → Prop} (b : Bool), (∀ (x : Bool), p x) ↔
 p b ∧ p !b
· 使用定理 `IsClopen.eq_1`：∀ {X : Type u} [inst : TopologicalSpace X] (s : Set X), I
sClopen s = (IsClosed s ∧ IsOpen s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isOpen_compl_iff`：∀ {X : Type u} {s : Set X} [inst : TopologicalSpace X]
, IsOpen sᶜ ↔ IsClosed s
· 使用定理 `Set.preimage_compl`：preimage_compl {s : Set β} : f ⁻¹' sᶜ = (f ⁻¹' s)ᶜ
· 使用定理 `Bool.compl_singleton`：compl_singleton (b : Bool) : ({b}ᶜ : Set Bool) = {
!b}
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma continuous_bool_rng [TopologicalSpace X] {f : X → Bool} (b : Bool) :
    Continuous f ↔ IsClopen (f ⁻¹' {b}) := by
  rw [continuous_discrete_rng, Bool.forall_bool' b, IsClopen, ← isOpen_compl_iff, ← preimage_compl,
    Bool.compl_singleton, and_comm]

end Bool

section Subtype

variable [TopologicalSpace X] [TopologicalSpace Y] {p : X → Prop}

@[fun_prop]
/-
**Topology.IsInducing.subtypeVal** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsInducing.subtypeVal {t : Set Y} : IsInducing ((↑) : t -> Y)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Topology.IsInducing.subtypeVal {t : Set Y} : IsInducing ((↑) : t → Y) := ⟨rfl⟩
/-
**Topology.IsInducing.of_codRestrict** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsInducing.of_codRestrict {f : X -> Y} {t : Set Y} (ht : forall x
, f x in t) (h : IsInducing (t.codRestrict f ht)) : IsInducing f
参数：ht : forall x, f x in t；h : IsInducing (t.codRestrict f ht)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3}
 {f : X → Y} {g : Y → Z} [inst : TopologicalSpace Y]   [inst_1 : TopologicalSpac
e X] [inst_2 :…
· 使用引理 `Topology.IsInducing.subtypeVal`：Topology.IsInducing.subtypeVal {t : Set 
Y} : IsInducing ((↑) : t -> Y)
-/
lemma Topology.IsInducing.of_codRestrict {f : X → Y} {t : Set Y} (ht : ∀ x, f x ∈ t)
    (h : IsInducing (t.codRestrict f ht)) : IsInducing f := subtypeVal.comp h

@[fun_prop]
/-
**Topology.IsEmbedding.subtypeVal** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsEmbedding.subtypeVal : IsEmbedding ((↑) : Subtype p -> X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsInducing.subtypeVal`：Topology.IsInducing.subtypeVal {t : Set 
Y} : IsInducing ((↑) : t -> Y)
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
lemma Topology.IsEmbedding.subtypeVal : IsEmbedding ((↑) : Subtype p → X) :=
  ⟨.subtypeVal, Subtype.coe_injective⟩

@[fun_prop]
/-
**Topology.IsClosedEmbedding.subtypeVal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Topology.IsClosedEmbedding.subtypeVal (h : IsClosed {a | p a}) : IsClosedE
mbedding ((↑) : Subtype p -> X)
参数：h : IsClosed {a | p a}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsEmbedding.subtypeVal`：Topology.IsEmbedding.subtypeVal : IsEmb
edding ((↑) : Subtype p -> X)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
-/
theorem Topology.IsClosedEmbedding.subtypeVal (h : IsClosed {a | p a}) :
    IsClosedEmbedding ((↑) : Subtype p → X) :=
  ⟨.subtypeVal, by rwa [Subtype.range_coe_subtype]⟩

@[continuity, fun_prop]
/-
**continuous_subtype_val** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_subtype_val : Continuous (@Subtype.val X p)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_induced_dom`：continuous_induced_dom {t : TopologicalSpace β} 
: Continuous[induced f t, t] f
-/
theorem continuous_subtype_val : Continuous (@Subtype.val X p) :=
  continuous_induced_dom
/-
**Continuous.subtype_val** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.subtype_val {f : Y -> Subtype p} (hf : Continuous f) : Continuo
us fun x => (f x : X)
参数：hf : Continuous f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
-/
theorem Continuous.subtype_val {f : Y → Subtype p} (hf : Continuous f) :
    Continuous fun x => (f x : X) :=
  continuous_subtype_val.comp hf

@[fun_prop]
/-
**IsOpen.isOpenEmbedding_subtypeVal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.isOpenEmbedding_subtypeVal {s : Set X} (hs : IsOpen s) : IsOpenEmbe
dding ((↑) : s -> X)
参数：hs : IsOpen s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsEmbedding.subtypeVal`：Topology.IsEmbedding.subtypeVal : IsEmb
edding ((↑) : Subtype p -> X)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
-/
theorem IsOpen.isOpenEmbedding_subtypeVal {s : Set X} (hs : IsOpen s) :
    IsOpenEmbedding ((↑) : s → X) :=
  ⟨.subtypeVal, (@Subtype.range_coe _ s).symm ▸ hs⟩
/-
**IsOpen.isOpenMap_subtype_val** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.isOpenMap_subtype_val {s : Set X} (hs : IsOpen s) : IsOpenMap ((↑) 
: s -> X)
参数：hs : IsOpen s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsOpenEmbedding.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} {f :
 X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.Is
OpenEmbedding f → IsOpen…
· 使用定理 `IsOpen.isOpenEmbedding_subtypeVal`：IsOpen.isOpenEmbedding_subtypeVal {s 
: Set X} (hs : IsOpen s) : IsOpenEmbedding ((↑) : s -> X)
-/
theorem IsOpen.isOpenMap_subtype_val {s : Set X} (hs : IsOpen s) : IsOpenMap ((↑) : s → X) :=
  hs.isOpenEmbedding_subtypeVal.isOpenMap
/-
**IsOpenMap.domRestrict** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpenMap.domRestrict {f : X -> Y} (hf : IsOpenMap f) {s : Set X} (hs : Is
Open s) : IsOpenMap (s.domRestrict f)
参数：hf : IsOpenMap f；hs : IsOpen s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenMap.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} {f : X → 
Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : TopologicalSpace Y] [inst
_2 :…
· 使用定理 `IsOpen.isOpenMap_subtype_val`：IsOpen.isOpenMap_subtype_val {s : Set X} (
hs : IsOpen s) : IsOpenMap ((↑) : s -> X)
-/
theorem IsOpenMap.domRestrict {f : X → Y} (hf : IsOpenMap f) {s : Set X} (hs : IsOpen s) :
    IsOpenMap (s.domRestrict f) :=
  hf.comp hs.isOpenMap_subtype_val

@[deprecated (since := "2026-07-19")] alias IsOpenMap.restrict := IsOpenMap.domRestrict

@[fun_prop]
/-
**IsClosed.isClosedEmbedding_subtypeVal** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsClosed.isClosedEmbedding_subtypeVal {s : Set X} (hs : IsClosed s) : IsCl
osedEmbedding ((↑) : s -> X)
参数：hs : IsClosed s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsClosedEmbedding.subtypeVal`：Topology.IsClosedEmbedding.subtyp
eVal (h : IsClosed {a | p a}) : IsClosedEmbedding ((↑) : Subtype p -> X)
-/
lemma IsClosed.isClosedEmbedding_subtypeVal {s : Set X} (hs : IsClosed s) :
    IsClosedEmbedding ((↑) : s → X) := .subtypeVal hs
/-
**IsClosed.isClosedMap_subtype_val** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.isClosedMap_subtype_val {s : Set X} (hs : IsClosed s) : IsClosedM
ap ((↑) : s -> X)
参数：hs : IsClosed s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsClosedEmbedding.isClosedMap`：∀ {X : Type u_1} {Y : Type u_2} 
{f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topolog
y.IsClosedEmbedding f → IsCl…
· 使用引理 `IsClosed.isClosedEmbedding_subtypeVal`：IsClosed.isClosedEmbedding_subtyp
eVal {s : Set X} (hs : IsClosed s) : IsClosedEmbedding ((↑) : s -> X)
-/
theorem IsClosed.isClosedMap_subtype_val {s : Set X} (hs : IsClosed s) :
    IsClosedMap ((↑) : s → X) :=
  hs.isClosedEmbedding_subtypeVal.isClosedMap
/-
**IsClosedMap.domRestrict** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosedMap.domRestrict {f : X -> Y} (hf : IsClosedMap f) {s : Set X} (hs 
: IsClosed s) : IsClosedMap (s.domRestrict f)
参数：hf : IsClosedMap f；hs : IsClosed s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosedMap.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} {f : X 
→ Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : TopologicalSpace Y] [in
st_2 :…
· 使用定理 `IsClosed.isClosedMap_subtype_val`：IsClosed.isClosedMap_subtype_val {s : 
Set X} (hs : IsClosed s) : IsClosedMap ((↑) : s -> X)
-/
theorem IsClosedMap.domRestrict {f : X → Y} (hf : IsClosedMap f) {s : Set X}
    (hs : IsClosed s) : IsClosedMap (s.domRestrict f) :=
  hf.comp hs.isClosedMap_subtype_val

@[deprecated (since := "2026-07-19")] alias IsClosedMap.restrict := IsClosedMap.domRestrict

@[continuity, fun_prop]
/-
**Continuous.subtype_mk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.subtype_mk {f : Y -> X} (h : Continuous f) (hp : forall x, p (f
 x)) : Continuous fun x => (⟨f x, hp x⟩ : Subtype p)
参数：h : Continuous f；hp : forall x, p (f x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_induced_rng`：continuous_induced_rng {g : γ -> α} {t₂ : Topolo
gicalSpace β} {t₁ : TopologicalSpace γ} : Continuous[t₁, induced f t₂] g ↔ Conti
nuous[t₁, t₂…
-/
theorem Continuous.subtype_mk {f : Y → X} (h : Continuous f) (hp : ∀ x, p (f x)) :
    Continuous fun x => (⟨f x, hp x⟩ : Subtype p) :=
  continuous_induced_rng.2 h
/-
**IsOpenMap.subtype_mk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpenMap.subtype_mk {f : Y -> X} (hf : IsOpenMap f) (hp : forall x, p (f 
x)) : IsOpenMap fun x => (⟨f x, hp x⟩ : Subtype p)
参数：hf : IsOpenMap f；hp : forall x, p (f x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `and_congr_right'`：∀ {b c a : Prop}, (b ↔ c) → (a ∧ b ↔ a ∧ c)
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
-/
theorem IsOpenMap.subtype_mk {f : Y → X} (hf : IsOpenMap f) (hp : ∀ x, p (f x)) :
    IsOpenMap fun x ↦ (⟨f x, hp x⟩ : Subtype p) := fun u hu ↦ by
  convert! (hf u hu).preimage continuous_subtype_val
  exact Set.ext fun _ ↦ exists_congr fun _ ↦ and_congr_right' Subtype.ext_iff
/-
**IsClosedMap.subtype_mk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosedMap.subtype_mk {f : Y -> X} (hf : IsClosedMap f) (hp : forall x, p
 (f x)) : IsClosedMap fun x => (⟨f x, hp x⟩ : Subtype p)
参数：hf : IsClosedMap f；hp : forall x, p (f x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `and_congr_right'`：∀ {b c a : Prop}, (b ↔ c) → (a ∧ b ↔ a ∧ c)
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
-/
theorem IsClosedMap.subtype_mk {f : Y → X} (hf : IsClosedMap f) (hp : ∀ x, p (f x)) :
    IsClosedMap fun x ↦ (⟨f x, hp x⟩ : Subtype p) := fun u hu ↦ by
  convert! (hf u hu).preimage continuous_subtype_val
  exact Set.ext fun _ ↦ exists_congr fun _ ↦ and_congr_right' Subtype.ext_iff

@[fun_prop]
/-
**Continuous.subtype_coind** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.subtype_coind {f : Y -> X} (hf : Continuous f) (hp : forall x, 
p (f x)) : Continuous (Subtype.coind f hp)
参数：hf : Continuous f；hp : forall x, p (f x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.subtype_mk`：Continuous.subtype_mk {f : Y -> X} (h : Continuou
s f) (hp : forall x, p (f x)) : Continuous fun x => (⟨f x, hp x⟩ : Subtype p)
-/
theorem Continuous.subtype_coind {f : Y → X} (hf : Continuous f) (hp : ∀ x, p (f x)) :
    Continuous (Subtype.coind f hp) :=
  hf.subtype_mk hp
/-
**IsOpenMap.subtype_coind** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpenMap.subtype_coind {f : Y -> X} (hf : IsOpenMap f) (hp : forall x, p 
(f x)) : IsOpenMap (Subtype.coind f hp)
参数：hf : IsOpenMap f；hp : forall x, p (f x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenMap.subtype_mk`：IsOpenMap.subtype_mk {f : Y -> X} (hf : IsOpenMap 
f) (hp : forall x, p (f x)) : IsOpenMap fun x => (⟨f x, hp x⟩ : Subtype p)
-/
theorem IsOpenMap.subtype_coind {f : Y → X} (hf : IsOpenMap f) (hp : ∀ x, p (f x)) :
    IsOpenMap (Subtype.coind f hp) :=
  hf.subtype_mk hp
/-
**IsClosedMap.subtype_coind** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosedMap.subtype_coind {f : Y -> X} (hf : IsClosedMap f) (hp : forall x
, p (f x)) : IsClosedMap (Subtype.coind f hp)
参数：hf : IsClosedMap f；hp : forall x, p (f x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosedMap.subtype_mk`：IsClosedMap.subtype_mk {f : Y -> X} (hf : IsClos
edMap f) (hp : forall x, p (f x)) : IsClosedMap fun x => (⟨f x, hp x⟩ : Subtype 
p)
-/
theorem IsClosedMap.subtype_coind {f : Y → X} (hf : IsClosedMap f) (hp : ∀ x, p (f x)) :
    IsClosedMap (Subtype.coind f hp) :=
  hf.subtype_mk hp

@[fun_prop]
/-
**Continuous.subtype_map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.subtype_map {f : X -> Y} (h : Continuous f) {q : Y -> Prop} (hp
q : forall x, p x -> q (f x)) : Continuous (Subtype.map f hpq)
参数：h : Continuous f；hpq : forall x, p x -> q (f x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.subtype_mk`：Continuous.subtype_mk {f : Y -> X} (h : Continuou
s f) (hp : forall x, p (f x)) : Continuous fun x => (⟨f x, hp x⟩ : Subtype p)
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
-/
theorem Continuous.subtype_map {f : X → Y} (h : Continuous f) {q : Y → Prop}
    (hpq : ∀ x, p x → q (f x)) : Continuous (Subtype.map f hpq) :=
  (h.comp continuous_subtype_val).subtype_mk _
/-
**IsOpenMap.subtype_map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpenMap.subtype_map {f : X -> Y} (hf : IsOpenMap f) {s : Set X} {t : Set
 Y} (hs : IsOpen s) (hst : forall x in s, f x in t) : IsOpenMap (Subtype.map f h
st)
参数：hf : IsOpenMap f；hs : IsOpen s；hst : forall x in s, f x in t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenMap.subtype_mk`：IsOpenMap.subtype_mk {f : Y -> X} (hf : IsOpenMap 
f) (hp : forall x, p (f x)) : IsOpenMap fun x => (⟨f x, hp x⟩ : Subtype p)
· 使用定理 `IsOpenMap.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} {f : X → 
Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : TopologicalSpace Y] [inst
_2 :…
· 使用定理 `IsOpen.isOpenMap_subtype_val`：IsOpen.isOpenMap_subtype_val {s : Set X} (
hs : IsOpen s) : IsOpenMap ((↑) : s -> X)
-/
theorem IsOpenMap.subtype_map {f : X → Y} (hf : IsOpenMap f) {s : Set X} {t : Set Y} (hs : IsOpen s)
    (hst : ∀ x ∈ s, f x ∈ t) : IsOpenMap (Subtype.map f hst) :=
  (hf.comp hs.isOpenMap_subtype_val).subtype_mk _
/-
**IsClosedMap.subtype_map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosedMap.subtype_map {f : X -> Y} (hf : IsClosedMap f) {s : Set X} {t :
 Set Y} (hs : IsClosed s) (hst : forall x in s, f x in t) : IsClosedMap (Subtype
.map f hst)
参数：hf : IsClosedMap f；hs : IsClosed s；hst : forall x in s, f x in t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosedMap.subtype_mk`：IsClosedMap.subtype_mk {f : Y -> X} (hf : IsClos
edMap f) (hp : forall x, p (f x)) : IsClosedMap fun x => (⟨f x, hp x⟩ : Subtype 
p)
· 使用定理 `IsClosedMap.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} {f : X 
→ Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : TopologicalSpace Y] [in
st_2 :…
· 使用定理 `IsClosed.isClosedMap_subtype_val`：IsClosed.isClosedMap_subtype_val {s : 
Set X} (hs : IsClosed s) : IsClosedMap ((↑) : s -> X)
-/
theorem IsClosedMap.subtype_map {f : X → Y} (hf : IsClosedMap f) {s : Set X} {t : Set Y}
    (hs : IsClosed s) (hst : ∀ x ∈ s, f x ∈ t) : IsClosedMap (Subtype.map f hst) :=
  (hf.comp hs.isClosedMap_subtype_val).subtype_mk _
/-
**continuous_inclusion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_inclusion {s t : Set X} (h : s subseteq t) : Continuous (inclus
ion h)
参数：h : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.subtype_map`：Continuous.subtype_map {f : X -> Y} (h : Continu
ous f) {q : Y -> Prop} (hpq : forall x, p x -> q (f x)) : Continuous (Subtype.ma
p f hpq)
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
theorem continuous_inclusion {s t : Set X} (h : s ⊆ t) : Continuous (inclusion h) :=
  continuous_id.subtype_map h
/-
**IsOpen.isOpenMap_inclusion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.isOpenMap_inclusion {s t : Set X} (hs : IsOpen s) (h : s subseteq t
) : IsOpenMap (inclusion h)
参数：hs : IsOpen s；h : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenMap.subtype_map`：IsOpenMap.subtype_map {f : X -> Y} (hf : IsOpenMa
p f) {s : Set X} {t : Set Y} (hs : IsOpen s) (hst : forall x in s, f x in t) : I
sOpenMap (S…
· 使用定理 `IsOpenMap.id`：∀ {X : Type u_1} [inst : TopologicalSpace X], IsOpenMap id
-/
theorem IsOpen.isOpenMap_inclusion {s t : Set X} (hs : IsOpen s) (h : s ⊆ t) :
    IsOpenMap (inclusion h) :=
  IsOpenMap.id.subtype_map hs h
/-
**IsClosed.isClosedMap_inclusion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.isClosedMap_inclusion {s t : Set X} (hs : IsClosed s) (h : s subs
eteq t) : IsClosedMap (inclusion h)
参数：hs : IsClosed s；h : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosedMap.subtype_map`：IsClosedMap.subtype_map {f : X -> Y} (hf : IsCl
osedMap f) {s : Set X} {t : Set Y} (hs : IsClosed s) (hst : forall x in s, f x i
n t) : IsClos…
· 使用定理 `IsClosedMap.id`：∀ {X : Type u_1} [inst : TopologicalSpace X], IsClosedMa
p id
-/
theorem IsClosed.isClosedMap_inclusion {s t : Set X} (hs : IsClosed s) (h : s ⊆ t) :
    IsClosedMap (inclusion h) :=
  IsClosedMap.id.subtype_map hs h

@[simp]
/-
**continuous_rangeFactorization_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_rangeFactorization_iff {f : X -> Y} : Continuous (rangeFactoriz
ation f) ↔ Continuous f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsInducing.continuous_iff`：continuous_iff (hg : IsInducing g) :
 Continuous f ↔ Continuous (g ∘ f)
· 使用引理 `Topology.IsInducing.subtypeVal`：Topology.IsInducing.subtypeVal {t : Set 
Y} : IsInducing ((↑) : t -> Y)
-/
theorem continuous_rangeFactorization_iff {f : X → Y} :
    Continuous (rangeFactorization f) ↔ Continuous f :=
  IsInducing.subtypeVal.continuous_iff

@[continuity, fun_prop]
/-
**Continuous.rangeFactorization** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.rangeFactorization {f : X -> Y} (hf : Continuous f) : Continuou
s (rangeFactorization f)
参数：hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_rangeFactorization_iff`：continuous_rangeFactorization_iff {f 
: X -> Y} : Continuous (rangeFactorization f) ↔ Continuous f
-/
theorem Continuous.rangeFactorization {f : X → Y} (hf : Continuous f) :
    Continuous (rangeFactorization f) :=
  continuous_rangeFactorization_iff.mpr hf
/-
**continuousAt_subtype_val** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousAt_subtype_val {p : X -> Prop} {x : Subtype p} : ContinuousAt ((
↑) : Subtype p -> X) x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
-/
theorem continuousAt_subtype_val {p : X → Prop} {x : Subtype p} :
    ContinuousAt ((↑) : Subtype p → X) x :=
  continuous_subtype_val.continuousAt

/-- The induced homeomorphism between two equal subtypes of a given topological space:
the underlying equivalence is `Equiv.subtypeEquivProp`. -/
/-
**Homeomorph.ofEqSubtypes** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Homeomorph.ofEqSubtypes {p q : X -> Prop} (hpq : p = q) : Subtype p ≃ₜ Sub
type q where toEquiv
参数：hpq : p = q。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The induced homeomorphism between two equal subtypes of a given topological spac
e:
the underlying equivalence is `Equiv.subtypeEquivProp`.
-/
def Homeomorph.ofEqSubtypes {p q : X → Prop} (hpq : p = q) : Subtype p ≃ₜ Subtype q where
  toEquiv := Equiv.subtypeEquivProp hpq
  continuous_toFun := continuous_id.subtype_map (fun x ↦ by simp [hpq])
  continuous_invFun := continuous_id.subtype_map (fun x ↦ by simp [hpq])

@[simp]
/-
**Homeomorph.ofEqSubtypes_toEquiv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Homeomorph.ofEqSubtypes_toEquiv {p q : X -> Prop} (hpq : p = q) : (Homeomo
rph.ofEqSubtypes hpq).toEquiv = Equiv.subtypeEquivProp hpq
参数：hpq : p = q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Homeomorph.ofEqSubtypes_toEquiv {p q : X → Prop} (hpq : p = q) :
    (Homeomorph.ofEqSubtypes hpq).toEquiv = Equiv.subtypeEquivProp hpq := rfl
/-
**Subtype.dense_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subtype.dense_iff {s : Set X} {t : Set s} : Dense t ↔ s subseteq closure (
(↑) '' t)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.IsInducing.dense_iff`：dense_iff (hf : IsInducing f) {s : Set X}
 : Dense s ↔ forall x, f x in closure (f '' s)
· 使用引理 `Topology.IsInducing.subtypeVal`：Topology.IsInducing.subtypeVal {t : Set 
Y} : IsInducing ((↑) : t -> Y)
· 使用定理 `SetCoe.forall`：SetCoe.forall {s : Set α} {p : s -> Prop} : (forall x : s
, p x) ↔ forall (x) (h : x in s), p ⟨x, h⟩
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Subtype.dense_iff {s : Set X} {t : Set s} : Dense t ↔ s ⊆ closure ((↑) '' t) := by
  rw [IsInducing.subtypeVal.dense_iff, SetCoe.forall]
  rfl

@[simp]
/-
**denseRange_inclusion_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：denseRange_inclusion_iff {s t : Set X} (hst : s subseteq t) : DenseRange (
inclusion hst) ↔ t subseteq closure s
参数：hst : s subseteq t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DenseRange.eq_1`：∀ {X : Type u} [inst : TopologicalSpace X] {α : Type u_
1} (f : α → X), DenseRange f = Dense (Set.range f)
· 使用定理 `Subtype.dense_iff`：Subtype.dense_iff {s : Set X} {t : Set s} : Dense t ↔
 s subseteq closure ((↑) '' t)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Set.val_comp_inclusion`：val_comp_inclusion (h : s subseteq t) : Subtype.
val ∘ inclusion h = Subtype.val
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem denseRange_inclusion_iff {s t : Set X} (hst : s ⊆ t) :
    DenseRange (inclusion hst) ↔ t ⊆ closure s := by
  rw [DenseRange, Subtype.dense_iff, ← range_comp, val_comp_inclusion, Subtype.range_coe]
/-
**map_nhds_subtype_val** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_nhds_subtype_val {s : Set X} (x : s) : map ((↑) : s -> X) (𝓝 x) = 𝓝[s]
 ↑x
参数：x : s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Topology.IsInducing.map_nhds_eq`：map_nhds_eq (hf : IsInducing f) (x : X)
 : (𝓝 x).map f = 𝓝[range f] f x
· 使用引理 `Topology.IsInducing.subtypeVal`：Topology.IsInducing.subtypeVal {t : Set 
Y} : IsInducing ((↑) : t -> Y)
· 使用定理 `Subtype.range_val`：range_val {s : Set α} : range (Subtype.val : s -> α) 
= s
-/
theorem map_nhds_subtype_val {s : Set X} (x : s) : map ((↑) : s → X) (𝓝 x) = 𝓝[s] ↑x := by
  rw [IsInducing.subtypeVal.map_nhds_eq, Subtype.range_val]

set_option backward.isDefEq.respectTransparency false in
/-
**map_nhds_subtype_coe_eq_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_nhds_subtype_coe_eq_nhds {x : X} (hx : p x) (h : forallᶠ x in 𝓝 x, p x
) : map ((↑) : Subtype p -> X) (𝓝 ⟨x, hx⟩) = 𝓝 x
参数：hx : p x；h : forallᶠ x in 𝓝 x, p x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_nhds_induced_of_mem`：map_nhds_induced_of_mem {a : α} (h : range f in
 𝓝 (f a)) : map f (@nhds α (induced f t) a) = 𝓝 (f a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.range_val`：range_val {s : Set α} : range (Subtype.val : s -> α) 
= s
-/
theorem map_nhds_subtype_coe_eq_nhds {x : X} (hx : p x) (h : ∀ᶠ x in 𝓝 x, p x) :
    map ((↑) : Subtype p → X) (𝓝 ⟨x, hx⟩) = 𝓝 x :=
  map_nhds_induced_of_mem <| by rw [Subtype.range_val]; exact h
/-
**nhds_subtype_eq_comap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_subtype_eq_comap {x : X} {h : p x} : 𝓝 (⟨x, h⟩ : Subtype p) = comap (
↑) (𝓝 x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhds_induced`：nhds_induced [T : TopologicalSpace α] (f : β -> α) (a : β)
 : @nhds β (TopologicalSpace.induced f T) a = comap f (𝓝 (f a))
-/
theorem nhds_subtype_eq_comap {x : X} {h : p x} : 𝓝 (⟨x, h⟩ : Subtype p) = comap (↑) (𝓝 x) :=
  nhds_induced _ _
/-
**tendsto_subtype_rng** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {X : Type u} [inst : TopologicalSpace X] {Y : Type u_5} {p : X → Prop} {
l : Filter Y} {f : Y → Subtype p}   {x : Subtype p}, Filter.Tendsto f l (nhds x)
 ↔ Filter.Tendsto (fun x => ↑(f x)) l (nhds ↑x)
参数：nhds x；fun x => ↑(f x)；nhds ↑x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_subtype_eq_comap`：nhds_subtype_eq_comap {x : X} {h : p x} : 𝓝 (⟨x, 
h⟩ : Subtype p) = comap (↑) (𝓝 x)
· 使用定理 `Filter.tendsto_comap_iff`：tendsto_comap_iff {f : α -> β} {g : β -> γ} {a
 : Filter α} {c : Filter γ} : Tendsto f a (c.comap g) ↔ Tendsto (g ∘ f) a c
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem tendsto_subtype_rng {Y : Type*} {p : X → Prop} {l : Filter Y} {f : Y → Subtype p} :
    ∀ {x : Subtype p}, Tendsto f l (𝓝 x) ↔ Tendsto (fun x => (f x : X)) l (𝓝 (x : X))
  | ⟨a, ha⟩ => by rw [nhds_subtype_eq_comap, tendsto_comap_iff]; rfl
/-
**closure_subtype** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_subtype {x : { a // p a }} {s : Set { a // p a }} : x in closure s
 ↔ (x : X) in closure (((↑) : _ -> X) '' s)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `closure_induced`：closure_induced {f : α -> β} {a : α} {s : Set α} : a in
 @closure α (t.induced f) s ↔ f a in closure (f '' s)
-/
theorem closure_subtype {x : { a // p a }} {s : Set { a // p a }} :
    x ∈ closure s ↔ (x : X) ∈ closure (((↑) : _ → X) '' s) :=
  closure_induced

@[simp]
/-
**continuousAt_codRestrict_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousAt_codRestrict_iff {f : X -> Y} {t : Set Y} (h1 : forall x, f x 
in t) {x : X} : ContinuousAt (codRestrict f t h1) x ↔ ContinuousAt f x
参数：h1 : forall x, f x in t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsInducing.continuousAt_iff`：continuousAt_iff (hg : IsInducing 
g) {x : X} : ContinuousAt f x ↔ ContinuousAt (g ∘ f) x
· 使用引理 `Topology.IsInducing.subtypeVal`：Topology.IsInducing.subtypeVal {t : Set 
Y} : IsInducing ((↑) : t -> Y)
-/
theorem continuousAt_codRestrict_iff {f : X → Y} {t : Set Y} (h1 : ∀ x, f x ∈ t) {x : X} :
    ContinuousAt (codRestrict f t h1) x ↔ ContinuousAt f x :=
  IsInducing.subtypeVal.continuousAt_iff

alias ⟨_, ContinuousAt.codRestrict⟩ := continuousAt_codRestrict_iff
/-
**ContinuousAt.restrict** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAt.restrict {f : X -> Y} {s : Set X} {t : Set Y} (h1 : MapsTo f 
s t) {x : s} (h2 : ContinuousAt f x) : ContinuousAt (h1.restrict f s t) x
参数：h1 : MapsTo f s t；h2 : ContinuousAt f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.codRestrict`：∀ {X : Type u} {Y : Type v} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y} {t : Set Y}   (h1 : ∀ (x : X
), f x ∈ t) {x…
· 使用定理 `ContinuousAt.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace
 Z] {f …
· 使用定理 `continuousAt_subtype_val`：continuousAt_subtype_val {p : X -> Prop} {x : 
Subtype p} : ContinuousAt ((↑) : Subtype p -> X) x
-/
theorem ContinuousAt.restrict {f : X → Y} {s : Set X} {t : Set Y} (h1 : MapsTo f s t) {x : s}
    (h2 : ContinuousAt f x) : ContinuousAt (h1.restrict f s t) x :=
  (h2.comp continuousAt_subtype_val).codRestrict _
/-
**ContinuousAt.restrictPreimage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAt.restrictPreimage {f : X -> Y} {s : Set Y} {x : f ⁻¹' s} (h : 
ContinuousAt f x) : ContinuousAt (s.restrictPreimage f) x
参数：h : ContinuousAt f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.restrict`：ContinuousAt.restrict {f : X -> Y} {s : Set X} {t
 : Set Y} (h1 : MapsTo f s t) {x : s} (h2 : ContinuousAt f x) : ContinuousAt (h1
.restrict f…
· 使用定理 `Set.mapsTo_preimage`：mapsTo_preimage (f : α -> β) (t : Set β) : MapsTo f
 (f ⁻¹' t) t
-/
theorem ContinuousAt.restrictPreimage {f : X → Y} {s : Set Y} {x : f ⁻¹' s} (h : ContinuousAt f x) :
    ContinuousAt (s.restrictPreimage f) x :=
  h.restrict _

@[continuity, fun_prop]
/-
**Continuous.codRestrict** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.codRestrict {f : X -> Y} {s : Set Y} (hf : Continuous f) (hs : 
forall a, f a in s) : Continuous (s.codRestrict f hs)
参数：hf : Continuous f；hs : forall a, f a in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.subtype_mk`：Continuous.subtype_mk {f : Y -> X} (h : Continuou
s f) (hp : forall x, p (f x)) : Continuous fun x => (⟨f x, hp x⟩ : Subtype p)
-/
theorem Continuous.codRestrict {f : X → Y} {s : Set Y} (hf : Continuous f) (hs : ∀ a, f a ∈ s) :
    Continuous (s.codRestrict f hs) :=
  hf.subtype_mk hs
/-
**continuous_codRestrict_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_codRestrict_iff {f : X -> Y} {s : Set Y} (hs : forall a, f a in
 s) : Continuous (codRestrict f s hs) ↔ Continuous f
参数：hs : forall a, f a in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `isOpen_induced`：isOpen_induced {s : Set β} (h : IsOpen s) : IsOpen[induc
ed f t] (f ⁻¹' s)
· 使用定理 `Continuous.codRestrict`：Continuous.codRestrict {f : X -> Y} {s : Set Y} 
(hf : Continuous f) (hs : forall a, f a in s) : Continuous (s.codRestrict f hs)
-/
theorem continuous_codRestrict_iff {f : X → Y} {s : Set Y} (hs : ∀ a, f a ∈ s) :
    Continuous (codRestrict f s hs) ↔ Continuous f := by
  refine ⟨?_, fun hf ↦ hf.codRestrict hs⟩
  simp_rw [continuous_def]
  intro hf t ht
  exact hf (Subtype.val ⁻¹' t) (isOpen_induced ht)
/-
**IsOpenMap.codRestrict** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpenMap.codRestrict {f : X -> Y} (hf : IsOpenMap f) {s : Set Y} (hs : fo
rall a, f a in s) : IsOpenMap (s.codRestrict f hs)
参数：hf : IsOpenMap f；hs : forall a, f a in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenMap.subtype_mk`：IsOpenMap.subtype_mk {f : Y -> X} (hf : IsOpenMap 
f) (hp : forall x, p (f x)) : IsOpenMap fun x => (⟨f x, hp x⟩ : Subtype p)
-/
theorem IsOpenMap.codRestrict {f : X → Y} (hf : IsOpenMap f) {s : Set Y} (hs : ∀ a, f a ∈ s) :
    IsOpenMap (s.codRestrict f hs) :=
  hf.subtype_mk hs
/-
**IsClosedMap.codRestrict** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosedMap.codRestrict {f : X -> Y} (hf : IsClosedMap f) {s : Set Y} (hs 
: forall a, f a in s) : IsClosedMap (s.codRestrict f hs)
参数：hf : IsClosedMap f；hs : forall a, f a in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosedMap.subtype_mk`：IsClosedMap.subtype_mk {f : Y -> X} (hf : IsClos
edMap f) (hp : forall x, p (f x)) : IsClosedMap fun x => (⟨f x, hp x⟩ : Subtype 
p)
-/
theorem IsClosedMap.codRestrict {f : X → Y} (hf : IsClosedMap f) {s : Set Y} (hs : ∀ a, f a ∈ s) :
    IsClosedMap (s.codRestrict f hs) :=
  hf.subtype_mk hs

@[continuity, fun_prop]
/-
**Continuous.restrict** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.restrict {f : X -> Y} {s : Set X} {t : Set Y} (h1 : MapsTo f s 
t) (h2 : Continuous f) : Continuous (h1.restrict f s t)
参数：h1 : MapsTo f s t；h2 : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.codRestrict`：Continuous.codRestrict {f : X -> Y} {s : Set Y} 
(hf : Continuous f) (hs : forall a, f a in s) : Continuous (s.codRestrict f hs)
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
-/
theorem Continuous.restrict {f : X → Y} {s : Set X} {t : Set Y} (h1 : MapsTo f s t)
    (h2 : Continuous f) : Continuous (h1.restrict f s t) :=
  (h2.comp continuous_subtype_val).codRestrict _
/-
**IsOpenMap.mapsToRestrict** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsOpenMap.mapsToRestrict {f : X -> Y} (hf : IsOpenMap f) {s : Set X} {t : 
Set Y} (hs : IsOpen s) (ht : MapsTo f s t) : IsOpenMap ht.restrict
参数：hf : IsOpenMap f；hs : IsOpen s；ht : MapsTo f s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenMap.codRestrict`：IsOpenMap.codRestrict {f : X -> Y} (hf : IsOpenMa
p f) {s : Set Y} (hs : forall a, f a in s) : IsOpenMap (s.codRestrict f hs)
· 使用定理 `IsOpenMap.domRestrict`：IsOpenMap.domRestrict {f : X -> Y} (hf : IsOpenMa
p f) {s : Set X} (hs : IsOpen s) : IsOpenMap (s.domRestrict f)
-/
lemma IsOpenMap.mapsToRestrict {f : X → Y} (hf : IsOpenMap f) {s : Set X} {t : Set Y}
    (hs : IsOpen s) (ht : MapsTo f s t) : IsOpenMap ht.restrict :=
  (hf.domRestrict hs).codRestrict _
/-
**IsClosedMap.mapsToRestrict** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsClosedMap.mapsToRestrict {f : X -> Y} (hf : IsClosedMap f) {s : Set X} {
t : Set Y} (hs : IsClosed s) (ht : MapsTo f s t) : IsClosedMap ht.restrict
参数：hf : IsClosedMap f；hs : IsClosed s；ht : MapsTo f s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosedMap.codRestrict`：IsClosedMap.codRestrict {f : X -> Y} (hf : IsCl
osedMap f) {s : Set Y} (hs : forall a, f a in s) : IsClosedMap (s.codRestrict f 
hs)
· 使用定理 `IsClosedMap.domRestrict`：IsClosedMap.domRestrict {f : X -> Y} (hf : IsCl
osedMap f) {s : Set X} (hs : IsClosed s) : IsClosedMap (s.domRestrict f)
-/
lemma IsClosedMap.mapsToRestrict {f : X → Y} (hf : IsClosedMap f) {s : Set X} {t : Set Y}
    (hs : IsClosed s) (ht : MapsTo f s t) : IsClosedMap ht.restrict :=
  (hf.domRestrict hs).codRestrict _

@[continuity, fun_prop]
/-
**Continuous.restrictPreimage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.restrictPreimage {f : X -> Y} {s : Set Y} (h : Continuous f) : 
Continuous (s.restrictPreimage f)
参数：h : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.restrict`：Continuous.restrict {f : X -> Y} {s : Set X} {t : S
et Y} (h1 : MapsTo f s t) (h2 : Continuous f) : Continuous (h1.restrict f s t)
· 使用定理 `Set.mapsTo_preimage`：mapsTo_preimage (f : α -> β) (t : Set β) : MapsTo f
 (f ⁻¹' t) t
-/
theorem Continuous.restrictPreimage {f : X → Y} {s : Set Y} (h : Continuous f) :
    Continuous (s.restrictPreimage f) :=
  h.restrict _

@[fun_prop]
/-
**Topology.IsEmbedding.restrict** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsEmbedding.restrict {f : X -> Y} (hf : IsEmbedding f) {s : Set X
} {t : Set Y} (H : s.MapsTo f t) : IsEmbedding H.restrict
参数：hf : IsEmbedding f；H : s.MapsTo f t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.of_comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type 
u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : Topological
Space Y] [inst_2 :…
· 使用定理 `Continuous.restrict`：Continuous.restrict {f : X -> Y} {s : Set X} {t : S
et Y} (h1 : MapsTo f s t) (h2 : Continuous f) : Continuous (h1.restrict f s t)
· 使用定理 `Topology.IsEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Continuous…
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `Topology.IsEmbedding.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3
} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : TopologicalSpa
ce Y] [inst_2 :…
· 使用引理 `Topology.IsEmbedding.subtypeVal`：Topology.IsEmbedding.subtypeVal : IsEmb
edding ((↑) : Subtype p -> X)
-/
lemma Topology.IsEmbedding.restrict {f : X → Y}
    (hf : IsEmbedding f) {s : Set X} {t : Set Y} (H : s.MapsTo f t) :
    IsEmbedding H.restrict :=
  .of_comp (hf.continuous.restrict H) continuous_subtype_val (hf.comp .subtypeVal)

@[fun_prop]
/-
**Topology.IsOpenEmbedding.restrict** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsOpenEmbedding.restrict {f : X -> Y} (hf : IsOpenEmbedding f) {s
 : Set X} {t : Set Y} (H : s.MapsTo f t) (hs : IsOpen s) : IsOpenEmbedding H.res
trict
参数：hf : IsOpenEmbedding f；H : s.MapsTo f t；hs : IsOpen s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsEmbedding.restrict`：Topology.IsEmbedding.restrict {f : X -> Y
} (hf : IsEmbedding f) {s : Set X} {t : Set Y} (H : s.MapsTo f t) : IsEmbedding 
H.restrict
· 使用定理 `Topology.IsOpenEmbedding.isEmbedding`：∀ {X : Type u_1} {Y : Type u_2} {f
 : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.
IsOpenEmbedding f → Topolo…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.MapsTo.range_restrict`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (
s : Set α) (t : Set β) (h : Set.MapsTo f s t),   Set.range (Set.MapsTo.restrict 
f s t h) = Subt…
· 使用定理 `Continuous.isOpen_preimage`：∀ {X : Type u} {Y : Type v} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Continuous f → ∀ (s : S
et Y), IsOpen s …
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `Topology.IsOpenEmbedding.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} {f :
 X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.Is
OpenEmbedding f → IsOpen…
-/
lemma Topology.IsOpenEmbedding.restrict {f : X → Y}
    (hf : IsOpenEmbedding f) {s : Set X} {t : Set Y} (H : s.MapsTo f t) (hs : IsOpen s) :
    IsOpenEmbedding H.restrict :=
  ⟨hf.isEmbedding.restrict H, (by
    rw [MapsTo.range_restrict]
    exact continuous_subtype_val.1 _ (hf.isOpenMap _ hs))⟩
/-
**Topology.IsInducing.codRestrict** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Topology.IsInducing.codRestrict {e : X -> Y} (he : IsInducing e) {s : Set 
Y} (hs : forall x, e x in s) : IsInducing (codRestrict e s hs)
参数：he : IsInducing e；hs : forall x, e x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.of_comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u
_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace Y]   [inst_1 : TopologicalS
pace X] [inst_2 :…
· 使用定理 `Continuous.codRestrict`：Continuous.codRestrict {f : X -> Y} {s : Set Y} 
(hf : Continuous f) (hs : forall a, f a in s) : Continuous (s.codRestrict f hs)
· 使用定理 `Topology.IsInducing.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X →
 Y} [inst : TopologicalSpace Y] [inst_1 : TopologicalSpace X],   Topology.IsIndu
cing f → Continuous …
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
-/
theorem Topology.IsInducing.codRestrict {e : X → Y} (he : IsInducing e) {s : Set Y}
    (hs : ∀ x, e x ∈ s) : IsInducing (codRestrict e s hs) :=
  he.of_comp (he.continuous.codRestrict hs) continuous_subtype_val
/-
**Topology.IsEmbedding.codRestrict** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsEmbeddi
ng`。
形式化陈述：∀ {X : Type u} {Y : Type v} [inst : TopologicalSpace X] [inst_1 : Topologi
calSpace Y] {e : X → Y},   Topology.IsEmbedding e → ∀ (s : Set Y) (hs : ∀ (x : X
), e x ∈ s), Topology.IsEmbedding (Set.codRestrict e s hs)
参数：s : Set Y；hs : ∀ (x : X), e x ∈ s；Set.codRestrict e s hs。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.of_comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type 
u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : Topological
Space Y] [inst_2 :…
· 使用定理 `Continuous.codRestrict`：Continuous.codRestrict {f : X -> Y} {s : Set Y} 
(hf : Continuous f) (hs : forall a, f a in s) : Continuous (s.codRestrict f hs)
· 使用定理 `Topology.IsEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Continuous…
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
-/
protected lemma Topology.IsEmbedding.codRestrict {e : X → Y} (he : IsEmbedding e) (s : Set Y)
    (hs : ∀ x, e x ∈ s) : IsEmbedding (codRestrict e s hs) :=
  he.of_comp (he.continuous.codRestrict hs) continuous_subtype_val

variable {s t : Set X}

@[fun_prop]
/-
**Topology.IsEmbedding.inclusion** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsEmbedding
`。
形式化陈述：∀ {X : Type u} [inst : TopologicalSpace X] {s t : Set X} (h : s ⊆ t), Topo
logy.IsEmbedding (Set.inclusion h)
参数：h : s ⊆ t；Set.inclusion h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.codRestrict`：∀ {X : Type u} {Y : Type v} [inst : To
pologicalSpace X] [inst_1 : TopologicalSpace Y] {e : X → Y},   Topology.IsEmbedd
ing e → ∀ (s : Set Y) …
· 使用引理 `Topology.IsEmbedding.subtypeVal`：Topology.IsEmbedding.subtypeVal : IsEmb
edding ((↑) : Subtype p -> X)
-/
protected lemma Topology.IsEmbedding.inclusion (h : s ⊆ t) :
    IsEmbedding (inclusion h) := IsEmbedding.subtypeVal.codRestrict _ _

@[fun_prop]
/-
**Topology.IsOpenEmbedding.inclusion** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsOpenE
mbedding`。
形式化陈述：∀ {X : Type u} [inst : TopologicalSpace X] {s t : Set X} (hst : s ⊆ t),   
IsOpen (Subtype.val ⁻¹' s) → Topology.IsOpenEmbedding (Set.inclusion hst)
参数：hst : s ⊆ t；Subtype.val ⁻¹' s；Set.inclusion hst。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.inclusion`：∀ {X : Type u} [inst : TopologicalSpace 
X] {s t : Set X} (h : s ⊆ t), Topology.IsEmbedding (Set.inclusion h)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_inclusion`：range_inclusion (h : s subseteq t) : range (inclusi
on h) = { x : t | (x : α) in s }
-/
protected lemma Topology.IsOpenEmbedding.inclusion (hst : s ⊆ t) (hs : IsOpen (t ↓∩ s)) :
    IsOpenEmbedding (inclusion hst) where
  toIsEmbedding := .inclusion _
  isOpen_range := by rwa [range_inclusion]

@[fun_prop]
/-
**Topology.IsClosedEmbedding.inclusion** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsClo
sedEmbedding`。
形式化陈述：∀ {X : Type u} [inst : TopologicalSpace X] {s t : Set X} (hst : s ⊆ t),   
IsClosed (Subtype.val ⁻¹' s) → Topology.IsClosedEmbedding (Set.inclusion hst)
参数：hst : s ⊆ t；Subtype.val ⁻¹' s；Set.inclusion hst。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.inclusion`：∀ {X : Type u} [inst : TopologicalSpace 
X] {s t : Set X} (h : s ⊆ t), Topology.IsEmbedding (Set.inclusion h)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_inclusion`：range_inclusion (h : s subseteq t) : range (inclusi
on h) = { x : t | (x : α) in s }
-/
protected lemma Topology.IsClosedEmbedding.inclusion (hst : s ⊆ t) (hs : IsClosed (t ↓∩ s)) :
    IsClosedEmbedding (inclusion hst) where
  toIsEmbedding := .inclusion _
  isClosed_range := by rwa [range_inclusion]

/-- Let `s, t ⊆ X` be two subsets of a topological space `X`.  If `t ⊆ s` and the topology induced
by `X` on `s` is discrete, then also the topology induces on `t` is discrete.

(Compare `IsDiscrete.mono` which is the same thing stated without using subtypes.) -/
/-
**DiscreteTopology.of_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DiscreteTopology.of_subset {X : Type*} [TopologicalSpace X] {s t : Set X} 
(_ : DiscreteTopology s) (ts : t subseteq s) : DiscreteTopology t
参数：_ : DiscreteTopology s；ts : t subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.discreteTopology`：∀ {X : Type u_1} {Y : Type u_2} {
f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [Discrete
Topology Y], Topology.IsEmb…
· 使用定理 `Topology.IsEmbedding.inclusion`：∀ {X : Type u} [inst : TopologicalSpace 
X] {s t : Set X} (h : s ⊆ t), Topology.IsEmbedding (Set.inclusion h)

--- 原说明 ---
Let `s, t ⊆ X` be two subsets of a topological space `X`.  If `t ⊆ s` and the to
pology induced
by `X` on `s` is discrete, then also the topology induces on `t` is discrete.

(Compare `IsDiscrete.mono` which is the same thing stated without using subtypes
.)
-/
theorem DiscreteTopology.of_subset {X : Type*} [TopologicalSpace X] {s t : Set X}
    (_ : DiscreteTopology s) (ts : t ⊆ s) : DiscreteTopology t :=
  (IsEmbedding.inclusion ts).discreteTopology

/-- Let `s, t ⊆ X` be two subsets of a topological space `X`.  If `t ⊆ s` and `s` is discrete,
then `t` is discrete.

(Compare `DiscreteTopology.of_subset` which is the same thing stated in terms of subtypes.) -/
/-
**IsDiscrete.mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsDiscrete.mono {t : Set X} (hs : IsDiscrete s) (hst : t subseteq s) : IsD
iscrete t
参数：hs : IsDiscrete s；hst : t subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DiscreteTopology.of_subset`：DiscreteTopology.of_subset {X : Type*} [Topo
logicalSpace X] {s t : Set X} (_ : DiscreteTopology s) (ts : t subseteq s) : Dis
creteTopology t
· 使用定理 `IsDiscrete.to_subtype`：∀ {X : Type u_5} [inst : TopologicalSpace X] {s :
 Set X}, IsDiscrete s → DiscreteTopology ↑s

--- 原说明 ---
Let `s, t ⊆ X` be two subsets of a topological space `X`.  If `t ⊆ s` and `s` is
 discrete,
then `t` is discrete.

(Compare `DiscreteTopology.of_subset` which is the same thing stated in terms of
 subtypes.)
-/
lemma IsDiscrete.mono {t : Set X} (hs : IsDiscrete s) (hst : t ⊆ s) : IsDiscrete t :=
  ⟨.of_subset hs.to_subtype hst⟩

/-- Let `s` be a discrete subset of a topological space. Then the preimage of `s` by
a continuous injective map is also discrete. -/
/-
**DiscreteTopology.preimage_of_continuous_injective** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：DiscreteTopology.preimage_of_continuous_injective {X Y : Type*} [Topologic
alSpace X] [TopologicalSpace Y] (s : Set Y) [DiscreteTopology s] {f : X -> Y} (h
c : Continuous f) (hinj : Function.Injective f) : DiscreteTopology (f ⁻¹' s)
参数：s : Set Y；hc : Continuous f；hinj : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DiscreteTopology.of_continuous_injective`：DiscreteTopology.of_continuous
_injective {β : Type*} [TopologicalSpace α] [TopologicalSpace β] [DiscreteTopolo
gy β] {f : α -> β} (hc : Conti…
· 使用定理 `Continuous.restrict`：Continuous.restrict {f : X -> Y} {s : Set X} {t : S
et Y} (h1 : MapsTo f s t) (h2 : Continuous f) : Continuous (h1.restrict f s t)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.MapsTo.restrict_inj`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t 
: Set β} {f : α → β} (h : Set.MapsTo f s t),   Function.Injective (Set.MapsTo.re
strict f s t …
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s

--- 原说明 ---
Let `s` be a discrete subset of a topological space. Then the preimage of `s` by
a continuous injective map is also discrete.
-/
theorem DiscreteTopology.preimage_of_continuous_injective {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (s : Set Y) [DiscreteTopology s] {f : X → Y} (hc : Continuous f)
    (hinj : Function.Injective f) : DiscreteTopology (f ⁻¹' s) :=
  DiscreteTopology.of_continuous_injective (β := s) (Continuous.restrict
    (by exact fun _ x ↦ x) hc) ((MapsTo.restrict_inj _).mpr hinj.injOn)
/-
**Topology.IsCoinducing.restrictPreimage_of_isOpen** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsCoinducing.restrictPreimage_of_isOpen {f : X -> Y} (hf : IsCoin
ducing f) {s : Set Y} (hs : IsOpen s) : IsCoinducing (s.restrictPreimage f)
参数：hf : IsCoinducing f；hs : IsOpen s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsCoinducing.of_isOpen_preimage_iff_isOpen`：∀ {X : Type u_1} {Y
 : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace 
Y],   (∀ (s : Set Y), IsOpen (f ⁻¹' s) ↔ …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.IsOpenEmbedding.isOpen_iff_image_isOpen`：∀ {X : Type u_1} {Y : 
Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],
   Topology.IsOpenEmbedding f → ∀ {s :…
· 使用定理 `IsOpen.isOpenEmbedding_subtypeVal`：IsOpen.isOpenEmbedding_subtypeVal {s 
: Set X} (hs : IsOpen s) : IsOpenEmbedding ((↑) : s -> X)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsCoinducing.isOpen_preimage`：∀ {X : Type u_1} {Y : Type u_2} {
f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology
.IsCoinducing f → ∀ {s : Se…
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `Topology.IsCoinducing.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X
 → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsCo
inducing f → Continuou…
· 使用定理 `Set.image_val_preimage_restrictPreimage`：image_val_preimage_restrictPrei
mage {u : Set t} : Subtype.val '' t.restrictPreimage f ⁻¹' u = f ⁻¹' Subtype.val
 '' u
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma Topology.IsCoinducing.restrictPreimage_of_isOpen {f : X → Y} (hf : IsCoinducing f)
    {s : Set Y} (hs : IsOpen s) :
    IsCoinducing (s.restrictPreimage f) := by
  refine .of_isOpen_preimage_iff_isOpen fun _ ↦ ?_
  rw [hs.isOpenEmbedding_subtypeVal.isOpen_iff_image_isOpen, ← hf.isOpen_preimage,
    (hs.preimage hf.continuous).isOpenEmbedding_subtypeVal.isOpen_iff_image_isOpen,
    image_val_preimage_restrictPreimage]

/-- If `f : X → Y` is a quotient map,
then its restriction to the preimage of an open set is a quotient map too. -/
/-
**Topology.IsQuotientMap.restrictPreimage_isOpen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Topology.IsQuotientMap.restrictPreimage_isOpen {f : X -> Y} (hf : IsQuotie
ntMap f) {s : Set Y} (hs : IsOpen s) : IsQuotientMap (s.restrictPreimage f)
参数：hf : IsQuotientMap f；hs : IsOpen s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Topology.isQuotientMap_iff`：∀ {X : Type u_3} {Y : Type u_4} [inst : Topo
logicalSpace X] [inst_1 : TopologicalSpace Y] (f : X → Y),   Topology.IsQuotient
Map f ↔ Topology…
· 使用引理 `Topology.IsCoinducing.restrictPreimage_of_isOpen`：Topology.IsCoinducing.
restrictPreimage_of_isOpen {f : X -> Y} (hf : IsCoinducing f) {s : Set Y} (hs : 
IsOpen s) : IsCoinducing (s.restrictPr…
· 使用定理 `Topology.IsQuotientMap.isCoinducing`：∀ {X : Type u_3} {Y : Type u_4} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Topology.I
sQuotientMap f → Topology…
· 使用定理 `Function.Surjective.restrictPreimage`：∀ {α : Type u_1} {β : Type u_2} (t
 : Set β) {f : α → β},   Function.Surjective f → Function.Surjective (t.restrict
Preimage f)
· 使用定理 `Topology.IsQuotientMap.surjective`：∀ {X : Type u_3} {Y : Type u_4} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Topology.IsQ
uotientMap f → Function…

--- 原说明 ---
If `f : X → Y` is a quotient map,
then its restriction to the preimage of an open set is a quotient map too.
-/
theorem Topology.IsQuotientMap.restrictPreimage_isOpen {f : X → Y} (hf : IsQuotientMap f)
    {s : Set Y} (hs : IsOpen s) : IsQuotientMap (s.restrictPreimage f) :=
  (isQuotientMap_iff _).2
    ⟨.restrictPreimage_of_isOpen hf.isCoinducing hs, hf.surjective.restrictPreimage _⟩

open scoped Set.Notation in
/-
**isClosed_preimage_val** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isClosed_preimage_val {s t : Set X} : IsClosed (s ↓inter t) ↔ s inter clos
ure (s inter t) subseteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `closure_eq_iff_isClosed`：closure_eq_iff_isClosed : closure s = s ↔ IsClo
sed s
· 使用定理 `Topology.IsEmbedding.closure_eq_preimage_closure_image`：∀ {X : Type u_1}
 {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpa
ce Y],   Topology.IsEmbedding f → ∀ (s : Set…
· 使用引理 `Topology.IsEmbedding.subtypeVal`：Topology.IsEmbedding.subtypeVal : IsEmb
edding ((↑) : Subtype p -> X)
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Function.Injective.image_injective`：∀ {α : Type u_1} {β : Type u_2} {f :
 α → β}, Function.Injective f → Function.Injective (Set.image f)
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `Subtype.image_preimage_coe`：image_preimage_coe (s t : Set α) : ((↑) : s 
-> α) '' ((↑) : s -> α) ⁻¹' t = s inter t
· 使用定理 `subset_antisymm_iff`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst 
: PartialOrder α] {a b : α}, a = b ↔ a ⊆ b ∧ b ⊆ a
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `Set.subset_inter`：subset_inter {s t r : Set α} (rs : r subseteq s) (rt :
 r subseteq t) : r subseteq s inter t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Set.subset_inter_iff`：subset_inter_iff {s t r : Set α} : r subseteq s in
ter t ↔ r subseteq s ∧ r subseteq t
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isClosed_preimage_val {s t : Set X} : IsClosed (s ↓∩ t) ↔ s ∩ closure (s ∩ t) ⊆ t := by
  rw [← closure_eq_iff_isClosed, IsEmbedding.subtypeVal.closure_eq_preimage_closure_image,
    ← Subtype.val_injective.image_injective.eq_iff, Subtype.image_preimage_coe,
    Subtype.image_preimage_coe, subset_antisymm_iff, and_iff_left, Set.subset_inter_iff,
    and_iff_right]
  exacts [Set.inter_subset_left, Set.subset_inter Set.inter_subset_left subset_closure]
/-
**frontier_inter_open_inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：frontier_inter_open_inter {s t : Set X} (ht : IsOpen t) : frontier (s inte
r t) inter t = frontier s inter t
参数：ht : IsOpen t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `IsOpenMap.preimage_frontier_eq_frontier_preimage`：∀ {X : Type u_1} {Y : 
Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],
   IsOpenMap f → Continuous f → ∀ (s :…
· 使用定理 `IsOpen.isOpenMap_subtype_val`：IsOpen.isOpenMap_subtype_val {s : Set X} (
hs : IsOpen s) : IsOpenMap ((↑) : s -> X)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `Subtype.preimage_coe_self_inter`：preimage_coe_self_inter (s t : Set α) :
 ((↑) : s -> α) ⁻¹' (s inter t) = ((↑) : s -> α) ⁻¹' t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem frontier_inter_open_inter {s t : Set X} (ht : IsOpen t) :
    frontier (s ∩ t) ∩ t = frontier s ∩ t := by
  simp only [Set.inter_comm _ t, ← Subtype.preimage_coe_eq_preimage_coe_iff,
    ht.isOpenMap_subtype_val.preimage_frontier_eq_frontier_preimage continuous_subtype_val,
    Subtype.preimage_coe_self_inter]

section SetNotation

open scoped Set.Notation

/-
**IsOpen.preimage_val** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsOpen.preimage_val {s t : Set X} (ht : IsOpen t) : IsOpen (s ↓inter t)
参数：ht : IsOpen t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
-/
lemma IsOpen.preimage_val {s t : Set X} (ht : IsOpen t) : IsOpen (s ↓∩ t) :=
  ht.preimage continuous_subtype_val
/-
**IsOpen.image_val** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsOpen.image_val {s : Set X} {t : Set s} (ht : IsOpen t) : exists c, IsOpe
n c ∧ Subtype.val '' t = c inter s
参数：ht : IsOpen t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `Topology.IsInducing.image_eq_isOpen_inter_range`：image_eq_isOpen_inter_r
ange (hf : IsInducing f) {s : Set X} (hs : IsOpen s) : exists c, IsOpen c ∧ f ''
 s = c inter range f
· 使用引理 `Topology.IsInducing.subtypeVal`：Topology.IsInducing.subtypeVal {t : Set 
Y} : IsInducing ((↑) : t -> Y)
-/
lemma IsOpen.image_val {s : Set X} {t : Set s} (ht : IsOpen t) :
    ∃ c, IsOpen c ∧ Subtype.val '' t = c ∩ s := by
  simpa using IsInducing.subtypeVal.image_eq_isOpen_inter_range ht

/-- If `s` is dense in `X` and `u` is open and dense in `s`, then `u = v ∩ s` for some `v` that is
open and dense in `X`. -/
/-
**exists_open_dense_of_open_dense_subtype** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_open_dense_of_open_dense_subtype (hs : Dense s) {u : Set s} (huo : 
IsOpen u) (hud : Dense u) : exists v : Set X, IsOpen v ∧ Dense v ∧ Subtype.val ⁻
¹' v = u
参数：hs : Dense s；huo : IsOpen u；hud : Dense u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dense_iff_inter_open`：dense_iff_inter_open : Dense s ↔ forall U, IsOpen 
U -> U.Nonempty -> (U inter s).Nonempty
· 使用定理 `Set.nonempty_of_nonempty_preimage`：nonempty_of_nonempty_preimage {s : Se
t β} {f : α -> β} (hf : (f ⁻¹' s).Nonempty) : s.Nonempty
· 使用引理 `IsOpen.preimage_val`：IsOpen.preimage_val {s t : Set X} (ht : IsOpen t) :
 IsOpen (s ↓inter t)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
If `s` is dense in `X` and `u` is open and dense in `s`, then `u = v ∩ s` for so
me `v` that is
open and dense in `X`.
-/
lemma exists_open_dense_of_open_dense_subtype (hs : Dense s) {u : Set s} (huo : IsOpen u)
    (hud : Dense u) :
    ∃ v : Set X, IsOpen v ∧ Dense v ∧ Subtype.val ⁻¹' v = u := by
  choose v hv1 hv2 using huo
  refine ⟨v, hv1, ?_, hv2⟩
  rw [dense_iff_inter_open] at *
  intro t ht ht'
  subst hv2
  refine nonempty_of_nonempty_preimage (f := (Subtype.val : s → X)) (hud (Subtype.val ⁻¹' t) ?_ ?_)
  · exact IsOpen.preimage_val ht
  · obtain ⟨x, hx⟩ := hs t ht ht'
    simpa using ⟨⟨x, hx.2⟩, hx.1⟩
/-
**IsClosed.preimage_val** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsClosed.preimage_val {s t : Set X} (ht : IsClosed t) : IsClosed (s ↓inter
 t)
参数：ht : IsClosed t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
-/
lemma IsClosed.preimage_val {s t : Set X} (ht : IsClosed t) : IsClosed (s ↓∩ t) :=
  ht.preimage continuous_subtype_val
/-
**IsClosed.image_val** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsClosed.image_val {s : Set X} {t : Set s} (ht : IsClosed t) : exists c, I
sClosed c ∧ Subtype.val '' t = c inter s
参数：ht : IsClosed t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `Topology.IsInducing.image_eq_isClosed_inter_range`：image_eq_isClosed_int
er_range (hf : IsInducing f) {s : Set X} (hs : IsClosed s) : exists c, IsClosed 
c ∧ f '' s = c inter range f
· 使用引理 `Topology.IsInducing.subtypeVal`：Topology.IsInducing.subtypeVal {t : Set 
Y} : IsInducing ((↑) : t -> Y)
-/
lemma IsClosed.image_val {s : Set X} {t : Set s} (ht : IsClosed t) :
    ∃ c, IsClosed c ∧ Subtype.val '' t = c ∩ s := by
  simpa using IsInducing.subtypeVal.image_eq_isClosed_inter_range ht
/-
**IsOpen.inter_preimage_val_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsOpen`。
形式化陈述：∀ {X : Type u} [inst : TopologicalSpace X] {s t : Set X}, IsOpen s → (IsOp
en (Subtype.val ⁻¹' t) ↔ IsOpen (s ∩ t))
参数：IsOpen (Subtype.val ⁻¹' t) ↔ IsOpen (s ∩ t)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.image_preimage_coe`：image_preimage_coe (s t : Set α) : ((↑) : s 
-> α) '' ((↑) : s -> α) ⁻¹' t = s inter t
· 使用定理 `IsOpen.isOpenMap_subtype_val`：IsOpen.isOpenMap_subtype_val {s : Set X} (
hs : IsOpen s) : IsOpenMap ((↑) : s -> X)
· 使用引理 `IsOpen.preimage_val`：IsOpen.preimage_val {s t : Set X} (ht : IsOpen t) :
 IsOpen (s ↓inter t)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.preimage_coe_self_inter`：preimage_coe_self_inter (s t : Set α) :
 ((↑) : s -> α) ⁻¹' (s inter t) = ((↑) : s -> α) ⁻¹' t
-/
@[simp] lemma IsOpen.inter_preimage_val_iff {s t : Set X} (hs : IsOpen s) :
    IsOpen (s ↓∩ t) ↔ IsOpen (s ∩ t) :=
  ⟨fun h ↦ by simpa using hs.isOpenMap_subtype_val _ h,
    fun h ↦ (Subtype.preimage_coe_self_inter _ _).symm ▸ h.preimage_val⟩
/-
**IsClosed.inter_preimage_val_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsClosed`。
形式化陈述：∀ {X : Type u} [inst : TopologicalSpace X] {s t : Set X}, IsClosed s → (Is
Closed (Subtype.val ⁻¹' t) ↔ IsClosed (s ∩ t))
参数：IsClosed (Subtype.val ⁻¹' t) ↔ IsClosed (s ∩ t)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.image_preimage_coe`：image_preimage_coe (s t : Set α) : ((↑) : s 
-> α) '' ((↑) : s -> α) ⁻¹' t = s inter t
· 使用定理 `IsClosed.isClosedMap_subtype_val`：IsClosed.isClosedMap_subtype_val {s : 
Set X} (hs : IsClosed s) : IsClosedMap ((↑) : s -> X)
· 使用引理 `IsClosed.preimage_val`：IsClosed.preimage_val {s t : Set X} (ht : IsClose
d t) : IsClosed (s ↓inter t)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.preimage_coe_self_inter`：preimage_coe_self_inter (s t : Set α) :
 ((↑) : s -> α) ⁻¹' (s inter t) = ((↑) : s -> α) ⁻¹' t
-/
@[simp] lemma IsClosed.inter_preimage_val_iff {s t : Set X} (hs : IsClosed s) :
    IsClosed (s ↓∩ t) ↔ IsClosed (s ∩ t) :=
  ⟨fun h ↦ by simpa using hs.isClosedMap_subtype_val _ h,
    fun h ↦ (Subtype.preimage_coe_self_inter _ _).symm ▸ h.preimage_val⟩

end SetNotation

end Subtype

section Quotient

variable [TopologicalSpace X] [TopologicalSpace Y]
variable {r : X → X → Prop} {s : Setoid X}

/-
**isQuotientMap_quot_mk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isQuotientMap_quot_mk : IsQuotientMap (@Quot.mk X r)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.exists_rep`：∀ {α : Sort u} {r : α → α → Prop} (q : Quot r), ∃ a, Qu
ot.mk r a = q
-/
theorem isQuotientMap_quot_mk : IsQuotientMap (@Quot.mk X r) :=
  ⟨⟨rfl⟩, Quot.exists_rep⟩

@[continuity, fun_prop]
/-
**continuous_quot_mk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_quot_mk : Continuous (@Quot.mk X r)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_coinduced_rng`：continuous_coinduced_rng {t : TopologicalSpace
 α} : Continuous[t, coinduced f t] f
-/
theorem continuous_quot_mk : Continuous (@Quot.mk X r) :=
  continuous_coinduced_rng

@[continuity, fun_prop]
/-
**continuous_quot_lift** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_quot_lift {f : X -> Y} (hr : forall a b, r a b -> f a = f b) (h
 : Continuous f) : Continuous (Quot.lift f hr : Quot r -> Y)
参数：hr : forall a b, r a b -> f a = f b；h : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_coinduced_dom`：continuous_coinduced_dom {g : β -> γ} {t₁ : To
pologicalSpace α} {t₂ : TopologicalSpace γ} : Continuous[coinduced f t₁, t₂] g ↔
 Continuous[t₁…
-/
theorem continuous_quot_lift {f : X → Y} (hr : ∀ a b, r a b → f a = f b) (h : Continuous f) :
    Continuous (Quot.lift f hr : Quot r → Y) :=
  continuous_coinduced_dom.2 h

@[continuity, fun_prop]
/-
**continuous_quot_map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_quot_map {r' : Y -> Y -> Prop} {f : X -> Y} (hr : forall a b, r
 a b -> r' (f a) (f b)) (h : Continuous f) : Continuous (Quot.map f hr : Quot r 
-> Quot r')
参数：hr : forall a b, r a b -> r' (f a) (f b)；h : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_quot_lift`：continuous_quot_lift {f : X -> Y} (hr : forall a b
, r a b -> f a = f b) (h : Continuous f) : Continuous (Quot.lift f hr : Quot r -
> Y)
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_quot_mk`：continuous_quot_mk : Continuous (@Quot.mk X r)
-/
theorem continuous_quot_map {r' : Y → Y → Prop} {f : X → Y} (hr : ∀ a b, r a b → r' (f a) (f b))
    (h : Continuous f) :
    Continuous (Quot.map f hr : Quot r → Quot r') :=
  continuous_quot_lift _ (continuous_quot_mk.comp h)
/-
**isQuotientMap_quotient_mk'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isQuotientMap_quotient_mk' : IsQuotientMap (@Quotient.mk' X s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isQuotientMap_quot_mk`：isQuotientMap_quot_mk : IsQuotientMap (@Quot.mk X
 r)
-/
theorem isQuotientMap_quotient_mk' : IsQuotientMap (@Quotient.mk' X s) :=
  isQuotientMap_quot_mk
/-
**continuous_quotient_mk'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_quotient_mk' : Continuous (@Quotient.mk' X s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_coinduced_rng`：continuous_coinduced_rng {t : TopologicalSpace
 α} : Continuous[t, coinduced f t] f
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)
-/
theorem continuous_quotient_mk' : Continuous (@Quotient.mk' X s) :=
  continuous_coinduced_rng
/-
**Continuous.quotient_lift** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.quotient_lift {f : X -> Y} (h : Continuous f) (hs : forall a b,
 a ≈ b -> f a = f b) : Continuous (Quotient.lift f hs : Quotient s -> Y)
参数：h : Continuous f；hs : forall a b, a ≈ b -> f a = f b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)
· 使用定理 `continuous_coinduced_dom`：continuous_coinduced_dom {g : β -> γ} {t₁ : To
pologicalSpace α} {t₂ : TopologicalSpace γ} : Continuous[coinduced f t₁, t₂] g ↔
 Continuous[t₁…
-/
theorem Continuous.quotient_lift {f : X → Y} (h : Continuous f) (hs : ∀ a b, a ≈ b → f a = f b) :
    Continuous (Quotient.lift f hs : Quotient s → Y) :=
  continuous_coinduced_dom.2 h
/-
**Continuous.quotient_liftOn'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.quotient_liftOn' {f : X -> Y} (h : Continuous f) (hs : forall a
 b, s a b -> f a = f b) : Continuous (fun x => Quotient.liftOn' x f hs : Quotien
t s -> Y)
参数：h : Continuous f；hs : forall a b, s a b -> f a = f b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.quotient_lift`：Continuous.quotient_lift {f : X -> Y} (h : Con
tinuous f) (hs : forall a b, a ≈ b -> f a = f b) : Continuous (Quotient.lift f h
s : Quotient s…
-/
theorem Continuous.quotient_liftOn' {f : X → Y} (h : Continuous f)
    (hs : ∀ a b, s a b → f a = f b) :
    Continuous (fun x => Quotient.liftOn' x f hs : Quotient s → Y) :=
  h.quotient_lift hs

open scoped Relator in
@[continuity, fun_prop]
/-
**Continuous.quotient_map'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.quotient_map' {t : Setoid Y} {f : X -> Y} (hf : Continuous f) (
H : (s.r ⇒ t.r) f f) : Continuous (Quotient.map' f H)
参数：hf : Continuous f；H : (s.r ⇒ t.r) f f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.quotient_lift`：Continuous.quotient_lift {f : X -> Y} (h : Con
tinuous f) (hs : forall a b, a ≈ b -> f a = f b) : Continuous (Quotient.lift f h
s : Quotient s…
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_quotient_mk'`：continuous_quotient_mk' : Continuous (@Quotient
.mk' X s)
-/
theorem Continuous.quotient_map' {t : Setoid Y} {f : X → Y} (hf : Continuous f)
    (H : (s.r ⇒ t.r) f f) : Continuous (Quotient.map' f H) :=
  (continuous_quotient_mk'.comp hf).quotient_lift _

end Quotient

section Pi

variable {ι : Type*} {A B : ι → Type*} {κ : Type*} [TopologicalSpace X]
  [T : ∀ i, TopologicalSpace (A i)] [∀ i, TopologicalSpace (B i)] {f : X → ∀ i : ι, A i}

/-
**continuous_pi_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_pi_iff : Continuous f ↔ forall i, Continuous fun a => f a i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem continuous_pi_iff : Continuous f ↔ ∀ i, Continuous fun a => f a i := by
  simp only [continuous_iInf_rng, continuous_induced_rng, comp_def]

@[continuity, fun_prop]
/-
**continuous_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_pi (f : X → α → Y) (hf : ∀ a, Continuous (f x a)) : Continuous 
(fun x a ↦ f x a)
参数：f : X → α → Y；hf : ∀ a, Continuous (f x a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_pi_iff`：continuous_pi_iff : Continuous f ↔ forall i, Continuo
us fun a => f a i
-/
theorem continuous_pi (h : ∀ i, Continuous fun a => f a i) : Continuous f :=
  continuous_pi_iff.2 h

@[continuity, fun_prop]
/-
**continuous_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_apply (a : α) : Continuous (fun f : (α → X) ↦ f a)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_iInf_dom`：continuous_iInf_dom {t₁ : ι -> TopologicalSpace α} 
{t₂ : TopologicalSpace β} {i : ι} : Continuous[t₁ i, t₂] f -> Continuous[iInf t₁
, t₂] f
· 使用定理 `continuous_induced_dom`：continuous_induced_dom {t : TopologicalSpace β} 
: Continuous[induced f t, t] f
-/
theorem continuous_apply (i : ι) : Continuous fun p : ∀ i, A i => p i :=
  continuous_iInf_dom continuous_induced_dom

@[continuity]
/-
**continuous_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_apply_apply {ρ : κ -> ι -> Type*} [forall j i, TopologicalSpace
 (ρ j i)] (j : κ) (i : ι) : Continuous fun p : forall j, forall i, ρ j i => p j 
i
参数：ρ j i；j : κ；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
-/
theorem continuous_apply_apply {ρ : κ → ι → Type*} [∀ j i, TopologicalSpace (ρ j i)] (j : κ)
    (i : ι) : Continuous fun p : ∀ j, ∀ i, ρ j i => p j i :=
  (continuous_apply i).comp (continuous_apply j)
/-
**continuousAt_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousAt_apply (i : ι) (x : forall i, A i) : ContinuousAt (fun p : for
all i, A i => p i) x
参数：i : ι；x : forall i, A i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
-/
theorem continuousAt_apply (i : ι) (x : ∀ i, A i) : ContinuousAt (fun p : ∀ i, A i => p i) x :=
  (continuous_apply i).continuousAt
/-
**Filter.Tendsto.apply_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.apply_nhds {l : Filter Y} {f : Y -> forall i, A i} {x : for
all i, A i} (h : Tendsto f l (𝓝 x)) (i : ι) : Tendsto (fun a => f a i) l (𝓝 <| x
 i)
参数：h : Tendsto f l (𝓝 x)；i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
· 使用定理 `continuousAt_apply`：continuousAt_apply (i : ι) (x : forall i, A i) : Con
tinuousAt (fun p : forall i, A i => p i) x
-/
theorem Filter.Tendsto.apply_nhds {l : Filter Y} {f : Y → ∀ i, A i} {x : ∀ i, A i}
    (h : Tendsto f l (𝓝 x)) (i : ι) : Tendsto (fun a => f a i) l (𝓝 <| x i) :=
  (continuousAt_apply i _).tendsto.comp h

@[fun_prop]
/-
**Continuous.piMap** 是 Mathlib 中的一个定理，位于命名空间 `Continuous`。
形式化陈述：∀ {ι : Type u_5} {A : ι → Type u_6} {B : ι → Type u_7} [T : (i : ι) → Topo
logicalSpace (A i)]   [inst : (i : ι) → TopologicalSpace (B i)] {f : (i : ι) → A
 i → B i},   (∀ (i : ι), Continuous (f i)) → Continuous (Pi.map f)
参数：i : ι；A i；i : ι；B i；i : ι；∀ (i : ι), Continuous (f i)；Pi.map f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_pi`：continuous_pi (f : X → α → Y) (hf : ∀ a, Continuous (f x 
a)) : Continuous (fun x a ↦ f x a)
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
-/
protected theorem Continuous.piMap
    {f : ∀ i, A i → B i} (hf : ∀ i, Continuous (f i)) : Continuous (Pi.map f) :=
  continuous_pi fun i ↦ (hf i).comp (continuous_apply i)
/-
**nhds_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_pi {a : forall i, A i} : 𝓝 a = pi fun i => 𝓝 (a i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_iInf`：nhds_iInf {ι : Sort*} {t : ι -> TopologicalSpace α} {a : α} :
 @nhds α (iInf t) a = ⨅ i, @nhds α (t i) a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `nhds_induced`：nhds_induced [T : TopologicalSpace α] (f : β -> α) (a : β)
 : @nhds β (TopologicalSpace.induced f T) a = comap f (𝓝 (f a))
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nhds_pi {a : ∀ i, A i} : 𝓝 a = pi fun i => 𝓝 (a i) := by
  simp only [nhds_iInf, nhds_induced, Filter.pi]
/-
**IsOpenMap.piMap** 是 Mathlib 中的一个定理，位于命名空间 `IsOpenMap`。
形式化陈述：∀ {ι : Type u_5} {A : ι → Type u_6} {B : ι → Type u_7} [T : (i : ι) → Topo
logicalSpace (A i)]   [inst : (i : ι) → TopologicalSpace (B i)] {f : (i : ι) → A
 i → B i},   (∀ (i : ι), IsOpenMap (f i)) → (∀ᶠ (i : ι) in Filter.cofinite, Func
tion.Surjective (f i)) → IsOpenMap (Pi.map f)
参数：i : ι；A i；i : ι；B i；i : ι；∀ (i : ι), IsOpenMap (f i)；∀ᶠ (i : ι) in Filter.cof
inite, Function.Surjective (f i)；Pi.map f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenMap.of_nhds_le`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y],   (∀ (x : X), nhds (f x) ≤ 
Filter.map…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_pi`：nhds_pi {a : forall i, A i} : 𝓝 a = pi fun i => 𝓝 (a i)
· 使用定理 `Filter.map_piMap_pi`：map_piMap_pi {α β : ι -> Type*} {f : forall i, α i 
-> β i} (hf : forallᶠ i in cofinite, Surjective (f i)) (l : forall i, Filter (α 
i)) : map…
· 使用定理 `Filter.pi_mono`：pi_mono (h : forall i, f₁ i <= f₂ i) : pi f₁ <= pi f₂
· 使用定理 `IsOpenMap.nhds_le`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : T
opologicalSpace X] [inst_1 : TopologicalSpace Y],   IsOpenMap f → ∀ (x : X), nhd
s (f x)…
-/
protected theorem IsOpenMap.piMap {f : ∀ i, A i → B i}
    (hfo : ∀ i, IsOpenMap (f i)) (hsurj : ∀ᶠ i in cofinite, Surjective (f i)) :
    IsOpenMap (Pi.map f) := by
  refine IsOpenMap.of_nhds_le fun x ↦ ?_
  rw [nhds_pi, nhds_pi, map_piMap_pi hsurj]
  exact Filter.pi_mono fun i ↦ (hfo i).nhds_le _
/-
**IsOpenQuotientMap.piMap** 是 Mathlib 中的一个定理，位于命名空间 `IsOpenQuotientMap`。
形式化陈述：∀ {ι : Type u_5} {A : ι → Type u_6} {B : ι → Type u_7} [T : (i : ι) → Topo
logicalSpace (A i)]   [inst : (i : ι) → TopologicalSpace (B i)] {f : (i : ι) → A
 i → B i},   (∀ (i : ι), IsOpenQuotientMap (f i)) → IsOpenQuotientMap (Pi.map f)
参数：i : ι；A i；i : ι；B i；i : ι；∀ (i : ι), IsOpenQuotientMap (f i)；Pi.map f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.piMap`：∀ {ι : Sort u_1} {α : ι → Sort u_2} {β : ι → 
Sort u_3} {f : (i : ι) → α i → β i},   (∀ (i : ι), Function.Surjective (f i)) → 
Function.Surjec…
· 使用定理 `IsOpenQuotientMap.surjective`：∀ {X : Type u} {Y : Type v} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsOpenQuotientMap f →
 Function.Surjecti…
· 使用定理 `Continuous.piMap`：∀ {ι : Type u_5} {A : ι → Type u_6} {B : ι → Type u_7}
 [T : (i : ι) → TopologicalSpace (A i)]   [inst : (i : ι) → TopologicalSpace (B 
i)] {f…
· 使用定理 `IsOpenQuotientMap.continuous`：∀ {X : Type u} {Y : Type v} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsOpenQuotientMap f →
 Continuous f
· 使用定理 `IsOpenMap.piMap`：∀ {ι : Type u_5} {A : ι → Type u_6} {B : ι → Type u_7} 
[T : (i : ι) → TopologicalSpace (A i)]   [inst : (i : ι) → TopologicalSpace (B i
)] {f…
· 使用定理 `IsOpenQuotientMap.isOpenMap`：∀ {X : Type u} {Y : Type v} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsOpenQuotientMap f → 
IsOpenMap f
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
-/
protected theorem IsOpenQuotientMap.piMap
    {f : ∀ i, A i → B i} (hf : ∀ i, IsOpenQuotientMap (f i)) : IsOpenQuotientMap (Pi.map f) :=
  ⟨.piMap fun i ↦ (hf i).1, .piMap fun i ↦ (hf i).2, .piMap (fun i ↦ (hf i).3) <|
    .of_forall fun i ↦ (hf i).1⟩
/-
**tendsto_pi_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_pi_nhds {f : Y -> forall i, A i} {g : forall i, A i} {u : Filter Y
} : Tendsto f u (𝓝 g) ↔ forall x, Tendsto (fun i => f i x) u (𝓝 (g x))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_pi`：nhds_pi {a : forall i, A i} : 𝓝 a = pi fun i => 𝓝 (a i)
· 使用定理 `Filter.tendsto_pi`：tendsto_pi {β : Type*} {m : β -> forall i, α i} {l : 
Filter β} : Tendsto m l (pi f) ↔ forall i, Tendsto (fun x => m x i) l (f i)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem tendsto_pi_nhds {f : Y → ∀ i, A i} {g : ∀ i, A i} {u : Filter Y} :
    Tendsto f u (𝓝 g) ↔ ∀ x, Tendsto (fun i => f i x) u (𝓝 (g x)) := by
  rw [nhds_pi, Filter.tendsto_pi]
/-
**continuousAt_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousAt_pi {f : X -> forall i, A i} {x : X} : ContinuousAt f x ↔ fora
ll i, ContinuousAt (fun y => f y i) x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_pi_nhds`：tendsto_pi_nhds {f : Y -> forall i, A i} {g : forall i,
 A i} {u : Filter Y} : Tendsto f u (𝓝 g) ↔ forall x, Tendsto (fun i => f i x) u 
(𝓝 (g…
-/
theorem continuousAt_pi {f : X → ∀ i, A i} {x : X} :
    ContinuousAt f x ↔ ∀ i, ContinuousAt (fun y => f y i) x :=
  tendsto_pi_nhds

@[fun_prop]
/-
**continuousAt_pi'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousAt_pi' {f : X -> forall i, A i} {x : X} (hf : forall i, Continuo
usAt (fun y => f y i) x) : ContinuousAt f x
参数：hf : forall i, ContinuousAt (fun y => f y i) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuousAt_pi`：continuousAt_pi {f : X -> forall i, A i} {x : X} : Cont
inuousAt f x ↔ forall i, ContinuousAt (fun y => f y i) x
-/
theorem continuousAt_pi' {f : X → ∀ i, A i} {x : X} (hf : ∀ i, ContinuousAt (fun y => f y i) x) :
    ContinuousAt f x :=
  continuousAt_pi.2 hf

@[fun_prop]
/-
**ContinuousAt.piMap** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAt`。
形式化陈述：∀ {ι : Type u_5} {A : ι → Type u_6} {B : ι → Type u_7} [T : (i : ι) → Topo
logicalSpace (A i)]   [inst : (i : ι) → TopologicalSpace (B i)] {f : (i : ι) → A
 i → B i} {x : (i : ι) → A i},   (∀ (i : ι), ContinuousAt (f i) (x i)) → Continu
ousAt (Pi.map f) x
参数：i : ι；A i；i : ι；B i；i : ι；i : ι；∀ (i : ι), ContinuousAt (f i) (x i)；Pi.map f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuousAt_pi`：continuousAt_pi {f : X -> forall i, A i} {x : X} : Cont
inuousAt f x ↔ forall i, ContinuousAt (fun y => f y i) x
· 使用定理 `ContinuousAt.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace
 Z] {f …
· 使用定理 `continuousAt_apply`：continuousAt_apply (i : ι) (x : forall i, A i) : Con
tinuousAt (fun p : forall i, A i => p i) x
-/
protected theorem ContinuousAt.piMap {f : ∀ i, A i → B i} {x : ∀ i, A i}
    (hf : ∀ i, ContinuousAt (f i) (x i)) :
    ContinuousAt (Pi.map f) x :=
  continuousAt_pi.2 fun i ↦ (hf i).comp (continuousAt_apply i x)
/-
**Topology.IsInducing.piMap** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsInducing`。
形式化陈述：∀ {ι : Type u_5} {A : ι → Type u_6} {B : ι → Type u_7} [T : (i : ι) → Topo
logicalSpace (A i)]   [inst : (i : ι) → TopologicalSpace (B i)] {f : (i : ι) → A
 i → B i},   (∀ (i : ι), Topology.IsInducing (f i)) → Topology.IsInducing (Pi.ma
p f)
参数：i : ι；A i；i : ι；B i；i : ι；∀ (i : ι), Topology.IsInducing (f i)；Pi.map f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_pi`：nhds_pi {a : forall i, A i} : 𝓝 a = pi fun i => 𝓝 (a i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Topology.IsInducing.nhds_eq_comap`：nhds_eq_comap (hf : IsInducing f) : f
orall x : X, 𝓝 x = comap f (𝓝 <| f x)
· 使用定理 `Filter.pi_comap`：pi_comap {β : ι -> Type*} {f : forall i, α i -> β i} {l
 : forall i, Filter (β i)} : pi (fun i => comap (f i) (l i)) = comap (Pi.map f) 
(pi l…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
protected lemma Topology.IsInducing.piMap {f : ∀ i, A i → B i}
    (hf : ∀ i, IsInducing (f i)) : IsInducing (Pi.map f) := by
  simp [isInducing_iff_nhds, nhds_pi, (hf _).nhds_eq_comap, Filter.pi_comap]
/-
**Topology.IsEmbedding.piMap** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsEmbedding`。
形式化陈述：∀ {ι : Type u_5} {A : ι → Type u_6} {B : ι → Type u_7} [T : (i : ι) → Topo
logicalSpace (A i)]   [inst : (i : ι) → TopologicalSpace (B i)] {f : (i : ι) → A
 i → B i},   (∀ (i : ι), Topology.IsEmbedding (f i)) → Topology.IsEmbedding (Pi.
map f)
参数：i : ι；A i；i : ι；B i；i : ι；∀ (i : ι), Topology.IsEmbedding (f i)；Pi.map f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.piMap`：∀ {ι : Type u_5} {A : ι → Type u_6} {B : ι → 
Type u_7} [T : (i : ι) → TopologicalSpace (A i)]   [inst : (i : ι) → Topological
Space (B i)] {f…
· 使用定理 `Topology.IsEmbedding.toIsInducing`：∀ {X : Type u_1} {Y : Type u_2} [tX :
 TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbeddi
ng f → Topology.IsInduc…
· 使用定理 `Function.Injective.piMap`：∀ {ι : Sort u_4} {α : ι → Sort u_5} {β : ι → S
ort u_6} {f : (i : ι) → α i → β i},   (∀ (i : ι), Function.Injective (f i)) → Fu
nction.Injecti…
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
-/
protected lemma Topology.IsEmbedding.piMap {f : ∀ i, A i → B i}
    (hf : ∀ i, IsEmbedding (f i)) : IsEmbedding (Pi.map f) :=
  ⟨.piMap fun i ↦ (hf i).1, .piMap fun i ↦ (hf i).2⟩
/-
**Pi.continuous_precomp'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Pi.continuous_precomp' {ι' : Type*} (φ : ι' -> ι) : Continuous (fun (f : (
forall i, A i)) (j : ι') => f (φ j))
参数：φ : ι' -> ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_pi`：continuous_pi (f : X → α → Y) (hf : ∀ a, Continuous (f x 
a)) : Continuous (fun x a ↦ f x a)
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
-/
theorem Pi.continuous_precomp' {ι' : Type*} (φ : ι' → ι) :
    Continuous (fun (f : (∀ i, A i)) (j : ι') ↦ f (φ j)) :=
  continuous_pi fun j ↦ continuous_apply (φ j)
/-
**Pi.continuous_precomp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Pi.continuous_precomp {ι' : Type*} (φ : ι' -> ι) : Continuous (· ∘ φ : (ι 
-> X) -> (ι' -> X))
参数：φ : ι' -> ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.continuous_precomp'`：Pi.continuous_precomp' {ι' : Type*} (φ : ι' -> ι
) : Continuous (fun (f : (forall i, A i)) (j : ι') => f (φ j))
-/
theorem Pi.continuous_precomp {ι' : Type*} (φ : ι' → ι) :
    Continuous (· ∘ φ : (ι → X) → (ι' → X)) :=
  Pi.continuous_precomp' φ
/-
**Pi.continuous_postcomp'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Pi.continuous_postcomp' {X : ι -> Type*} [forall i, TopologicalSpace (X i)
] {g : forall i, A i -> X i} (hg : forall i, Continuous (g i)) : Continuous (fun
 (f : (forall i, A i)) (i : ι) => g i (f i))
参数：X i；hg : forall i, Continuous (g i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_pi`：continuous_pi (f : X → α → Y) (hf : ∀ a, Continuous (f x 
a)) : Continuous (fun x a ↦ f x a)
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
-/
theorem Pi.continuous_postcomp' {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    {g : ∀ i, A i → X i} (hg : ∀ i, Continuous (g i)) :
    Continuous (fun (f : (∀ i, A i)) (i : ι) ↦ g i (f i)) :=
  continuous_pi fun i ↦ (hg i).comp <| continuous_apply i
/-
**Pi.continuous_postcomp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Pi.continuous_postcomp [TopologicalSpace Y] {g : X -> Y} (hg : Continuous 
g) : Continuous (g ∘ · : (ι -> X) -> (ι -> Y))
参数：hg : Continuous g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.continuous_postcomp'`：Pi.continuous_postcomp' {X : ι -> Type*} [foral
l i, TopologicalSpace (X i)] {g : forall i, A i -> X i} (hg : forall i, Continuo
us (g i)) : C…
-/
theorem Pi.continuous_postcomp [TopologicalSpace Y] {g : X → Y} (hg : Continuous g) :
    Continuous (g ∘ · : (ι → X) → (ι → Y)) :=
  Pi.continuous_postcomp' fun _ ↦ hg
/-
**Pi.induced_precomp'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Pi.induced_precomp' {ι' : Type*} (φ : ι' -> ι) : induced (fun (f : (forall
 i, A i)) (j : ι') => f (φ j)) Pi.topologicalSpace = ⨅ i', induced (eval (φ i'))
 (T (φ i'))
参数：φ : ι' -> ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `induced_iInf`：induced_iInf {ι : Sort w} {t : ι -> TopologicalSpace α} : 
(⨅ i, t i).induced g = ⨅ i, (t i).induced g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `induced_compose`：induced_compose {tγ : TopologicalSpace γ} {f : α -> β} 
{g : β -> γ} : (tγ.induced g).induced f = tγ.induced (g ∘ f)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Pi.induced_precomp' {ι' : Type*} (φ : ι' → ι) :
    induced (fun (f : (∀ i, A i)) (j : ι') ↦ f (φ j)) Pi.topologicalSpace =
    ⨅ i', induced (eval (φ i')) (T (φ i')) := by
  simp [Pi.topologicalSpace, induced_iInf, induced_compose, comp_def]
/-
**Pi.induced_precomp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Pi.induced_precomp [TopologicalSpace Y] {ι' : Type*} (φ : ι' -> ι) : induc
ed (· ∘ φ) Pi.topologicalSpace = ⨅ i', induced (eval (φ i')) ‹TopologicalSpace Y
›
参数：φ : ι' -> ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Pi.induced_precomp'`：Pi.induced_precomp' {ι' : Type*} (φ : ι' -> ι) : in
duced (fun (f : (forall i, A i)) (j : ι') => f (φ j)) Pi.topologicalSpace = ⨅ i'
, induced…
-/
lemma Pi.induced_precomp [TopologicalSpace Y] {ι' : Type*} (φ : ι' → ι) :
    induced (· ∘ φ) Pi.topologicalSpace =
    ⨅ i', induced (eval (φ i')) ‹TopologicalSpace Y› :=
  induced_precomp' φ

/-- Homeomorphism between `X → Y → Z` and `X × Y → Z` with product topologies. -/
@[simps]
/-
**Homeomorph.piCurry** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Homeomorph.piCurry {X Y Z : Type*} [TopologicalSpace Z] : (X × Y -> Z) ≃ₜ 
(X -> Y -> Z) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Homeomorphism between `X → Y → Z` and `X × Y → Z` with product topologies.
-/
def Homeomorph.piCurry {X Y Z : Type*}
    [TopologicalSpace Z] :
    (X × Y → Z) ≃ₜ (X → Y → Z) where
  toFun := Function.curry
  invFun := Function.uncurry
  right_inv := congrFun rfl
  left_inv := congrFun rfl
  continuous_toFun := continuous_pi (fun i ↦ Pi.continuous_precomp (Prod.mk i))

@[continuity, fun_prop]
/-
**Pi.continuous_domRestrict** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Pi.continuous_domRestrict (S : Set ι) : Continuous (S.domRestrict : (foral
l i : ι, A i) -> (forall i : S, A i))
参数：S : Set ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.continuous_precomp'`：Pi.continuous_precomp' {ι' : Type*} (φ : ι' -> ι
) : Continuous (fun (f : (forall i, A i)) (j : ι') => f (φ j))
-/
lemma Pi.continuous_domRestrict (S : Set ι) :
    Continuous (S.domRestrict : (∀ i : ι, A i) → (∀ i : S, A i)) :=
  Pi.continuous_precomp' ((↑) : S → ι)

@[deprecated (since := "2026-07-19")] alias Pi.continuous_restrict := Pi.continuous_domRestrict

@[continuity, fun_prop]
/-
**Pi.continuous_domRestrict** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Pi.continuous_domRestrict (S : Set ι) : Continuous (S.domRestrict : (foral
l i : ι, A i) -> (forall i : S, A i))
参数：S : Set ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.continuous_precomp'`：Pi.continuous_precomp' {ι' : Type*} (φ : ι' -> ι
) : Continuous (fun (f : (forall i, A i)) (j : ι') => f (φ j))
-/
lemma Pi.continuous_domRestrict₂ {s t : Set ι} (hst : s ⊆ t) :
    Continuous (domRestrict₂ (π := A) hst) := continuous_pi fun _ ↦ continuous_apply _

@[deprecated (since := "2026-07-19")] alias Pi.continuous_restrict₂ := Pi.continuous_domRestrict₂

@[continuity, fun_prop]
/-
**Finset.continuous_restrict** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.continuous_restrict (s : Finset ι) : Continuous (s.restrict (π
参数：s : Finset ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_pi`：continuous_pi (f : X → α → Y) (hf : ∀ a, Continuous (f x 
a)) : Continuous (fun x a ↦ f x a)
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
-/
theorem Finset.continuous_restrict (s : Finset ι) : Continuous (s.restrict (π := A)) :=
  continuous_pi fun _ ↦ continuous_apply _

@[continuity, fun_prop]
/-
**Finset.continuous_restrict** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.continuous_restrict (s : Finset ι) : Continuous (s.restrict (π
参数：s : Finset ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_pi`：continuous_pi (f : X → α → Y) (hf : ∀ a, Continuous (f x 
a)) : Continuous (fun x a ↦ f x a)
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
-/
theorem Finset.continuous_restrict₂ {s t : Finset ι} (hst : s ⊆ t) :
    Continuous (Finset.restrict₂ (π := A) hst) :=
  continuous_pi fun _ ↦ continuous_apply _

variable [TopologicalSpace Z]

@[continuity, fun_prop]
/-
**Pi.continuous_domRestrict_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Pi.continuous_domRestrict_apply (s : Set X) {f : X -> Z} (hf : Continuous 
f) : Continuous (s.domRestrict f)
参数：s : Set X；hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
-/
theorem Pi.continuous_domRestrict_apply (s : Set X) {f : X → Z} (hf : Continuous f) :
    Continuous (s.domRestrict f) := hf.comp continuous_subtype_val

@[deprecated (since := "2026-07-19")]
alias Pi.continuous_restrict_apply := Pi.continuous_domRestrict_apply

@[continuity, fun_prop]
/-
**Pi.continuous_domRestrict** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Pi.continuous_domRestrict (S : Set ι) : Continuous (S.domRestrict : (foral
l i : ι, A i) -> (forall i : S, A i))
参数：S : Set ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.continuous_precomp'`：Pi.continuous_precomp' {ι' : Type*} (φ : ι' -> ι
) : Continuous (fun (f : (forall i, A i)) (j : ι') => f (φ j))
-/
theorem Pi.continuous_domRestrict₂_apply {s t : Set X} (hst : s ⊆ t)
    {f : t → Z} (hf : Continuous f) :
    Continuous (domRestrict₂ (π := fun _ ↦ Z) hst f) := hf.comp (continuous_inclusion hst)

@[deprecated (since := "2026-07-19")]
alias Pi.continuous_restrict₂_apply := Pi.continuous_domRestrict₂_apply

@[continuity, fun_prop]
/-
**Finset.continuous_restrict_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.continuous_restrict_apply (s : Finset X) {f : X -> Z} (hf : Continu
ous f) : Continuous (s.restrict f)
参数：s : Finset X；hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
-/
theorem Finset.continuous_restrict_apply (s : Finset X) {f : X → Z} (hf : Continuous f) :
    Continuous (s.restrict f) := hf.comp continuous_subtype_val

@[continuity, fun_prop]
/-
**Finset.continuous_restrict** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.continuous_restrict (s : Finset ι) : Continuous (s.restrict (π
参数：s : Finset ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_pi`：continuous_pi (f : X → α → Y) (hf : ∀ a, Continuous (f x 
a)) : Continuous (fun x a ↦ f x a)
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
-/
theorem Finset.continuous_restrict₂_apply {s t : Finset X} (hst : s ⊆ t)
    {f : t → Z} (hf : Continuous f) :
    Continuous (restrict₂ (π := fun _ ↦ Z) hst f) := hf.comp (continuous_inclusion hst)
/-
**Pi.induced_domRestrict** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Pi.induced_domRestrict (S : Set ι) : induced (S.domRestrict) Pi.topologica
lSpace = ⨅ i in S, induced (eval i) (T i)
参数：S : Set ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Pi.induced_precomp'`：Pi.induced_precomp' {ι' : Type*} (φ : ι' -> ι) : in
duced (fun (f : (forall i, A i)) (j : ι') => f (φ j)) Pi.topologicalSpace = ⨅ i'
, induced…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Pi.induced_domRestrict (S : Set ι) :
    induced (S.domRestrict) Pi.topologicalSpace =
    ⨅ i ∈ S, induced (eval i) (T i) := by
  simp +unfoldPartialApp [← iInf_subtype'', ← induced_precomp' ((↑) : S → ι),
    domRestrict]

@[deprecated (since := "2026-07-19")] alias Pi.induced_restrict := Pi.induced_domRestrict
/-
**Pi.induced_domRestrict_sUnion** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Pi.induced_domRestrict_sUnion (𝔖 : Set (Set ι)) : induced (⋃₀ 𝔖).domRestri
ct (Pi.topologicalSpace (Y
参数：𝔖 : Set (Set ι)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Pi.induced_domRestrict`：Pi.induced_domRestrict (S : Set ι) : induced (S.
domRestrict) Pi.topologicalSpace = ⨅ i in S, induced (eval i) (T i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `iInf_sUnion`：iInf_sUnion (S : Set (Set α)) (f : α -> β) : (⨅ x in ⋃₀ S, 
f x) = ⨅ (s in S) (x in s), f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Pi.induced_domRestrict_sUnion (𝔖 : Set (Set ι)) :
    induced (⋃₀ 𝔖).domRestrict (Pi.topologicalSpace (Y := fun i : (⋃₀ 𝔖) ↦ A i)) =
    ⨅ S ∈ 𝔖, induced S.domRestrict Pi.topologicalSpace := by
  simp_rw [Pi.induced_domRestrict, iInf_sUnion]

@[deprecated (since := "2026-07-19")]
alias Pi.induced_restrict_sUnion := Pi.induced_domRestrict_sUnion
/-
**Filter.Tendsto.update** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.update [DecidableEq ι] {l : Filter Y} {f : Y -> forall i, A
 i} {x : forall i, A i} (hf : Tendsto f l (𝓝 x)) (i : ι) {g : Y -> A i} {xi : A 
i} (hg : Tendsto g l (𝓝 xi)) : Tendsto (fun a => update (f a) i (g a)) l (𝓝 <| u
pdate x i xi)
参数：hf : Tendsto f l (𝓝 x)；i : ι；hg : Tendsto g l (𝓝 xi)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendsto_pi_nhds`：tendsto_pi_nhds {f : Y -> forall i, A i} {g : forall i,
 A i} {u : Filter Y} : Tendsto f u (𝓝 g) ↔ forall x, Tendsto (fun i => f i x) u 
(𝓝 (g…
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Filter.Tendsto.apply_nhds`：Filter.Tendsto.apply_nhds {l : Filter Y} {f :
 Y -> forall i, A i} {x : forall i, A i} (h : Tendsto f l (𝓝 x)) (i : ι) : Tends
to (fun a => f …
-/
theorem Filter.Tendsto.update [DecidableEq ι] {l : Filter Y} {f : Y → ∀ i, A i} {x : ∀ i, A i}
    (hf : Tendsto f l (𝓝 x)) (i : ι) {g : Y → A i} {xi : A i} (hg : Tendsto g l (𝓝 xi)) :
    Tendsto (fun a => update (f a) i (g a)) l (𝓝 <| update x i xi) :=
  tendsto_pi_nhds.2 fun j => by rcases eq_or_ne j i with (rfl | hj) <;> simp [*, hf.apply_nhds]

@[fun_prop]
/-
**ContinuousAt.update** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAt.update [DecidableEq ι] {x : X} (hf : ContinuousAt f x) (i : ι
) {g : X -> A i} (hg : ContinuousAt g x) : ContinuousAt (fun a => update (f a) i
 (g a)) x
参数：hf : ContinuousAt f x；i : ι；hg : ContinuousAt g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.update`：Filter.Tendsto.update [DecidableEq ι] {l : Filter
 Y} {f : Y -> forall i, A i} {x : forall i, A i} (hf : Tendsto f l (𝓝 x)) (i : ι
) {g : Y ->…
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
-/
theorem ContinuousAt.update [DecidableEq ι] {x : X} (hf : ContinuousAt f x) (i : ι) {g : X → A i}
    (hg : ContinuousAt g x) : ContinuousAt (fun a => update (f a) i (g a)) x :=
  hf.tendsto.update i hg

@[fun_prop]
/-
**Continuous.update** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.update [DecidableEq ι] (hf : Continuous f) (i : ι) {g : X -> A 
i} (hg : Continuous g) : Continuous fun a => update (f a) i (g a)
参数：hf : Continuous f；i : ι；hg : Continuous g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `ContinuousAt.update`：ContinuousAt.update [DecidableEq ι] {x : X} (hf : C
ontinuousAt f x) (i : ι) {g : X -> A i} (hg : ContinuousAt g x) : ContinuousAt (
fun a => …
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
-/
theorem Continuous.update [DecidableEq ι] (hf : Continuous f) (i : ι) {g : X → A i}
    (hg : Continuous g) : Continuous fun a => update (f a) i (g a) :=
  continuous_iff_continuousAt.2 fun _ => hf.continuousAt.update i hg.continuousAt

/-- `Function.update f i x` is continuous in `(f, x)`. -/
@[continuity, fun_prop]
/-
**continuous_update** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_update [DecidableEq ι] (i : ι) : Continuous fun f : (forall j, 
A j) × A i => update f.1 i f.2
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.update`：Continuous.update [DecidableEq ι] (hf : Continuous f)
 (i : ι) {g : X -> A i} (hg : Continuous g) : Continuous fun a => update (f a) i
 (g a)
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)

--- 原说明 ---
`Function.update f i x` is continuous in `(f, x)`.
-/
theorem continuous_update [DecidableEq ι] (i : ι) :
    Continuous fun f : (∀ j, A j) × A i => update f.1 i f.2 :=
  continuous_fst.update i continuous_snd

/-- `Pi.mulSingle i x` is continuous in `x`. -/
@[to_additive (attr := continuity, fun_prop) /-- `Pi.single i x` is continuous in `x`. -/]
/-
**continuous_mulSingle** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_mulSingle [forall i, One (A i)] [DecidableEq ι] (i : ι) : Conti
nuous fun x => (Pi.mulSingle i x : forall i, A i)
参数：A i；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.update`：Continuous.update [DecidableEq ι] (hf : Continuous f)
 (i : ι) {g : X -> A i} (hg : Continuous g) : Continuous fun a => update (f a) i
 (g a)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)

--- 原说明 ---
`Pi.mulSingle i x` is continuous in `x`.
-/
theorem continuous_mulSingle [∀ i, One (A i)] [DecidableEq ι] (i : ι) :
    Continuous fun x => (Pi.mulSingle i x : ∀ i, A i) :=
  continuous_const.update _ continuous_id

section Fin
variable {n : ℕ} {A : Fin (n + 1) → Type*} [∀ i, TopologicalSpace (A i)]

/-
**Filter.Tendsto.finCons** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.finCons {f : Y -> A 0} {g : Y -> forall j : Fin n, A j.succ
} {l : Filter Y} {x : A 0} {y : forall j, A (Fin.succ j)} (hf : Tendsto f l (𝓝 x
)) (hg : Tendsto g l (𝓝 y)) : Tendsto (fun a => Fin.cons (f a) (g a)) l (𝓝 <| Fi
n.cons x y)
参数：Fin.succ j；hf : Tendsto f l (𝓝 x)；hg : Tendsto g l (𝓝 y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendsto_pi_nhds`：tendsto_pi_nhds {f : Y -> forall i, A i} {g : forall i,
 A i} {u : Filter Y} : Tendsto f u (𝓝 g) ↔ forall x, Tendsto (fun i => f i x) u 
(𝓝 (g…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fin.cons_zero`：cons_zero : cons x p 0 = x
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Fin.cons_succ`：cons_succ : cons x p i.succ = p i
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem Filter.Tendsto.finCons
    {f : Y → A 0} {g : Y → ∀ j : Fin n, A j.succ} {l : Filter Y} {x : A 0} {y : ∀ j, A (Fin.succ j)}
    (hf : Tendsto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) :
    Tendsto (fun a => Fin.cons (f a) (g a)) l (𝓝 <| Fin.cons x y) :=
  tendsto_pi_nhds.2 fun j => Fin.cases (by simpa) (by simpa using tendsto_pi_nhds.1 hg) j

@[fun_prop]
/-
**ContinuousAt.finCons** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAt.finCons {f : X -> A 0} {g : X -> forall j : Fin n, A (Fin.suc
c j)} {x : X} (hf : ContinuousAt f x) (hg : ContinuousAt g x) : ContinuousAt (fu
n a => Fin.cons (f a) (g a)) x
参数：Fin.succ j；hf : ContinuousAt f x；hg : ContinuousAt g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Filter.Tendsto.finCons`：Filter.Tendsto.finCons {f : Y -> A 0} {g : Y -> 
forall j : Fin n, A j.succ} {l : Filter Y} {x : A 0} {y : forall j, A (Fin.succ 
j)} (hf : Te…
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
-/
theorem ContinuousAt.finCons {f : X → A 0} {g : X → ∀ j : Fin n, A (Fin.succ j)} {x : X}
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (fun a => Fin.cons (f a) (g a)) x :=
  hf.tendsto.finCons hg

@[fun_prop]
/-
**Continuous.finCons** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.finCons {f : X -> A 0} {g : X -> forall j : Fin n, A (Fin.succ 
j)} (hf : Continuous f) (hg : Continuous g) : Continuous fun a => Fin.cons (f a)
 (g a)
参数：Fin.succ j；hf : Continuous f；hg : Continuous g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `ContinuousAt.finCons`：ContinuousAt.finCons {f : X -> A 0} {g : X -> fora
ll j : Fin n, A (Fin.succ j)} {x : X} (hf : ContinuousAt f x) (hg : ContinuousAt
 g x) : Co…
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
-/
theorem Continuous.finCons {f : X → A 0} {g : X → ∀ j : Fin n, A (Fin.succ j)}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun a => Fin.cons (f a) (g a) :=
  continuous_iff_continuousAt.2 fun _ => hf.continuousAt.finCons hg.continuousAt
/-
**Filter.Tendsto.matrixVecCons** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.matrixVecCons {f : Y -> Z} {g : Y -> Fin n -> Z} {l : Filte
r Y} {x : Z} {y : Fin n -> Z} (hf : Tendsto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) 
: Tendsto (fun a => Matrix.vecCons (f a) (g a)) l (𝓝 <| Matrix.vecCons x y)
参数：hf : Tendsto f l (𝓝 x)；hg : Tendsto g l (𝓝 y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.finCons`：Filter.Tendsto.finCons {f : Y -> A 0} {g : Y -> 
forall j : Fin n, A j.succ} {l : Filter Y} {x : A 0} {y : forall j, A (Fin.succ 
j)} (hf : Te…
-/
theorem Filter.Tendsto.matrixVecCons
    {f : Y → Z} {g : Y → Fin n → Z} {l : Filter Y} {x : Z} {y : Fin n → Z}
    (hf : Tendsto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) :
    Tendsto (fun a => Matrix.vecCons (f a) (g a)) l (𝓝 <| Matrix.vecCons x y) :=
  hf.finCons hg

@[fun_prop]
/-
**ContinuousAt.matrixVecCons** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAt.matrixVecCons {f : X -> Z} {g : X -> Fin n -> Z} {x : X} (hf 
: ContinuousAt f x) (hg : ContinuousAt g x) : ContinuousAt (fun a => Matrix.vecC
ons (f a) (g a)) x
参数：hf : ContinuousAt f x；hg : ContinuousAt g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.finCons`：ContinuousAt.finCons {f : X -> A 0} {g : X -> fora
ll j : Fin n, A (Fin.succ j)} {x : X} (hf : ContinuousAt f x) (hg : ContinuousAt
 g x) : Co…
-/
theorem ContinuousAt.matrixVecCons
    {f : X → Z} {g : X → Fin n → Z} {x : X} (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (fun a => Matrix.vecCons (f a) (g a)) x :=
  hf.finCons hg

@[fun_prop]
/-
**Continuous.matrixVecCons** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.matrixVecCons {f : X -> Z} {g : X -> Fin n -> Z} (hf : Continuo
us f) (hg : Continuous g) : Continuous fun a => Matrix.vecCons (f a) (g a)
参数：hf : Continuous f；hg : Continuous g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.finCons`：Continuous.finCons {f : X -> A 0} {g : X -> forall j
 : Fin n, A (Fin.succ j)} (hf : Continuous f) (hg : Continuous g) : Continuous f
un a => …
-/
theorem Continuous.matrixVecCons
    {f : X → Z} {g : X → Fin n → Z} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun a => Matrix.vecCons (f a) (g a) :=
  hf.finCons hg
/-
**Filter.Tendsto.finSnoc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.finSnoc {f : Y -> forall j : Fin n, A j.castSucc} {g : Y ->
 A (Fin.last _)} {l : Filter Y} {x : forall j, A (Fin.castSucc j)} {y : A (Fin.l
ast _)} (hf : Tendsto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) : Tendsto (fun a => Fi
n.snoc (f a) (g a)) l (𝓝 <| Fin.snoc x y)
参数：Fin.last _；Fin.castSucc j；Fin.last _；hf : Tendsto f l (𝓝 x)；hg : Tendsto g l 
(𝓝 y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendsto_pi_nhds`：tendsto_pi_nhds {f : Y -> forall i, A i} {g : forall i,
 A i} {u : Filter Y} : Tendsto f u (𝓝 g) ↔ forall x, Tendsto (fun i => f i x) u 
(𝓝 (g…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fin.snoc_last`：snoc_last : snoc p x (last n) = x
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Fin.snoc_castSucc`：snoc_castSucc : snoc p x i.castSucc = p i
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem Filter.Tendsto.finSnoc
    {f : Y → ∀ j : Fin n, A j.castSucc} {g : Y → A (Fin.last _)}
    {l : Filter Y} {x : ∀ j, A (Fin.castSucc j)} {y : A (Fin.last _)}
    (hf : Tendsto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) :
    Tendsto (fun a => Fin.snoc (f a) (g a)) l (𝓝 <| Fin.snoc x y) :=
  tendsto_pi_nhds.2 fun j => Fin.lastCases (by simpa) (by simpa using tendsto_pi_nhds.1 hf) j

@[fun_prop]
/-
**ContinuousAt.finSnoc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAt.finSnoc {f : X -> forall j : Fin n, A j.castSucc} {g : X -> A
 (Fin.last _)} {x : X} (hf : ContinuousAt f x) (hg : ContinuousAt g x) : Continu
ousAt (fun a => Fin.snoc (f a) (g a)) x
参数：Fin.last _；hf : ContinuousAt f x；hg : ContinuousAt g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.finSnoc`：Filter.Tendsto.finSnoc {f : Y -> forall j : Fin 
n, A j.castSucc} {g : Y -> A (Fin.last _)} {l : Filter Y} {x : forall j, A (Fin.
castSucc j)}…
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
-/
theorem ContinuousAt.finSnoc {f : X → ∀ j : Fin n, A j.castSucc} {g : X → A (Fin.last _)} {x : X}
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (fun a => Fin.snoc (f a) (g a)) x :=
  hf.tendsto.finSnoc hg

@[fun_prop]
/-
**Continuous.finSnoc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.finSnoc {f : X -> forall j : Fin n, A j.castSucc} {g : X -> A (
Fin.last _)} (hf : Continuous f) (hg : Continuous g) : Continuous fun a => Fin.s
noc (f a) (g a)
参数：Fin.last _；hf : Continuous f；hg : Continuous g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `ContinuousAt.finSnoc`：ContinuousAt.finSnoc {f : X -> forall j : Fin n, A
 j.castSucc} {g : X -> A (Fin.last _)} {x : X} (hf : ContinuousAt f x) (hg : Con
tinuousAt …
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
-/
theorem Continuous.finSnoc {f : X → ∀ j : Fin n, A j.castSucc} {g : X → A (Fin.last _)}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun a => Fin.snoc (f a) (g a) :=
  continuous_iff_continuousAt.2 fun _ => hf.continuousAt.finSnoc hg.continuousAt
/-
**Filter.Tendsto.finInsertNth** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.finInsertNth (i : Fin (n + 1)) {f : Y -> A i} {g : Y -> for
all j : Fin n, A (i.succAbove j)} {l : Filter Y} {x : A i} {y : forall j, A (i.s
uccAbove j)} (hf : Tendsto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) : Tendsto (fun a 
=> i.insertNth (f a) (g a)) l (𝓝 <| i.insertNth x y)
参数：i : Fin (n + 1)；i.succAbove j；i.succAbove j；hf : Tendsto f l (𝓝 x)；hg : Tends
to g l (𝓝 y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendsto_pi_nhds`：tendsto_pi_nhds {f : Y -> forall i, A i} {g : forall i,
 A i} {u : Filter Y} : Tendsto f u (𝓝 g) ↔ forall x, Tendsto (fun i => f i x) u 
(𝓝 (g…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fin.insertNth_apply_same`：insertNth_apply_same (i : Fin (n + 1)) (x : α 
i) (p : forall j, α (i.succAbove j)) : insertNth i x p i = x
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Fin.insertNth_apply_succAbove`：insertNth_apply_succAbove (i : Fin (n + 1
)) (x : α i) (p : forall j, α (i.succAbove j)) (j : Fin n) : insertNth i x p (i.
succAbove j) = p j
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem Filter.Tendsto.finInsertNth
    (i : Fin (n + 1)) {f : Y → A i} {g : Y → ∀ j : Fin n, A (i.succAbove j)} {l : Filter Y}
    {x : A i} {y : ∀ j, A (i.succAbove j)} (hf : Tendsto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) :
    Tendsto (fun a => i.insertNth (f a) (g a)) l (𝓝 <| i.insertNth x y) :=
  tendsto_pi_nhds.2 fun j => Fin.succAboveCases i (by simpa) (by simpa using tendsto_pi_nhds.1 hg) j

@[fun_prop]
/-
**ContinuousAt.finInsertNth** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAt.finInsertNth (i : Fin (n + 1)) {f : X -> A i} {g : X -> foral
l j : Fin n, A (i.succAbove j)} {x : X} (hf : ContinuousAt f x) (hg : Continuous
At g x) : ContinuousAt (fun a => i.insertNth (f a) (g a)) x
参数：i : Fin (n + 1)；i.succAbove j；hf : ContinuousAt f x；hg : ContinuousAt g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.finInsertNth`：Filter.Tendsto.finInsertNth (i : Fin (n + 1
)) {f : Y -> A i} {g : Y -> forall j : Fin n, A (i.succAbove j)} {l : Filter Y} 
{x : A i} {y : fo…
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
-/
theorem ContinuousAt.finInsertNth
    (i : Fin (n + 1)) {f : X → A i} {g : X → ∀ j : Fin n, A (i.succAbove j)} {x : X}
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (fun a => i.insertNth (f a) (g a)) x :=
  hf.tendsto.finInsertNth i hg

@[fun_prop]
/-
**Continuous.finInsertNth** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.finInsertNth (i : Fin (n + 1)) {f : X -> A i} {g : X -> forall 
j : Fin n, A (i.succAbove j)} (hf : Continuous f) (hg : Continuous g) : Continuo
us fun a => i.insertNth (f a) (g a)
参数：i : Fin (n + 1)；i.succAbove j；hf : Continuous f；hg : Continuous g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `ContinuousAt.finInsertNth`：ContinuousAt.finInsertNth (i : Fin (n + 1)) {
f : X -> A i} {g : X -> forall j : Fin n, A (i.succAbove j)} {x : X} (hf : Conti
nuousAt f x) (h…
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
-/
theorem Continuous.finInsertNth
    (i : Fin (n + 1)) {f : X → A i} {g : X → ∀ j : Fin n, A (i.succAbove j)}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun a => i.insertNth (f a) (g a) :=
  continuous_iff_continuousAt.2 fun _ => hf.continuousAt.finInsertNth i hg.continuousAt
/-
**Filter.Tendsto.finInit** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.finInit {f : Y -> forall j : Fin (n + 1), A j} {l : Filter 
Y} {x : forall j, A j} (hg : Tendsto f l (𝓝 x)) : Tendsto (fun a => Fin.init (f 
a)) l (𝓝 <| Fin.init x)
参数：n + 1；hg : Tendsto f l (𝓝 x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendsto_pi_nhds`：tendsto_pi_nhds {f : Y -> forall i, A i} {g : forall i,
 A i} {u : Filter Y} : Tendsto f u (𝓝 g) ↔ forall x, Tendsto (fun i => f i x) u 
(𝓝 (g…
· 使用定理 `Filter.Tendsto.apply_nhds`：Filter.Tendsto.apply_nhds {l : Filter Y} {f :
 Y -> forall i, A i} {x : forall i, A i} (h : Tendsto f l (𝓝 x)) (i : ι) : Tends
to (fun a => f …
-/
theorem Filter.Tendsto.finInit {f : Y → ∀ j : Fin (n + 1), A j} {l : Filter Y} {x : ∀ j, A j}
    (hg : Tendsto f l (𝓝 x)) : Tendsto (fun a ↦ Fin.init (f a)) l (𝓝 <| Fin.init x) :=
  tendsto_pi_nhds.2 fun j ↦ apply_nhds hg j.castSucc

@[fun_prop]
/-
**ContinuousAt.finInit** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAt.finInit {f : X -> forall j : Fin (n + 1), A j} {x : X} (hf : 
ContinuousAt f x) : ContinuousAt (fun a => Fin.init (f a)) x
参数：n + 1；hf : ContinuousAt f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.finInit`：Filter.Tendsto.finInit {f : Y -> forall j : Fin 
(n + 1), A j} {l : Filter Y} {x : forall j, A j} (hg : Tendsto f l (𝓝 x)) : Tend
sto (fun a =…
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
-/
theorem ContinuousAt.finInit {f : X → ∀ j : Fin (n + 1), A j} {x : X}
    (hf : ContinuousAt f x) : ContinuousAt (fun a ↦ Fin.init (f a)) x :=
  hf.tendsto.finInit

@[fun_prop]
/-
**Continuous.finInit** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.finInit {f : X -> forall j : Fin (n + 1), A j} (hf : Continuous
 f) : Continuous fun a => Fin.init (f a)
参数：n + 1；hf : Continuous f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `ContinuousAt.finInit`：ContinuousAt.finInit {f : X -> forall j : Fin (n +
 1), A j} {x : X} (hf : ContinuousAt f x) : ContinuousAt (fun a => Fin.init (f a
)) x
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
-/
theorem Continuous.finInit {f : X → ∀ j : Fin (n + 1), A j} (hf : Continuous f) :
    Continuous fun a ↦ Fin.init (f a) :=
  continuous_iff_continuousAt.2 fun _ ↦ hf.continuousAt.finInit
/-
**Filter.Tendsto.finTail** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.finTail {f : Y -> forall j : Fin (n + 1), A j} {l : Filter 
Y} {x : forall j, A j} (hg : Tendsto f l (𝓝 x)) : Tendsto (fun a => Fin.tail (f 
a)) l (𝓝 <| Fin.tail x)
参数：n + 1；hg : Tendsto f l (𝓝 x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendsto_pi_nhds`：tendsto_pi_nhds {f : Y -> forall i, A i} {g : forall i,
 A i} {u : Filter Y} : Tendsto f u (𝓝 g) ↔ forall x, Tendsto (fun i => f i x) u 
(𝓝 (g…
· 使用定理 `Filter.Tendsto.apply_nhds`：Filter.Tendsto.apply_nhds {l : Filter Y} {f :
 Y -> forall i, A i} {x : forall i, A i} (h : Tendsto f l (𝓝 x)) (i : ι) : Tends
to (fun a => f …
-/
theorem Filter.Tendsto.finTail {f : Y → ∀ j : Fin (n + 1), A j} {l : Filter Y} {x : ∀ j, A j}
    (hg : Tendsto f l (𝓝 x)) : Tendsto (fun a ↦ Fin.tail (f a)) l (𝓝 <| Fin.tail x) :=
  tendsto_pi_nhds.2 fun j ↦ apply_nhds hg j.succ

@[fun_prop]
/-
**ContinuousAt.finTail** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAt.finTail {f : X -> forall j : Fin (n + 1), A j} {x : X} (hf : 
ContinuousAt f x) : ContinuousAt (fun a => Fin.tail (f a)) x
参数：n + 1；hf : ContinuousAt f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.finTail`：Filter.Tendsto.finTail {f : Y -> forall j : Fin 
(n + 1), A j} {l : Filter Y} {x : forall j, A j} (hg : Tendsto f l (𝓝 x)) : Tend
sto (fun a =…
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
-/
theorem ContinuousAt.finTail {f : X → ∀ j : Fin (n + 1), A j} {x : X}
    (hf : ContinuousAt f x) : ContinuousAt (fun a ↦ Fin.tail (f a)) x :=
  hf.tendsto.finTail

@[fun_prop]
/-
**Continuous.finTail** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.finTail {f : X -> forall j : Fin (n + 1), A j} (hf : Continuous
 f) : Continuous fun a => Fin.tail (f a)
参数：n + 1；hf : Continuous f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `ContinuousAt.finTail`：ContinuousAt.finTail {f : X -> forall j : Fin (n +
 1), A j} {x : X} (hf : ContinuousAt f x) : ContinuousAt (fun a => Fin.tail (f a
)) x
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
-/
theorem Continuous.finTail {f : X → ∀ j : Fin (n + 1), A j} (hf : Continuous f) :
    Continuous fun a ↦ Fin.tail (f a) :=
  continuous_iff_continuousAt.2 fun _ ↦ hf.continuousAt.finTail

end Fin

/-
**isOpen_set_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpen_set_pi {i : Set ι} {s : forall a, Set (A a)} (hi : i.Finite) (hs : 
forall a in i, IsOpen (s a)) : IsOpen (pi i s)
参数：A a；hi : i.Finite；hs : forall a in i, IsOpen (s a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.pi_def`：pi_def (i : Set α) (s : forall a, Set (π a)) : pi i s = ⋂ a 
in i, eval a ⁻¹' s a
· 使用定理 `Set.Finite.isOpen_biInter`：Set.Finite.isOpen_biInter {s : Set α} {f : α 
-> Set X} (hs : s.Finite) (h : forall i in s, IsOpen (f i)) : IsOpen (⋂ i in s, 
f i)
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
-/
theorem isOpen_set_pi {i : Set ι} {s : ∀ a, Set (A a)} (hi : i.Finite)
    (hs : ∀ a ∈ i, IsOpen (s a)) : IsOpen (pi i s) := by
  rw [pi_def]; exact hi.isOpen_biInter fun a ha => (hs _ ha).preimage (continuous_apply _)
/-
**isOpen_pi_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpen_pi_iff {s : Set (forall a, A a)} : IsOpen s ↔ forall f, f in s -> e
xists (I : Finset ι) (u : forall a, Set (A a)), (forall a, a in I -> IsOpen (u a
) ∧ f a in u a) ∧ (I : Set ι).pi u subseteq s
参数：forall a, A a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isOpen_iff_nhds`：isOpen_iff_nhds : IsOpen s ↔ forall x in s, 𝓝 x <= 𝓟 s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `nhds_pi`：nhds_pi {a : forall i, A i} : 𝓝 a = pi fun i => 𝓝 (a i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.eval_image_pi`：eval_image_pi (hs : i in s) (ht : (s.pi t).Nonempty) 
: eval i '' s.pi t = t i
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)
· 使用定理 `Set.pi_nonempty_iff`：pi_nonempty_iff : (s.pi t).Nonempty ↔ forall i, exi
sts x, i in s -> x in t i
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.pi_mono`：pi_mono (h : forall i in s, t₁ i subseteq t₂ i) : pi s t₁ s
ubseteq pi s t₂
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.eval_image_pi_subset`：eval_image_pi_subset (hs : i in s) : eval i ''
 s.pi t subseteq t i
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.univ_pi_ite`：univ_pi_ite (s : Set ι) [DecidablePred (· in s)] (t : f
orall i, Set (α i)) : (pi univ fun i => if i in s then t i else univ) = s.pi t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
（共 31 条，此处仅展示前 30 条）
-/
theorem isOpen_pi_iff {s : Set (∀ a, A a)} :
    IsOpen s ↔
      ∀ f, f ∈ s → ∃ (I : Finset ι) (u : ∀ a, Set (A a)),
        (∀ a, a ∈ I → IsOpen (u a) ∧ f a ∈ u a) ∧ (I : Set ι).pi u ⊆ s := by
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
    refine ⟨I, fun a => ite (a ∈ I) (t a) univ, fun i => ?_, ?_⟩
    · by_cases hi : i ∈ I
      · use t i
        simp_rw [if_pos hi]
        exact ⟨Subset.rfl, (h1 i) hi⟩
      · use univ
        simp_rw [if_neg hi]
        exact ⟨Subset.rfl, isOpen_univ, mem_univ _⟩
    · rw [← univ_pi_ite]
      simp only [← ite_and, ← Finset.mem_coe, and_self_iff, univ_pi_ite, h2]
/-
**isOpen_pi_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpen_pi_iff' [Finite ι] {s : Set (forall a, A a)} : IsOpen s ↔ forall f,
 f in s -> exists u : forall a, Set (A a), (forall a, IsOpen (u a) ∧ f a in u a)
 ∧ univ.pi u subseteq s
参数：forall a, A a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isOpen_iff_nhds`：isOpen_iff_nhds : IsOpen s ↔ forall x in s, 𝓝 x <= 𝓟 s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `nhds_pi`：nhds_pi {a : forall i, A i} : 𝓝 a = pi fun i => 𝓝 (a i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.pi_mono`：pi_mono (h : forall i in s, t₁ i subseteq t₂ i) : pi s t₁ s
ubseteq pi s t₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.pi_inter_compl`：pi_inter_compl (s : Set ι) : pi s t inter pi sᶜ t = 
pi univ t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
-/
theorem isOpen_pi_iff' [Finite ι] {s : Set (∀ a, A a)} :
    IsOpen s ↔
      ∀ f, f ∈ s → ∃ u : ∀ a, Set (A a), (∀ a, IsOpen (u a) ∧ f a ∈ u a) ∧ univ.pi u ⊆ s := by
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
/-
**isClosed_set_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_set_pi {i : Set ι} {s : forall a, Set (A a)} (hs : forall a in i,
 IsClosed (s a)) : IsClosed (pi i s)
参数：A a；hs : forall a in i, IsClosed (s a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.pi_def`：pi_def (i : Set α) (s : forall a, Set (π a)) : pi i s = ⋂ a 
in i, eval a ⁻¹' s a
· 使用定理 `isClosed_biInter`：isClosed_biInter {s : Set α} {f : α -> Set X} (h : for
all i in s, IsClosed (f i)) : IsClosed (⋂ i in s, f i)
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
-/
theorem isClosed_set_pi {i : Set ι} {s : ∀ a, Set (A a)} (hs : ∀ a ∈ i, IsClosed (s a)) :
    IsClosed (pi i s) := by
  rw [pi_def]; exact isClosed_biInter fun a ha => (hs _ ha).preimage (continuous_apply _)
/-
**Topology.IsClosedEmbedding.piMap** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsClosedE
mbedding`。
形式化陈述：∀ {ι : Type u_5} {A : ι → Type u_6} {B : ι → Type u_7} [T : (i : ι) → Topo
logicalSpace (A i)]   [inst : (i : ι) → TopologicalSpace (B i)] {f : (i : ι) → A
 i → B i},   (∀ (i : ι), Topology.IsClosedEmbedding (f i)) → Topology.IsClosedEm
bedding (Pi.map f)
参数：i : ι；A i；i : ι；B i；i : ι；∀ (i : ι), Topology.IsClosedEmbedding (f i)；Pi.map 
f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.piMap`：∀ {ι : Type u_5} {A : ι → Type u_6} {B : ι →
 Type u_7} [T : (i : ι) → TopologicalSpace (A i)]   [inst : (i : ι) → Topologica
lSpace (B i)] {f…
· 使用定理 `Topology.IsClosedEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2
} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.Is
ClosedEmbedding f → Topology.I…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_piMap`：range_piMap (f : forall i, α i -> β i) : range (Pi.map 
f) = pi univ fun i => range (f i)
· 使用定理 `isClosed_set_pi`：isClosed_set_pi {i : Set ι} {s : forall a, Set (A a)} (
hs : forall a in i, IsClosed (s a)) : IsClosed (pi i s)
· 使用定理 `Topology.IsClosedEmbedding.isClosed_range`：∀ {X : Type u_1} {Y : Type u_
2} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.I
sClosedEmbedding f → IsClosed (…
-/
protected lemma Topology.IsClosedEmbedding.piMap {f : ∀ i, A i → B i}
    (hf : ∀ i, IsClosedEmbedding (f i)) : IsClosedEmbedding (Pi.map f) :=
  ⟨.piMap fun i ↦ (hf i).1, by simpa using isClosed_set_pi fun i _ ↦ (hf i).2⟩
/-
**Topology.IsOpenEmbedding.piMap** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsOpenEmbed
ding`。
形式化陈述：∀ {ι : Type u_5} {A : ι → Type u_6} {B : ι → Type u_7} [T : (i : ι) → Topo
logicalSpace (A i)]   [inst : (i : ι) → TopologicalSpace (B i)] [Finite ι] {f : 
(i : ι) → A i → B i},   (∀ (i : ι), Topology.IsOpenEmbedding (f i)) → Topology.I
sOpenEmbedding (Pi.map f)
参数：i : ι；A i；i : ι；B i；i : ι；∀ (i : ι), Topology.IsOpenEmbedding (f i)；Pi.map f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.piMap`：∀ {ι : Type u_5} {A : ι → Type u_6} {B : ι →
 Type u_7} [T : (i : ι) → TopologicalSpace (A i)]   [inst : (i : ι) → Topologica
lSpace (B i)] {f…
· 使用定理 `Topology.IsOpenEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
[tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOp
enEmbedding f → Topology.IsE…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_piMap`：range_piMap (f : forall i, α i -> β i) : range (Pi.map 
f) = pi univ fun i => range (f i)
· 使用定理 `isOpen_set_pi`：isOpen_set_pi {i : Set ι} {s : forall a, Set (A a)} (hi :
 i.Finite) (hs : forall a in i, IsOpen (s a)) : IsOpen (pi i s)
· 使用定理 `Set.finite_univ`：∀ {α : Type u} [Finite α], Set.univ.Finite
· 使用定理 `Topology.IsOpenEmbedding.isOpen_range`：∀ {X : Type u_1} {Y : Type u_2} [
tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOpe
nEmbedding f → IsOpen (Set.…
-/
protected lemma Topology.IsOpenEmbedding.piMap [Finite ι] {f : ∀ i, A i → B i}
    (hf : ∀ i, IsOpenEmbedding (f i)) : IsOpenEmbedding (Pi.map f) :=
  ⟨.piMap fun i ↦ (hf i).1, by simpa using isOpen_set_pi Set.finite_univ fun i _ ↦ (hf i).2⟩
/-
**mem_nhds_of_pi_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_nhds_of_pi_mem_nhds {I : Set ι} {s : forall i, Set (A i)} (a : forall 
i, A i) (hs : I.pi s in 𝓝 a) {i : ι} (hi : i in I) : s i in 𝓝 (a i)
参数：A i；a : forall i, A i；hs : I.pi s in 𝓝 a；hi : i in I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_of_pi_mem_pi`：mem_of_pi_mem_pi [forall i, NeBot (f i)] {I : S
et ι} (h : I.pi s in pi f) {i : ι} (hi : i in I) : s i in f i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_pi`：nhds_pi {a : forall i, A i} : 𝓝 a = pi fun i => 𝓝 (a i)
-/
theorem mem_nhds_of_pi_mem_nhds {I : Set ι} {s : ∀ i, Set (A i)} (a : ∀ i, A i) (hs : I.pi s ∈ 𝓝 a)
    {i : ι} (hi : i ∈ I) : s i ∈ 𝓝 (a i) := by
  rw [nhds_pi] at hs; exact mem_of_pi_mem_pi hs hi
/-
**set_pi_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：set_pi_mem_nhds {i : Set ι} {s : forall a, Set (A a)} {x : forall a, A a} 
(hi : i.Finite) (hs : forall a in i, s a in 𝓝 (x a)) : pi i s in 𝓝 x
参数：A a；hi : i.Finite；hs : forall a in i, s a in 𝓝 (x a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.pi_def`：pi_def (i : Set α) (s : forall a, Set (π a)) : pi i s = ⋂ a 
in i, eval a ⁻¹' s a
· 使用定理 `Filter.biInter_mem`：biInter_mem {β : Type v} {s : β -> Set α} {is : Set 
β} (hf : is.Finite) : (⋂ i in is, s i) in f ↔ forall i in is, s i in f
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
-/
theorem set_pi_mem_nhds {i : Set ι} {s : ∀ a, Set (A a)} {x : ∀ a, A a} (hi : i.Finite)
    (hs : ∀ a ∈ i, s a ∈ 𝓝 (x a)) : pi i s ∈ 𝓝 x := by
  rw [pi_def, biInter_mem hi]
  exact fun a ha => (continuous_apply a).continuousAt (hs a ha)
/-
**set_pi_mem_nhds_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：set_pi_mem_nhds_iff {I : Set ι} (hI : I.Finite) {s : forall i, Set (A i)} 
(a : forall i, A i) : I.pi s in 𝓝 a ↔ forall i : ι, i in I -> s i in 𝓝 (a i)
参数：hI : I.Finite；A i；a : forall i, A i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_pi`：nhds_pi {a : forall i, A i} : 𝓝 a = pi fun i => 𝓝 (a i)
· 使用定理 `Filter.pi_mem_pi_iff`：pi_mem_pi_iff [forall i, NeBot (f i)] {I : Set ι} 
(hI : I.Finite) : I.pi s in pi f ↔ forall i in I, s i in f i
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem set_pi_mem_nhds_iff {I : Set ι} (hI : I.Finite) {s : ∀ i, Set (A i)} (a : ∀ i, A i) :
    I.pi s ∈ 𝓝 a ↔ ∀ i : ι, i ∈ I → s i ∈ 𝓝 (a i) := by
  rw [nhds_pi, pi_mem_pi_iff hI]
/-
**interior_pi_set** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：interior_pi_set {I : Set ι} (hI : I.Finite) {s : forall i, Set (A i)} : in
terior (pi I s) = I.pi fun i => interior (s i)
参数：hI : I.Finite；A i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `set_pi_mem_nhds_iff`：set_pi_mem_nhds_iff {I : Set ι} (hI : I.Finite) {s 
: forall i, Set (A i)} (a : forall i, A i) : I.pi s in 𝓝 a ↔ forall i : ι, i in 
I -> s i …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem interior_pi_set {I : Set ι} (hI : I.Finite) {s : ∀ i, Set (A i)} :
    interior (pi I s) = I.pi fun i => interior (s i) := by
  ext a
  simp only [Set.mem_pi, mem_interior_iff_mem_nhds, set_pi_mem_nhds_iff hI]
/-
**exists_finset_piecewise_mem_of_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_finset_piecewise_mem_of_mem_nhds [DecidableEq ι] {s : Set (forall a
, A a)} {x : forall a, A a} (hs : s in 𝓝 x) (y : forall a, A a) : exists I : Fin
set ι, I.piecewise x y in s
参数：forall a, A a；hs : s in 𝓝 x；y : forall a, A a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_pi`：nhds_pi {a : forall i, A i} : 𝓝 a = pi fun i => 𝓝 (a i)
· 使用引理 `Finset.piecewise_eq_of_mem`：piecewise_eq_of_mem {i : ι} (hi : i in s) : 
s.piecewise f g i = f i
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
-/
theorem exists_finset_piecewise_mem_of_mem_nhds [DecidableEq ι] {s : Set (∀ a, A a)} {x : ∀ a, A a}
    (hs : s ∈ 𝓝 x) (y : ∀ a, A a) : ∃ I : Finset ι, I.piecewise x y ∈ s := by
  simp only [nhds_pi, Filter.mem_pi'] at hs
  rcases hs with ⟨I, t, htx, hts⟩
  refine ⟨I, hts fun i hi => ?_⟩
  simpa [Finset.mem_coe.1 hi] using mem_of_mem_nhds (htx i)
/-
**pi_generateFrom_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pi_generateFrom_eq {A : ι -> Type*} {g : forall a, Set (Set (A a))} : (@Pi
.topologicalSpace ι A fun a => generateFrom (g a)) = generateFrom { t | exists (
s : forall a, Set (A a)) (i : Finset ι), (forall a in i, s a in g a) ∧ t = pi (↑
i) s }
参数：Set (A a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_generateFrom`：le_generateFrom {t : TopologicalSpace α} {g : Set (Set 
α)} (h : forall s in g, IsOpen s) : t <= generateFrom g
· 使用定理 `isOpen_set_pi`：isOpen_set_pi {i : Set ι} {s : forall a, Set (A a)} (hi :
 i.Finite) (hs : forall a in i, IsOpen (s a)) : IsOpen (pi i s)
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `coinduced_le_iff_le_induced`：coinduced_le_iff_le_induced {f : α -> β} {t
α : TopologicalSpace α} {tβ : TopologicalSpace β} : tα.coinduced f <= tβ ↔ tα <=
 tβ.induced f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `Set.singleton_pi`：singleton_pi (i : ι) (t : forall i, Set (α i)) : pi {i
} t = eval i ⁻¹' t i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem pi_generateFrom_eq {A : ι → Type*} {g : ∀ a, Set (Set (A a))} :
    (@Pi.topologicalSpace ι A fun a => generateFrom (g a)) =
      generateFrom
        { t | ∃ (s : ∀ a, Set (A a)) (i : Finset ι), (∀ a ∈ i, s a ∈ g a) ∧ t = pi (↑i) s } := by
  refine le_antisymm ?_ ?_
  · apply le_generateFrom
    rintro _ ⟨s, i, hi, rfl⟩
    let := fun a => generateFrom (g a)
    exact isOpen_set_pi i.finite_toSet (fun a ha => GenerateOpen.basic _ (hi a ha))
  · classical
    refine le_iInf fun i => coinduced_le_iff_le_induced.1 <| le_generateFrom fun s hs => ?_
    refine GenerateOpen.basic _ ⟨update (fun i => univ) i s, {i}, ?_⟩
    simp [hs]
/-
**pi_eq_generateFrom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pi_eq_generateFrom : Pi.topologicalSpace = generateFrom { g | exists (s : 
forall a, Set (A a)) (i : Finset ι), (forall a in i, IsOpen (s a)) ∧ g = pi (↑i)
 s }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `TopologicalSpace.generateFrom_setOfPred_isOpen`：generateFrom_setOfPred_i
sOpen (t : TopologicalSpace α) : generateFrom { s | IsOpen[t] s } = t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pi_generateFrom_eq`：pi_generateFrom_eq {A : ι -> Type*} {g : forall a, S
et (Set (A a))} : (@Pi.topologicalSpace ι A fun a => generateFrom (g a)) = gener
ateFrom …
-/
theorem pi_eq_generateFrom :
    Pi.topologicalSpace =
      generateFrom
        { g | ∃ (s : ∀ a, Set (A a)) (i : Finset ι), (∀ a ∈ i, IsOpen (s a)) ∧ g = pi (↑i) s } :=
  calc Pi.topologicalSpace
  _ = @Pi.topologicalSpace ι A fun _ => generateFrom { s | IsOpen s } := by
    simp +instances only [generateFrom_setOfPred_isOpen]
  _ = _ := pi_generateFrom_eq
/-
**pi_generateFrom_eq_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pi_generateFrom_eq_finite {X : ι -> Type*} {g : forall a, Set (Set (X a))}
 [Finite ι] (hg : forall a, ⋃₀ g a = univ) : (@Pi.topologicalSpace ι X fun a => 
generateFrom (g a)) = generateFrom { t | exists s : forall a, Set (X a), (forall
 a, s a in g a) ∧ t = pi univ s }
参数：Set (X a)；hg : forall a, ⋃₀ g a = univ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pi_generateFrom_eq`：pi_generateFrom_eq {A : ι -> Type*} {g : forall a, S
et (Set (A a))} : (@Pi.topologicalSpace ι A fun a => generateFrom (g a)) = gener
ateFrom …
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `TopologicalSpace.generateFrom_anti`：generateFrom_anti {α} {g₁ g₂ : Set (
Set α)} (h : g₁ subseteq g₂) : generateFrom g₂ <= generateFrom g₁
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `le_generateFrom`：le_generateFrom {t : TopologicalSpace α} {g : Set (Set 
α)} (h : forall s in g, IsOpen s) : t <= generateFrom g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isOpen_iff_forall_mem_open`：isOpen_iff_forall_mem_open : IsOpen s ↔ fora
ll x in s, exists t, t subseteq s ∧ IsOpen t ∧ x in t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.univ_pi_piecewise`：univ_pi_piecewise {ι : Type*} {α : ι -> Type*} (s
 : Set ι) (t t' : forall i, Set (α i)) [forall x, Decidable (x in s)] : pi univ 
(s.piecewis…
· 使用定理 `Set.piecewise_eq_of_mem`：piecewise_eq_of_mem {i : α} (hi : i in s) : s.p
iecewise f g i = f i
· 使用定理 `Set.piecewise_eq_of_notMem`：piecewise_eq_of_notMem {i : α} (hi : i ∉ s) 
: s.piecewise f g i = g i
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.sUnion_eq_univ_iff`：sUnion_eq_univ_iff {c : Set (Set α)} : ⋃₀ c = un
iv ↔ forall a, exists b in c, a in b
（共 31 条，此处仅展示前 30 条）
-/
theorem pi_generateFrom_eq_finite {X : ι → Type*} {g : ∀ a, Set (Set (X a))} [Finite ι]
    (hg : ∀ a, ⋃₀ g a = univ) :
    (@Pi.topologicalSpace ι X fun a => generateFrom (g a)) =
      generateFrom { t | ∃ s : ∀ a, Set (X a), (∀ a, s a ∈ g a) ∧ t = pi univ s } := by
  cases nonempty_fintype ι
  rw [pi_generateFrom_eq]
  refine le_antisymm (generateFrom_anti ?_) (le_generateFrom ?_)
  · exact fun s ⟨t, ht, Eq⟩ => ⟨t, Finset.univ, by simp [ht, Eq]⟩
  · rintro s ⟨t, i, ht, rfl⟩
    let := generateFrom { t | ∃ s : ∀ a, Set (X a), (∀ a, s a ∈ g a) ∧ t = pi univ s }
    refine isOpen_iff_forall_mem_open.2 fun f hf => ?_
    choose c hcg hfc using fun a => sUnion_eq_univ_iff.1 (hg a) (f a)
    refine ⟨pi i t ∩ pi ((↑i)ᶜ : Set ι) c, inter_subset_left, ?_, ⟨hf, fun a _ => hfc a⟩⟩
    classical
    rw [← univ_pi_piecewise]
    refine GenerateOpen.basic _ ⟨_, fun a => ?_, rfl⟩
    by_cases a ∈ i <;> simp [*]
/-
**induced_to_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：induced_to_pi {X : Type*} (f : X -> forall i, A i) : induced f Pi.topologi
calSpace = ⨅ i, induced (f · i) inferInstance
参数：f : X -> forall i, A i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `induced_iInf`：induced_iInf {ι : Sort w} {t : ι -> TopologicalSpace α} : 
(⨅ i, t i).induced g = ⨅ i, (t i).induced g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `induced_compose`：induced_compose {tγ : TopologicalSpace γ} {f : α -> β} 
{g : β -> γ} : (tγ.induced g).induced f = tγ.induced (g ∘ f)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem induced_to_pi {X : Type*} (f : X → ∀ i, A i) :
    induced f Pi.topologicalSpace = ⨅ i, induced (f · i) inferInstance := by
  simp_rw [Pi.topologicalSpace, induced_iInf, induced_compose, Function.comp_def]

/-- Suppose `A i` is a family of topological spaces indexed by `i : ι`, and `X` is a type
endowed with a family of maps `f i : X → A i` for every `i : ι`, hence inducing a
map `g : X → Π i, A i`. This lemma shows that infimum of the topologies on `X` induced by
the `f i` as `i : ι` varies is simply the topology on `X` induced by `g : X → Π i, A i`
where `Π i, A i` is endowed with the usual product topology. -/
/-
**inducing_iInf_to_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inducing_iInf_to_pi {X : Type*} (f : forall i, X -> A i) : @IsInducing X (
forall i, A i) (⨅ i, induced (f i) inferInstance) _ fun x i => f i x
参数：f : forall i, X -> A i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `induced_to_pi`：induced_to_pi {X : Type*} (f : X -> forall i, A i) : indu
ced f Pi.topologicalSpace = ⨅ i, induced (f · i) inferInstance

--- 原说明 ---
Suppose `A i` is a family of topological spaces indexed by `i : ι`, and `X` is a
 type
endowed with a family of maps `f i : X → A i` for every `i : ι`, hence inducing 
a
map `g : X → Π i, A i`. This lemma shows that infimum of the topologies on `X` i
nduced by
the `f i` as `i : ι` varies is simply the topology on `X` induced by `g : X → Π 
i, A i`
where `Π i, A i` is endowed with the usual product topology.
-/
theorem inducing_iInf_to_pi {X : Type*} (f : ∀ i, X → A i) :
    @IsInducing X (∀ i, A i) (⨅ i, induced (f i) inferInstance) _ fun x i => f i x :=
  letI := ⨅ i, induced (f i) inferInstance; ⟨(induced_to_pi _).symm⟩

variable [Finite ι] [∀ i, DiscreteTopology (A i)]

/-- A finite product of discrete spaces is discrete. -/
/-
**Pi.discreteTopology** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.discreteTopology : DiscreteTopology (forall i, A i)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `discreteTopology_iff_isOpen_singleton`：discreteTopology_iff_isOpen_singl
eton [TopologicalSpace α] : DiscreteTopology α ↔ (forall a : α, IsOpen ({a} : Se
t α))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.univ_pi_singleton`：univ_pi_singleton (f : forall i, α i) : (pi univ 
fun i => {f i}) = ({f} : Set (forall i, α i))
· 使用定理 `isOpen_set_pi`：isOpen_set_pi {i : Set ι} {s : forall a, Set (A a)} (hi :
 i.Finite) (hs : forall a in i, IsOpen (s a)) : IsOpen (pi i s)
· 使用定理 `Set.finite_univ`：∀ {α : Type u} [Finite α], Set.univ.Finite
· 使用定理 `isOpen_discrete`：isOpen_discrete (s : Set α) : IsOpen s

--- 原说明 ---
A finite product of discrete spaces is discrete.
-/
instance Pi.discreteTopology : DiscreteTopology (∀ i, A i) :=
  discreteTopology_iff_isOpen_singleton.mpr fun x => by
    rw [← univ_pi_singleton]
    exact isOpen_set_pi finite_univ fun i _ => (isOpen_discrete {x i})
/-
**Function.Surjective.isEmbedding_comp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Function.Surjective.isEmbedding_comp {n m : Type*} (f : m -> n) (hf : Func
tion.Surjective f) : IsEmbedding ((· ∘ f) : (n -> X) -> (m -> X))
参数：f : m -> n；hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Topology.isInducing_iff_nhds`：isInducing_iff_nhds : IsInducing f ↔ foral
l x, 𝓝 x = comap f (𝓝 (f x))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_pi`：nhds_pi {a : forall i, A i} : 𝓝 a = pi fun i => 𝓝 (a i)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Surjective.iInf_congr`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : So
rt u_5} [inst : InfSet α] {f : ι → α} {g : ι' → α} (h : ι → ι'),   Function.Surj
ective h → (∀ (x : ι…
· 使用定理 `Filter.comap_iInf`：comap_iInf {f : ι -> Filter β} : comap m (⨅ i, f i) =
 ⨅ i, comap m (f i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.comap_comap`：comap_comap {m : γ -> β} {n : β -> α} : comap m (com
ap n f) = comap (n ∘ m) f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.Surjective.injective_comp_right`：∀ {α : Sort u_1} {β : Sort u_2
} {γ : Sort u_3} {f : α → β}, Function.Surjective f → Function.Injective fun g =
> g ∘ f
-/
lemma Function.Surjective.isEmbedding_comp {n m : Type*} (f : m → n) (hf : Function.Surjective f) :
    IsEmbedding ((· ∘ f) : (n → X) → (m → X)) := by
  refine ⟨isInducing_iff_nhds.mpr fun x ↦ ?_, hf.injective_comp_right⟩
  simp only [nhds_pi, Filter.pi, Filter.comap_iInf, ← hf.iInf_congr, Filter.comap_comap,
    Function.comp_def]

end Pi

section Sigma

variable {ι κ : Type*} {σ : ι → Type*} {τ : κ → Type*} [∀ i, TopologicalSpace (σ i)]
  [∀ k, TopologicalSpace (τ k)] [TopologicalSpace X]

@[continuity, fun_prop]
/-
**continuous_sigmaMk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_sigmaMk {i : ι} : Continuous (@Sigma.mk ι σ i)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_iSup_rng`：continuous_iSup_rng {t₁ : TopologicalSpace α} {t₂ :
 ι -> TopologicalSpace β} {i : ι} (h : Continuous[t₁, t₂ i] f) : Continuous[t₁, 
iSup t₂] …
· 使用定理 `continuous_coinduced_rng`：continuous_coinduced_rng {t : TopologicalSpace
 α} : Continuous[t, coinduced f t] f
-/
theorem continuous_sigmaMk {i : ι} : Continuous (@Sigma.mk ι σ i) :=
  continuous_iSup_rng continuous_coinduced_rng
/-
**isOpen_sigma_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpen_sigma_iff {s : Set (Sigma σ)} : IsOpen s ↔ forall i, IsOpen (Sigma.
mk i ⁻¹' s)
参数：Sigma σ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isOpen_iSup_iff`：isOpen_iSup_iff {s : Set α} : IsOpen[⨆ i, t i] s ↔ fora
ll i, IsOpen[t i] s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isOpen_sigma_iff {s : Set (Sigma σ)} : IsOpen s ↔ ∀ i, IsOpen (Sigma.mk i ⁻¹' s) := by
  rw [isOpen_iSup_iff]
  rfl
/-
**isClosed_sigma_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_sigma_iff {s : Set (Sigma σ)} : IsClosed s ↔ forall i, IsClosed (
Sigma.mk i ⁻¹' s)
参数：Sigma σ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isClosed_sigma_iff {s : Set (Sigma σ)} : IsClosed s ↔ ∀ i, IsClosed (Sigma.mk i ⁻¹' s) := by
  simp only [← isOpen_compl_iff, isOpen_sigma_iff, preimage_compl]
/-
**isOpenMap_sigmaMk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpenMap_sigmaMk {i : ι} : IsOpenMap (@Sigma.mk ι σ i)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isOpen_sigma_iff`：isOpen_sigma_iff {s : Set (Sigma σ)} : IsOpen s ↔ fora
ll i, IsOpen (Sigma.mk i ⁻¹' s)
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用定理 `sigma_mk_injective`：∀ {α : Type u_1} {β : α → Type u_4} {i : α}, Functio
n.Injective (Sigma.mk i)
· 使用定理 `Set.preimage_image_sigmaMk_of_ne`：preimage_image_sigmaMk_of_ne (h : i !=
 j) (s : Set (α j)) : Sigma.mk i ⁻¹' Sigma.mk j '' s = ∅
· 使用定理 `isOpen_empty`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen ∅
-/
theorem isOpenMap_sigmaMk {i : ι} : IsOpenMap (@Sigma.mk ι σ i) := by
  intro s hs
  rw [isOpen_sigma_iff]
  intro j
  rcases eq_or_ne j i with (rfl | hne)
  · rwa [preimage_image_eq _ sigma_mk_injective]
  · rw [preimage_image_sigmaMk_of_ne hne]
    exact isOpen_empty
/-
**isOpen_range_sigmaMk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpen_range_sigmaMk {i : ι} : IsOpen (range (@Sigma.mk ι σ i))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenMap.isOpen_range`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsOpenMap f → IsOpen (S
et.range f)
· 使用定理 `isOpenMap_sigmaMk`：isOpenMap_sigmaMk {i : ι} : IsOpenMap (@Sigma.mk ι σ 
i)
-/
theorem isOpen_range_sigmaMk {i : ι} : IsOpen (range (@Sigma.mk ι σ i)) :=
  isOpenMap_sigmaMk.isOpen_range
/-
**isClosedMap_sigmaMk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosedMap_sigmaMk {i : ι} : IsClosedMap (@Sigma.mk ι σ i)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isClosed_sigma_iff`：isClosed_sigma_iff {s : Set (Sigma σ)} : IsClosed s 
↔ forall i, IsClosed (Sigma.mk i ⁻¹' s)
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用定理 `sigma_mk_injective`：∀ {α : Type u_1} {β : α → Type u_4} {i : α}, Functio
n.Injective (Sigma.mk i)
· 使用定理 `Set.preimage_image_sigmaMk_of_ne`：preimage_image_sigmaMk_of_ne (h : i !=
 j) (s : Set (α j)) : Sigma.mk i ⁻¹' Sigma.mk j '' s = ∅
· 使用定理 `isClosed_empty`：isClosed_empty : IsClosed (∅ : Set X)
-/
theorem isClosedMap_sigmaMk {i : ι} : IsClosedMap (@Sigma.mk ι σ i) := by
  intro s hs
  rw [isClosed_sigma_iff]
  intro j
  rcases eq_or_ne j i with (rfl | hne)
  · rwa [preimage_image_eq _ sigma_mk_injective]
  · rw [preimage_image_sigmaMk_of_ne hne]
    exact isClosed_empty
/-
**isClosed_range_sigmaMk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_range_sigmaMk {i : ι} : IsClosed (range (@Sigma.mk ι σ i))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosedMap.isClosed_range`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} 
[inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsClosedMap f → IsC
losed (Set.range…
· 使用定理 `isClosedMap_sigmaMk`：isClosedMap_sigmaMk {i : ι} : IsClosedMap (@Sigma.m
k ι σ i)
-/
theorem isClosed_range_sigmaMk {i : ι} : IsClosed (range (@Sigma.mk ι σ i)) :=
  isClosedMap_sigmaMk.isClosed_range
/-
**Topology.IsOpenEmbedding.sigmaMk** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsOpenEmbedding.sigmaMk {i : ι} : IsOpenEmbedding (@Sigma.mk ι σ 
i)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap`：∀ {X : Type 
u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : Topologica
lSpace Y],   Continuous f → Function.Injective f…
· 使用定理 `continuous_sigmaMk`：continuous_sigmaMk {i : ι} : Continuous (@Sigma.mk ι
 σ i)
· 使用定理 `sigma_mk_injective`：∀ {α : Type u_1} {β : α → Type u_4} {i : α}, Functio
n.Injective (Sigma.mk i)
· 使用定理 `isOpenMap_sigmaMk`：isOpenMap_sigmaMk {i : ι} : IsOpenMap (@Sigma.mk ι σ 
i)
-/
lemma Topology.IsOpenEmbedding.sigmaMk {i : ι} : IsOpenEmbedding (@Sigma.mk ι σ i) :=
  .of_continuous_injective_isOpenMap continuous_sigmaMk sigma_mk_injective isOpenMap_sigmaMk
/-
**Topology.IsClosedEmbedding.sigmaMk** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsClosedEmbedding.sigmaMk {i : ι} : IsClosedEmbedding (@Sigma.mk 
ι σ i)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap`：∀ {X : T
ype u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : Topolo
gicalSpace Y],   Continuous f → Function.Injective f…
· 使用定理 `continuous_sigmaMk`：continuous_sigmaMk {i : ι} : Continuous (@Sigma.mk ι
 σ i)
· 使用定理 `sigma_mk_injective`：∀ {α : Type u_1} {β : α → Type u_4} {i : α}, Functio
n.Injective (Sigma.mk i)
· 使用定理 `isClosedMap_sigmaMk`：isClosedMap_sigmaMk {i : ι} : IsClosedMap (@Sigma.m
k ι σ i)
-/
lemma Topology.IsClosedEmbedding.sigmaMk {i : ι} : IsClosedEmbedding (@Sigma.mk ι σ i) :=
  .of_continuous_injective_isClosedMap continuous_sigmaMk sigma_mk_injective isClosedMap_sigmaMk
/-
**Topology.IsEmbedding.sigmaMk** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsEmbedding.sigmaMk {i : ι} : IsEmbedding (@Sigma.mk ι σ i)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsClosedEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2
} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.Is
ClosedEmbedding f → Topology.I…
· 使用引理 `Topology.IsClosedEmbedding.sigmaMk`：Topology.IsClosedEmbedding.sigmaMk {
i : ι} : IsClosedEmbedding (@Sigma.mk ι σ i)
-/
lemma Topology.IsEmbedding.sigmaMk {i : ι} : IsEmbedding (@Sigma.mk ι σ i) :=
  IsClosedEmbedding.sigmaMk.1
/-
**Sigma.nhds_mk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Sigma.nhds_mk (i : ι) (x : σ i) : 𝓝 (⟨i, x⟩ : Sigma σ) = Filter.map (Sigma
.mk i) (𝓝 x)
参数：i : ι；x : σ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsOpenEmbedding.map_nhds_eq`：∀ {X : Type u_1} {Y : Type u_2} {f
 : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.
IsOpenEmbedding f → ∀ (x :…
· 使用引理 `Topology.IsOpenEmbedding.sigmaMk`：Topology.IsOpenEmbedding.sigmaMk {i : 
ι} : IsOpenEmbedding (@Sigma.mk ι σ i)
-/
theorem Sigma.nhds_mk (i : ι) (x : σ i) : 𝓝 (⟨i, x⟩ : Sigma σ) = Filter.map (Sigma.mk i) (𝓝 x) :=
  (IsOpenEmbedding.sigmaMk.map_nhds_eq x).symm
/-
**Sigma.nhds_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Sigma.nhds_eq (x : Sigma σ) : 𝓝 x = Filter.map (Sigma.mk x.1) (𝓝 x.2)
参数：x : Sigma σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sigma.nhds_mk`：Sigma.nhds_mk (i : ι) (x : σ i) : 𝓝 (⟨i, x⟩ : Sigma σ) = 
Filter.map (Sigma.mk i) (𝓝 x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Sigma.nhds_eq (x : Sigma σ) : 𝓝 x = Filter.map (Sigma.mk x.1) (𝓝 x.2) := by
  cases x
  apply Sigma.nhds_mk
/-
**comap_sigmaMk_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：comap_sigmaMk_nhds (i : ι) (x : σ i) : comap (Sigma.mk i) (𝓝 ⟨i, x⟩) = 𝓝 x
参数：i : ι；x : σ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Topology.IsInducing.nhds_eq_comap`：nhds_eq_comap (hf : IsInducing f) : f
orall x : X, 𝓝 x = comap f (𝓝 <| f x)
· 使用定理 `Topology.IsEmbedding.toIsInducing`：∀ {X : Type u_1} {Y : Type u_2} [tX :
 TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbeddi
ng f → Topology.IsInduc…
· 使用引理 `Topology.IsEmbedding.sigmaMk`：Topology.IsEmbedding.sigmaMk {i : ι} : IsE
mbedding (@Sigma.mk ι σ i)
-/
theorem comap_sigmaMk_nhds (i : ι) (x : σ i) : comap (Sigma.mk i) (𝓝 ⟨i, x⟩) = 𝓝 x :=
  (IsEmbedding.sigmaMk.nhds_eq_comap _).symm
/-
**isOpen_sigma_fst_preimage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpen_sigma_fst_preimage (s : Set ι) : IsOpen (Sigma.fst ⁻¹' s : Set (Σ a
, σ a))
参数：s : Set ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.biUnion_of_singleton`：biUnion_of_singleton (s : Set α) : ⋃ x in s, {
x} = s
· 使用定理 `Set.preimage_iUnion₂`：preimage_iUnion₂ {f : α -> β} {s : forall i, κ i -
> Set β} : (f ⁻¹' ⋃ (i) (j), s i j) = ⋃ (i) (j), f ⁻¹' s i j
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `isOpen_biUnion`：isOpen_biUnion {s : Set α} {f : α -> Set X} (h : forall 
i in s, IsOpen (f i)) : IsOpen (⋃ i in s, f i)
· 使用定理 `isOpen_range_sigmaMk`：isOpen_range_sigmaMk {i : ι} : IsOpen (range (@Sig
ma.mk ι σ i))
-/
theorem isOpen_sigma_fst_preimage (s : Set ι) : IsOpen (Sigma.fst ⁻¹' s : Set (Σ a, σ a)) := by
  rw [← biUnion_of_singleton s, preimage_iUnion₂]
  simp only [← range_sigmaMk]
  exact isOpen_biUnion fun _ _ => isOpen_range_sigmaMk

/-- A map out of a sum type is continuous iff its restriction to each summand is. -/
@[simp]
/-
**continuous_sigma_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_sigma_iff {f : Sigma σ -> X} : Continuous f ↔ forall i, Continu
ous fun a => f ⟨i, a⟩
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuous_iSup_dom`：continuous_iSup_dom {t₁ : ι -> TopologicalSpace α} 
{t₂ : TopologicalSpace β} : Continuous[iSup t₁, t₂] f ↔ forall i, Continuous[t₁ 
i, t₂] f
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `continuous_coinduced_dom`：continuous_coinduced_dom {g : β -> γ} {t₁ : To
pologicalSpace α} {t₂ : TopologicalSpace γ} : Continuous[coinduced f t₁, t₂] g ↔
 Continuous[t₁…

--- 原说明 ---
A map out of a sum type is continuous iff its restriction to each summand is.
-/
theorem continuous_sigma_iff {f : Sigma σ → X} :
    Continuous f ↔ ∀ i, Continuous fun a => f ⟨i, a⟩ := by
  delta instTopologicalSpaceSigma
  rw [continuous_iSup_dom]
  exact forall_congr' fun _ => continuous_coinduced_dom

-- NB. This is a bad `fun_prop` theorem: because of its hypotheses, this would be classified as a
-- transition theorem, and most likely never fire.
/-- A map out of a sum type is continuous if its restriction to each summand is. -/
@[continuity]
/-
**continuous_sigma** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_sigma {f : Sigma σ -> X} (hf : forall i, Continuous fun a => f 
⟨i, a⟩) : Continuous f
参数：hf : forall i, Continuous fun a => f ⟨i, a⟩。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_sigma_iff`：continuous_sigma_iff {f : Sigma σ -> X} : Continuo
us f ↔ forall i, Continuous fun a => f ⟨i, a⟩

--- 原说明 ---
A map out of a sum type is continuous if its restriction to each summand is.
-/
theorem continuous_sigma {f : Sigma σ → X} (hf : ∀ i, Continuous fun a => f ⟨i, a⟩) :
    Continuous f :=
  continuous_sigma_iff.2 hf

/-- A map defined on a sigma type (a.k.a. the disjoint union of an indexed family of topological
spaces) is inducing iff its restriction to each component is inducing and each the image of each
component under `f` can be separated from the images of all other components by an open set. -/
/-
**inducing_sigma** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inducing_sigma {f : Sigma σ -> X} : IsInducing f ↔ (forall i, IsInducing (
f ∘ Sigma.mk i)) ∧ (forall i, exists U, IsOpen U ∧ forall x, f x in U ↔ x.1 = i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3}
 {f : X → Y} {g : Y → Z} [inst : TopologicalSpace Y]   [inst_1 : TopologicalSpac
e X] [inst_2 :…
· 使用定理 `Topology.IsEmbedding.toIsInducing`：∀ {X : Type u_1} {Y : Type u_2} [tX :
 TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbeddi
ng f → Topology.IsInduc…
· 使用引理 `Topology.IsEmbedding.sigmaMk`：Topology.IsEmbedding.sigmaMk {i : ι} : IsE
mbedding (@Sigma.mk ι σ i)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Topology.IsInducing.isOpen_iff`：isOpen_iff (hf : IsInducing f) {s : Set 
X} : IsOpen s ↔ exists t, IsOpen t ∧ f ⁻¹' t = s
· 使用定理 `isOpen_range_sigmaMk`：isOpen_range_sigmaMk {i : ι} : IsOpen (range (@Sig
ma.mk ι σ i))
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_sigmaMk`：range_sigmaMk (i : ι) : range (Sigma.mk i : α i -> Si
gma α) = Sigma.fst ⁻¹' {i}
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Topology.isInducing_iff_nhds`：isInducing_iff_nhds : IsInducing f ↔ foral
l x, 𝓝 x = comap f (𝓝 (f x))
· 使用定理 `Sigma.nhds_mk`：Sigma.nhds_mk (i : ι) (x : σ i) : 𝓝 (⟨i, x⟩ : Sigma σ) = 
Filter.map (Sigma.mk i) (𝓝 x)
· 使用引理 `Topology.IsInducing.nhds_eq_comap`：nhds_eq_comap (hf : IsInducing f) : f
orall x : X, 𝓝 x = comap f (𝓝 <| f x)
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.comap_comap`：comap_comap {m : γ -> β} {n : β -> α} : comap m (com
ap n f) = comap (n ∘ m) f
· 使用定理 `Filter.map_comap_of_mem`：map_comap_of_mem {f : Filter β} {m : α -> β} (h
f : range m in f) : (f.comap m).map m = f
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.preimage_mem_comap`：preimage_mem_comap (ht : t in g) : m ⁻¹' t in
 comap m g
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a

--- 原说明 ---
A map defined on a sigma type (a.k.a. the disjoint union of an indexed family of
 topological
spaces) is inducing iff its restriction to each component is inducing and each t
he image of each
component under `f` can be separated from the images of all other components by 
an open set.
-/
theorem inducing_sigma {f : Sigma σ → X} :
    IsInducing f ↔ (∀ i, IsInducing (f ∘ Sigma.mk i)) ∧
      (∀ i, ∃ U, IsOpen U ∧ ∀ x, f x ∈ U ↔ x.1 = i) := by
  refine ⟨fun h ↦ ⟨fun i ↦ h.comp IsEmbedding.sigmaMk.1, fun i ↦ ?_⟩, ?_⟩
  · rcases h.isOpen_iff.1 (isOpen_range_sigmaMk (i := i)) with ⟨U, hUo, hU⟩
    refine ⟨U, hUo, ?_⟩
    simpa [Set.ext_iff] using hU
  · refine fun ⟨h₁, h₂⟩ ↦ isInducing_iff_nhds.2 fun ⟨i, x⟩ ↦ ?_
    rw [Sigma.nhds_mk, (h₁ i).nhds_eq_comap, comp_apply, ← comap_comap, map_comap_of_mem]
    rcases h₂ i with ⟨U, hUo, hU⟩
    filter_upwards [preimage_mem_comap <| hUo.mem_nhds <| (hU _).2 rfl] with y hy
    simpa [hU] using hy

@[simp 1100]
/-
**continuous_sigma_map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_sigma_map {f₁ : ι -> κ} {f₂ : forall i, σ i -> τ (f₁ i)} : Cont
inuous (Sigma.map f₁ f₂) ↔ forall i, Continuous (f₂ i)
参数：f₁ i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `continuous_sigma_iff`：continuous_sigma_iff {f : Sigma σ -> X} : Continuo
us f ↔ forall i, Continuous fun a => f ⟨i, a⟩
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Topology.IsEmbedding.continuous_iff`：∀ {X : Type u_1} {Y : Type u_2} {Z 
: Type u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : Topo
logicalSpace Y] [inst_2 :…
· 使用引理 `Topology.IsEmbedding.sigmaMk`：Topology.IsEmbedding.sigmaMk {i : ι} : IsE
mbedding (@Sigma.mk ι σ i)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem continuous_sigma_map {f₁ : ι → κ} {f₂ : ∀ i, σ i → τ (f₁ i)} :
    Continuous (Sigma.map f₁ f₂) ↔ ∀ i, Continuous (f₂ i) :=
  continuous_sigma_iff.trans <| by
    simp only [Sigma.map, IsEmbedding.sigmaMk.continuous_iff, comp_def]

@[continuity, fun_prop]
/-
**Continuous.sigma_map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.sigma_map {f₁ : ι -> κ} {f₂ : forall i, σ i -> τ (f₁ i)} (hf : 
forall i, Continuous (f₂ i)) : Continuous (Sigma.map f₁ f₂)
参数：f₁ i；hf : forall i, Continuous (f₂ i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_sigma_map`：continuous_sigma_map {f₁ : ι -> κ} {f₂ : forall i,
 σ i -> τ (f₁ i)} : Continuous (Sigma.map f₁ f₂) ↔ forall i, Continuous (f₂ i)
-/
theorem Continuous.sigma_map {f₁ : ι → κ} {f₂ : ∀ i, σ i → τ (f₁ i)} (hf : ∀ i, Continuous (f₂ i)) :
    Continuous (Sigma.map f₁ f₂) :=
  continuous_sigma_map.2 hf
/-
**isOpenMap_sigma** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpenMap_sigma {f : Sigma σ -> X} : IsOpenMap f ↔ forall i, IsOpenMap fun
 a => f ⟨i, a⟩
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Sigma.nhds_eq`：Sigma.nhds_eq (x : Sigma σ) : 𝓝 x = Filter.map (Sigma.mk 
x.1) (𝓝 x.2)
· 使用定理 `Filter.map_map`：map_map : Filter.map m' (Filter.map m f) = Filter.map (m
' ∘ m) f
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isOpenMap_sigma {f : Sigma σ → X} : IsOpenMap f ↔ ∀ i, IsOpenMap fun a => f ⟨i, a⟩ := by
  simp only [isOpenMap_iff_nhds_le, Sigma.forall, Sigma.nhds_eq, map_map, comp_def]
/-
**isOpenMap_sigma_map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpenMap_sigma_map {f₁ : ι -> κ} {f₂ : forall i, σ i -> τ (f₁ i)} : IsOpe
nMap (Sigma.map f₁ f₂) ↔ forall i, IsOpenMap (f₂ i)
参数：f₁ i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `isOpenMap_sigma`：isOpenMap_sigma {f : Sigma σ -> X} : IsOpenMap f ↔ fora
ll i, IsOpenMap fun a => f ⟨i, a⟩
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Topology.IsOpenEmbedding.isOpenMap_iff`：∀ {X : Type u_1} {Y : Type u_2} 
{Z : Type u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : T
opologicalSpace Y] [inst_2 :…
· 使用引理 `Topology.IsOpenEmbedding.sigmaMk`：Topology.IsOpenEmbedding.sigmaMk {i : 
ι} : IsOpenEmbedding (@Sigma.mk ι σ i)
-/
theorem isOpenMap_sigma_map {f₁ : ι → κ} {f₂ : ∀ i, σ i → τ (f₁ i)} :
    IsOpenMap (Sigma.map f₁ f₂) ↔ ∀ i, IsOpenMap (f₂ i) :=
  isOpenMap_sigma.trans <|
    forall_congr' fun i => (@IsOpenEmbedding.sigmaMk _ _ _ (f₁ i)).isOpenMap_iff.symm
/-
**Topology.isInducing_sigmaMap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.isInducing_sigmaMap {f₁ : ι -> κ} {f₂ : forall i, σ i -> τ (f₁ i)
} (h₁ : Injective f₁) : IsInducing (Sigma.map f₁ f₂) ↔ forall i, IsInducing (f₂ 
i)
参数：f₁ i；h₁ : Injective f₁。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Sigma.nhds_mk`：Sigma.nhds_mk (i : ι) (x : σ i) : 𝓝 (⟨i, x⟩ : Sigma σ) = 
Filter.map (Sigma.mk i) (𝓝 x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.map_sigma_mk_comap`：map_sigma_mk_comap {π : α -> Type*} {π' : β -
> Type*} {f : α -> β} (hf : Function.Injective f) (g : forall a, π a -> π' (f a)
) (a : α) (l : …
· 使用定理 `Filter.map_inj`：map_inj {f g : Filter α} {m : α -> β} (hm : Injective m)
 : map m f = map m g ↔ f = g
· 使用定理 `sigma_mk_injective`：∀ {α : Type u_1} {β : α → Type u_4} {i : α}, Functio
n.Injective (Sigma.mk i)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Topology.isInducing_sigmaMap {f₁ : ι → κ} {f₂ : ∀ i, σ i → τ (f₁ i)}
    (h₁ : Injective f₁) : IsInducing (Sigma.map f₁ f₂) ↔ ∀ i, IsInducing (f₂ i) := by
  simp only [isInducing_iff_nhds, Sigma.forall, Sigma.nhds_mk, Sigma.map_mk,
    ← map_sigma_mk_comap h₁, map_inj sigma_mk_injective]
/-
**Topology.isEmbedding_sigmaMap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.isEmbedding_sigmaMap {f₁ : ι -> κ} {f₂ : forall i, σ i -> τ (f₁ i
)} (h : Injective f₁) : IsEmbedding (Sigma.map f₁ f₂) ↔ forall i, IsEmbedding (f
₂ i)
参数：f₁ i；h : Injective f₁。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Topology.isInducing_sigmaMap`：Topology.isInducing_sigmaMap {f₁ : ι -> κ}
 {f₂ : forall i, σ i -> τ (f₁ i)} (h₁ : Injective f₁) : IsInducing (Sigma.map f₁
 f₂) ↔ forall i, I…
· 使用定理 `Function.Injective.sigma_map_iff`：Function.Injective.sigma_map_iff {f₁ :
 α₁ -> α₂} {f₂ : forall a, β₁ a -> β₂ (f₁ a)} (h₁ : Injective f₁) : Injective (S
igma.map f₁ f₂) ↔ fora…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Topology.isEmbedding_sigmaMap {f₁ : ι → κ} {f₂ : ∀ i, σ i → τ (f₁ i)}
    (h : Injective f₁) : IsEmbedding (Sigma.map f₁ f₂) ↔ ∀ i, IsEmbedding (f₂ i) := by
  simp only [isEmbedding_iff, isInducing_sigmaMap h, forall_and,
    h.sigma_map_iff]
/-
**Topology.isOpenEmbedding_sigmaMap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.isOpenEmbedding_sigmaMap {f₁ : ι -> κ} {f₂ : forall i, σ i -> τ (
f₁ i)} (h : Injective f₁) : IsOpenEmbedding (Sigma.map f₁ f₂) ↔ forall i, IsOpen
Embedding (f₂ i)
参数：f₁ i；h : Injective f₁。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Topology.isEmbedding_sigmaMap`：Topology.isEmbedding_sigmaMap {f₁ : ι -> 
κ} {f₂ : forall i, σ i -> τ (f₁ i)} (h : Injective f₁) : IsEmbedding (Sigma.map 
f₁ f₂) ↔ forall i, …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Topology.isOpenEmbedding_sigmaMap {f₁ : ι → κ} {f₂ : ∀ i, σ i → τ (f₁ i)} (h : Injective f₁) :
    IsOpenEmbedding (Sigma.map f₁ f₂) ↔ ∀ i, IsOpenEmbedding (f₂ i) := by
  simp only [isOpenEmbedding_iff_isEmbedding_isOpenMap, isOpenMap_sigma_map, isEmbedding_sigmaMap h,
    forall_and]

end Sigma

section ULift

set_option backward.isDefEq.respectTransparency false in
/-
**ULift.isOpen_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ULift.isOpen_iff [TopologicalSpace X] {s : Set (ULift.{v} X)} : IsOpen s ↔
 IsOpen (ULift.up ⁻¹' s)
参数：ULift.{v} X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ULift.topologicalSpace.eq_1`：∀ {X : Type u} [t : TopologicalSpace X], UL
ift.topologicalSpace = TopologicalSpace.induced ULift.down t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.ulift_apply`：∀ {α : Type v}, ⇑Equiv.ulift = ULift.down
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.coinduced_symm`：Equiv.coinduced_symm {α β : Type*} (e : α ≃ β) : T
opologicalSpace.coinduced e.symm = TopologicalSpace.induced e
· 使用定理 `isOpen_coinduced`：isOpen_coinduced {t : TopologicalSpace α} {s : Set β} 
{f : α -> β} : IsOpen[t.coinduced f] s ↔ IsOpen (f ⁻¹' s)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ULift.isOpen_iff [TopologicalSpace X] {s : Set (ULift.{v} X)} :
    IsOpen s ↔ IsOpen (ULift.up ⁻¹' s) := by
  rw [ULift.topologicalSpace, ← Equiv.ulift_apply, ← Equiv.ulift.coinduced_symm, ← isOpen_coinduced]
/-
**ULift.isClosed_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ULift.isClosed_iff [TopologicalSpace X] {s : Set (ULift.{v} X)} : IsClosed
 s ↔ IsClosed (ULift.up ⁻¹' s)
参数：ULift.{v} X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isOpen_compl_iff`：∀ {X : Type u} {s : Set X} [inst : TopologicalSpace X]
, IsOpen sᶜ ↔ IsClosed s
· 使用定理 `ULift.isOpen_iff`：ULift.isOpen_iff [TopologicalSpace X] {s : Set (ULift.
{v} X)} : IsOpen s ↔ IsOpen (ULift.up ⁻¹' s)
· 使用定理 `Set.preimage_compl`：preimage_compl {s : Set β} : f ⁻¹' sᶜ = (f ⁻¹' s)ᶜ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ULift.isClosed_iff [TopologicalSpace X] {s : Set (ULift.{v} X)} :
    IsClosed s ↔ IsClosed (ULift.up ⁻¹' s) := by
  rw [← isOpen_compl_iff, ← isOpen_compl_iff, isOpen_iff, preimage_compl]

@[continuity, fun_prop]
/-
**continuous_uliftDown** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_uliftDown [TopologicalSpace X] : Continuous (ULift.down : ULift
.{v, u} X -> X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_induced_dom`：continuous_induced_dom {t : TopologicalSpace β} 
: Continuous[induced f t, t] f
-/
theorem continuous_uliftDown [TopologicalSpace X] : Continuous (ULift.down : ULift.{v, u} X → X) :=
  continuous_induced_dom

@[continuity, fun_prop]
/-
**continuous_uliftUp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_uliftUp [TopologicalSpace X] : Continuous (ULift.up : X -> ULif
t.{v, u} X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_induced_rng`：continuous_induced_rng {g : γ -> α} {t₂ : Topolo
gicalSpace β} {t₁ : TopologicalSpace γ} : Continuous[t₁, induced f t₂] g ↔ Conti
nuous[t₁, t₂…
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
theorem continuous_uliftUp [TopologicalSpace X] : Continuous (ULift.up : X → ULift.{v, u} X) :=
  continuous_induced_rng.2 continuous_id

@[continuity, fun_prop]
/-
**continuous_uliftMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_uliftMap [TopologicalSpace X] [TopologicalSpace Y] (f : X -> Y)
 (hf : Continuous f) : Continuous (ULift.map f : ULift.{u'} X -> ULift.{v'} Y)
参数：f : X -> Y；hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `continuous_uliftUp`：continuous_uliftUp [TopologicalSpace X] : Continuous
 (ULift.up : X -> ULift.{v, u} X)
· 使用定理 `continuous_uliftDown`：continuous_uliftDown [TopologicalSpace X] : Contin
uous (ULift.down : ULift.{v, u} X -> X)
-/
theorem continuous_uliftMap [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f) :
    Continuous (ULift.map f : ULift.{u'} X → ULift.{v'} Y) := by
  change Continuous (ULift.up ∘ f ∘ ULift.down)
  fun_prop

@[fun_prop]
/-
**Topology.IsEmbedding.uliftDown** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsEmbedding.uliftDown [TopologicalSpace X] : IsEmbedding (ULift.d
own : ULift.{v, u} X -> X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ULift.down_injective`：∀ {α : Type u_1}, Function.Injective ULift.down
-/
lemma Topology.IsEmbedding.uliftDown [TopologicalSpace X] :
    IsEmbedding (ULift.down : ULift.{v, u} X → X) := ⟨⟨rfl⟩, ULift.down_injective⟩

@[fun_prop]
/-
**Topology.IsClosedEmbedding.uliftDown** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsClosedEmbedding.uliftDown [TopologicalSpace X] : IsClosedEmbedd
ing (ULift.down : ULift.{v, u} X -> X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsEmbedding.uliftDown`：Topology.IsEmbedding.uliftDown [Topologi
calSpace X] : IsEmbedding (ULift.down : ULift.{v, u} X -> X)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Surjective.range_eq`：∀ {α : Type u_1} {ι : Sort u_4} {f : ι → α
}, Function.Surjective f → Set.range f = Set.univ
· 使用定理 `ULift.down_surjective`：down_surjective : Surjective (@down α)
-/
lemma Topology.IsClosedEmbedding.uliftDown [TopologicalSpace X] :
    IsClosedEmbedding (ULift.down : ULift.{v, u} X → X) :=
  ⟨.uliftDown, by simp only [ULift.down_surjective.range_eq, isClosed_univ]⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [TopologicalSpace X] [DiscreteTopology X] : DiscreteTopology (ULift X) :=
  IsEmbedding.uliftDown.discreteTopology

/-- Continuous maps between `ULift X` and `ULift Y` are equivalent to continuous maps between `X`
and `Y`. -/
@[simps]
/-
**ContinuousMap.uliftEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ContinuousMap.uliftEquiv (X : Type u) (Y : Type v) [TopologicalSpace X] [T
opologicalSpace Y] : C(ULift.{v} X, ULift.{u} Y) ≃ C(X, Y) where toFun f
参数：X : Type u；Y : Type v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Continuous maps between `ULift X` and `ULift Y` are equivalent to continuous map
s between `X`
and `Y`.
-/
def ContinuousMap.uliftEquiv (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y] :
    C(ULift.{v} X, ULift.{u} Y) ≃ C(X, Y) where
  toFun f := ⟨ULift.down ∘ f ∘ ULift.up, by fun_prop⟩
  invFun f := ⟨ULift.up ∘ f ∘ ULift.down, by fun_prop⟩

end ULift

section Monad

variable [TopologicalSpace X] {s : Set X} {t : Set s}

/-
**IsOpen.trans** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.trans (ht : IsOpen t) (hs : IsOpen s) : IsOpen (t : Set X)
参数：ht : IsOpen t；hs : IsOpen s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isOpen_induced_iff`：isOpen_induced_iff [t : TopologicalSpace β] {s : Set
 α} {f : α -> β} : IsOpen[t.induced f] s ↔ exists t, IsOpen t ∧ f ⁻¹' t = s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.image_preimage_coe`：image_preimage_coe (s t : Set α) : ((↑) : s 
-> α) '' ((↑) : s -> α) ⁻¹' t = s inter t
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
-/
theorem IsOpen.trans (ht : IsOpen t) (hs : IsOpen s) : IsOpen (t : Set X) := by
  rcases isOpen_induced_iff.mp ht with ⟨s', hs', rfl⟩
  rw [Subtype.image_preimage_coe]
  exact hs.inter hs'
/-
**IsClosed.trans** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.trans (ht : IsClosed t) (hs : IsClosed s) : IsClosed (t : Set X)
参数：ht : IsClosed t；hs : IsClosed s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isClosed_induced_iff`：isClosed_induced_iff [t : TopologicalSpace β] {s :
 Set α} {f : α -> β} : IsClosed[t.induced f] s ↔ exists t, IsClosed t ∧ f ⁻¹' t 
= s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.image_preimage_coe`：image_preimage_coe (s t : Set α) : ((↑) : s 
-> α) '' ((↑) : s -> α) ⁻¹' t = s inter t
· 使用定理 `IsClosed.inter`：IsClosed.inter (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) : I
sClosed (s₁ inter s₂)
-/
theorem IsClosed.trans (ht : IsClosed t) (hs : IsClosed s) : IsClosed (t : Set X) := by
  rcases isClosed_induced_iff.mp ht with ⟨s', hs', rfl⟩
  rw [Subtype.image_preimage_coe]
  exact hs.inter hs'

end Monad

section NhdsSet
variable [TopologicalSpace X] [TopologicalSpace Y]
  {s : Set X} {t : Set Y}

/-- The product of a neighborhood of `s` and a neighborhood of `t` is a neighborhood of `s ×ˢ t`,
formulated in terms of a filter inequality. -/
/-
**nhdsSet_prod_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsSet_prod_le (s : Set X) (t : Set Y) : 𝓝ˢ (s ×ˢ t) <= 𝓝ˢ s ×ˢ 𝓝ˢ t
参数：s : Set X；t : Set Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.ge_iff`：∀ {α : Type u_1} {ι' : Sort u_5} {l l' : Filter 
α} {p' : ι' → Prop} {s' : ι' → Set α},   l'.HasBasis p' s' → (l ≤ l' ↔ ∀ (i' : ι
'), p' i' → …
· 使用定理 `Filter.HasBasis.prod`：∀ {α : Type u_1} {β : Type u_2} {la : Filter α} {l
b : Filter β} {ι : Type u_6} {ι' : Type u_7} {pa : ι → Prop}   {sa : ι → Set α} 
{pb : ι' →…
· 使用定理 `hasBasis_nhdsSet`：hasBasis_nhdsSet (s : Set X) : (𝓝ˢ s).HasBasis (fun U 
=> IsOpen U ∧ s subseteq U) fun U => U
· 使用定理 `IsOpen.mem_nhdsSet`：IsOpen.mem_nhdsSet (hU : IsOpen s) : s in 𝓝ˢ t ↔ t s
ubseteq s
· 使用定理 `IsOpen.prod`：IsOpen.prod {s : Set X} {t : Set Y} (hs : IsOpen s) (ht : I
sOpen t) : IsOpen (s ×ˢ t)
· 使用定理 `Set.prod_mono`：prod_mono (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂) : s
₁ ×ˢ t₁ subseteq s₂ ×ˢ t₂

--- 原说明 ---
The product of a neighborhood of `s` and a neighborhood of `t` is a neighborhood
 of `s ×ˢ t`,
formulated in terms of a filter inequality.
-/
theorem nhdsSet_prod_le (s : Set X) (t : Set Y) : 𝓝ˢ (s ×ˢ t) ≤ 𝓝ˢ s ×ˢ 𝓝ˢ t :=
  ((hasBasis_nhdsSet _).prod (hasBasis_nhdsSet _)).ge_iff.2 fun (_u, _v) ⟨⟨huo, hsu⟩, hvo, htv⟩ ↦
    (huo.prod hvo).mem_nhdsSet.2 <| prod_mono hsu htv
/-
**Filter.eventually_nhdsSet_prod_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.eventually_nhdsSet_prod_iff {p : X × Y -> Prop} : (forallᶠ q in 𝓝ˢ 
(s ×ˢ t), p q) ↔ forall x in s, forall y in t, exists px : X -> Prop, (forallᶠ x
' in 𝓝 x, px x') ∧ exists py : Y -> Prop, (forallᶠ y' in 𝓝 y, py y') ∧ forall {x
 : X}, px x -> forall {y : Y}, py y -> p (x, y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Filter.eventually_nhdsSet_prod_iff {p : X × Y → Prop} :
    (∀ᶠ q in 𝓝ˢ (s ×ˢ t), p q) ↔
      ∀ x ∈ s, ∀ y ∈ t,
          ∃ px : X → Prop, (∀ᶠ x' in 𝓝 x, px x') ∧ ∃ py : Y → Prop, (∀ᶠ y' in 𝓝 y, py y') ∧
            ∀ {x : X}, px x → ∀ {y : Y}, py y → p (x, y) := by
  simp_rw [eventually_nhdsSet_iff_forall, forall_prod_set, nhds_prod_eq, eventually_prod_iff]
/-
**Filter.Eventually.prod_nhdsSet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Eventually.prod_nhdsSet {p : X × Y -> Prop} {px : X -> Prop} {py : 
Y -> Prop} (hp : forall {x : X}, px x -> forall {y : Y}, py y -> p (x, y)) (hs :
 forallᶠ x in 𝓝ˢ s, px x) (ht : forallᶠ y in 𝓝ˢ t, py y) : forallᶠ q in 𝓝ˢ (s ×ˢ
 t), p q
参数：hp : forall {x : X}, px x -> forall {y : Y}, py y -> p (x, y)；hs : forallᶠ x 
in 𝓝ˢ s, px x；ht : forallᶠ y in 𝓝ˢ t, py y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhdsSet_prod_le`：nhdsSet_prod_le (s : Set X) (t : Set Y) : 𝓝ˢ (s ×ˢ t) <
= 𝓝ˢ s ×ˢ 𝓝ˢ t
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Filter.prod_mem_prod`：prod_mem_prod (hs : s in f) (ht : t in g) : s ×ˢ t
 in f ×ˢ g
-/
theorem Filter.Eventually.prod_nhdsSet {p : X × Y → Prop} {px : X → Prop} {py : Y → Prop}
    (hp : ∀ {x : X}, px x → ∀ {y : Y}, py y → p (x, y)) (hs : ∀ᶠ x in 𝓝ˢ s, px x)
    (ht : ∀ᶠ y in 𝓝ˢ t, py y) : ∀ᶠ q in 𝓝ˢ (s ×ˢ t), p q :=
  nhdsSet_prod_le _ _ (mem_of_superset (prod_mem_prod hs ht) fun _ ⟨hx, hy⟩ ↦ hp hx hy)

end NhdsSet

