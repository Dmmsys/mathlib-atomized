/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Data.Real.ENatENNReal
public import Mathlib.Topology.Instances.ENat
public import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Algebra.Order.Floor.Extended

/-!
# Topology lemma for `ENat.toENNReal`

This file shows `ENat.toENNReal` is a closed embedding.
-/

public section

namespace ENat

@[continuity]
/-
**ENat.continuous_toENNReal** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：continuous_toENNReal : Continuous toENNReal
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `OrderTopology.continuous_iff`：∀ {α : Type u} {β : Type v} [ts : Topologi
calSpace α] [inst : Preorder α] [OrderTopology α]   [inst_2 : TopologicalSpace β
] {f : β → α},   C…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENat.preimage_toENNReal_Ioi`：∀ (a : ENNReal), ENat.toENNReal ⁻¹' Set.Ioi
 a = Set.Ioi ⌊a⌋ₑ
· 使用定理 `isOpen_Ioi`：isOpen_Ioi : IsOpen (Ioi a)
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENat.instOrderTopology`：OrderTopology ℕ∞
· 使用定理 `ENat.preimage_toENNReal_Iio`：∀ (a : ENNReal), ENat.toENNReal ⁻¹' Set.Iio
 a = Set.Iio ⌈a⌉ₑ
· 使用定理 `isOpen_Iio`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : LinearO
rder α] [ClosedIciTopology α] {a : α}, IsOpen (Set.Iio a)
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
-/
theorem continuous_toENNReal : Continuous toENNReal := by
  refine OrderTopology.continuous_iff.mpr fun a ↦ ⟨?_, ?_⟩
  · simpa using isOpen_Ioi
  · simpa using isOpen_Iio
/-
**ENat.isClosedEmbedding_toENNReal** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：isClosedEmbedding_toENNReal : Topology.IsClosedEmbedding toENNReal
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.isClosedEmbedding`：Continuous.isClosedEmbedding [CompactSpace
 X] [T2Space Y] {f : X -> Y} (h : Continuous f) (hf : Function.Injective f) : Is
ClosedEmbedding f
· 使用定理 `compactSpace_of_completeLinearOrder`：∀ {α : Type u_2} [inst : CompleteLi
nearOrder α] [inst_1 : TopologicalSpace α] [OrderTopology α], CompactSpace α
· 使用定理 `ENat.instOrderTopology`：OrderTopology ℕ∞
· 使用定理 `ENNReal.instT2Space`：T2Space ENNReal
· 使用定理 `ENat.continuous_toENNReal`：continuous_toENNReal : Continuous toENNReal
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用定理 `ENat.toENNReal_strictMono`：toENNReal_strictMono : StrictMono ((↑) : Nat∞
 -> Real>=0∞)
-/
theorem isClosedEmbedding_toENNReal : Topology.IsClosedEmbedding toENNReal :=
  continuous_toENNReal.isClosedEmbedding toENNReal_strictMono.injective

end ENat

