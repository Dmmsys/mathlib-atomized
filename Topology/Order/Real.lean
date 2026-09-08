/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Data.EReal.Basic
public import Mathlib.Topology.Order.T5

/-!
# The reals are equipped with their order topology

This file contains results related to the order topology on (extended) (non-negative) real numbers.
We
- prove that `ℝ` and `ℝ≥0` are equipped with the order topology and bornology,
- endow `EReal` with the order topology (and prove some very basic lemmas),
- define the topology `ℝ≥0∞` (which is the order topology, *not* the `EMetricSpace` topology)
-/

public section

assert_not_exists IsTopologicalRing UniformSpace

open Set

namespace EReal

/-!
### Topological structure on `EReal`

We endow `EReal` with the order topology.
Most proofs are adapted from the corresponding proofs on `ℝ≥0∞`.
-/

/-
**EReal.** 是 Mathlib 中的一个实例，位于命名空间 `EReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Topological structure on `EReal`

We endow `EReal` with the order topology.
Most proofs are adapted from the corresponding proofs on `ℝ≥0∞`.
-/
noncomputable instance : TopologicalSpace EReal := Preorder.topology EReal
/-
**EReal.** 是 Mathlib 中的一个实例，位于命名空间 `EReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrderTopology EReal := ⟨rfl⟩
/-
**EReal.** 是 Mathlib 中的一个实例，位于命名空间 `EReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : T5Space EReal := inferInstance
/-
**EReal.** 是 Mathlib 中的一个实例，位于命名空间 `EReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : T2Space EReal := inferInstance
/-
**EReal.denseRange_ratCast** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：denseRange_ratCast : DenseRange (fun r : Rat => ((r : Real) : EReal))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dense_of_exists_between`：dense_of_exists_between [Nontrivial α] {s : Set
 α} (h : forall ⦃a b⦄, a < b -> exists c in s, c in Ioo a b) : Dense s
· 使用定理 `EReal.instOrderTopology`：OrderTopology EReal
· 使用定理 `instNontrivialEReal`：Nontrivial EReal
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.exists_range_iff`：exists_range_iff {p : α -> Prop} : (exists a in ra
nge f, p a) ↔ exists i, p (f i)
· 使用定理 `EReal.exists_rat_btwn_of_lt`：exists_rat_btwn_of_lt : forall {a b : EReal
}, a < b -> exists x : Rat, a < (x : Real) ∧ ((x : Real) : EReal) < b | ⊤, _, h 
=> (not_top_lt h)…
-/
lemma denseRange_ratCast : DenseRange (fun r : ℚ ↦ ((r : ℝ) : EReal)) :=
  dense_of_exists_between fun _ _ h => exists_range_iff.2 <| exists_rat_btwn_of_lt h

end EReal

namespace ENNReal

/-- Topology on `ℝ≥0∞`.

Note: this is different from the `EMetricSpace` topology. The `EMetricSpace` topology has
`IsOpen {∞}`, while this topology doesn't have singleton elements. -/
/-
**ENNReal.** 是 Mathlib 中的一个实例，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Topology on `ℝ≥0∞`.

Note: this is different from the `EMetricSpace` topology. The `EMetricSpace` top
ology has
`IsOpen {∞}`, while this topology doesn't have singleton elements.
-/
instance : TopologicalSpace ℝ≥0∞ := Preorder.topology ℝ≥0∞
/-
**ENNReal.** 是 Mathlib 中的一个实例，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrderTopology ℝ≥0∞ := ⟨rfl⟩

-- short-circuit type class inference
/-
**ENNReal.** 是 Mathlib 中的一个实例，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : T2Space ℝ≥0∞ := inferInstance
/-
**ENNReal.** 是 Mathlib 中的一个实例，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : T5Space ℝ≥0∞ := inferInstance
/-
**ENNReal.** 是 Mathlib 中的一个实例，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : T4Space ℝ≥0∞ := inferInstance

end ENNReal

