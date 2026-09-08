/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.NumberTheory.Padics.Measure.Basic
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Topologies on spaces of measures

We define the weak and strong topologies on `D(X, E)`. These are deliberately not declared as
instances in order to avoid favouring one topology over the other.
-/

@[expose] public section

open ContinuousMap Topology

variable {X R E : Type*} [TopologicalSpace X]

namespace AbstractMeasure

section Topology

section Weak

variable [NormedAddCommGroup E] [CommRing R] [Module R E] [TopologicalSpace R]
  [IsTopologicalRing R] [ContinuousSMul R E]

/--
The weak topology on `AbstractMeasure G R E` (the weakest topology such that `μ ↦ μ f` is
continuous for all `f`).
-/
/-
**AbstractMeasure.WeakTopology** 是 Mathlib 中的一个定义，位于命名空间 `AbstractMeasure`。
形式化陈述：{X : Type u_1} →   {R : Type u_2} →     {E : Type u_3} →       [inst : Top
ologicalSpace X] →         [inst_1 : NormedAddCommGroup E] →           [inst_2 :
 CommRing R] →             [inst_3 : _root_.Module R E] →               [inst_4 
: TopologicalSpace R] → [inst_5 : IsTopologicalRing R] → TopologicalSpace (Abstr
actMeasure X R E)
参数：AbstractMeasure X R E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The weak topology on `AbstractMeasure G R E` (the weakest topology such that `μ 
↦ μ f` is
continuous for all `f`).
-/
@[reducible] def WeakTopology : TopologicalSpace (AbstractMeasure X R E) :=
  .induced (fun μ f ↦ μ f) inferInstance

end Weak

variable [CompactSpace X] [NontriviallyNormedField R] [NormedAddCommGroup E] [NormedSpace R E]

/-- The strong topology on `AbstractMeasure G R E` (the topology induced by the norm). -/
/-
**AbstractMeasure.StrongTopology** 是 Mathlib 中的一个定义，位于命名空间 `AbstractMeasure`。
形式化陈述：{X : Type u_1} →   {R : Type u_2} →     {E : Type u_3} →       [inst : Top
ologicalSpace X] →         [inst_1 : NontriviallyNormedField R] →           [ins
t_2 : NormedAddCommGroup E] → [inst_3 : NormedSpace R E] → TopologicalSpace (Abs
tractMeasure X R E)
参数：AbstractMeasure X R E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The strong topology on `AbstractMeasure G R E` (the topology induced by the norm
).
-/
@[reducible] def StrongTopology : TopologicalSpace (AbstractMeasure X R E) :=
  inferInstanceAs (TopologicalSpace (C(X, R) →L[R] E))

end Topology

end AbstractMeasure

end

