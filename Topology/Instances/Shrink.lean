/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Logic.Small.Defs
public import Mathlib.Topology.Homeomorph.TransferInstance

/-!
# Topological space structure on `Shrink X`
-/

@[expose] public section

universe v u

namespace Shrink

/-
**Shrink.** 是 Mathlib 中的一个实例，位于命名空间 `Shrink`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance (X : Type u) [TopologicalSpace X] [Small.{v} X] :
    TopologicalSpace (Shrink.{v} X) :=
  (equivShrink X).symm.topologicalSpace

/-- `equivShrink` as a homeomorphism. -/
@[simps! toEquiv]
/-
**Shrink.homeomorph** 是 Mathlib 中的一个定义，位于命名空间 `Shrink`。
形式化陈述：homeomorph (X : Type u) [TopologicalSpace X] [Small.{v} X] : X ≃ₜ Shrink.{
v} X
参数：X : Type u。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
`equivShrink` as a homeomorphism.
-/
noncomputable def homeomorph (X : Type u) [TopologicalSpace X] [Small.{v} X] :
    X ≃ₜ Shrink.{v} X :=
  (equivShrink X).symm.homeomorph.symm

end Shrink

